(use-modules
 (srfi srfi-1)                          ; list
 (srfi srfi-9 gnu)                      ; records, immutable records
 (srfi srfi-11)                         ; let-values
 (srfi srfi-26)                         ; cut
 (srfi srfi-41)                         ; streams
 (srfi srfi-64)                         ; test
 (ice-9 vlist)
 (ice-9 match)
 (ice-9 curried-definitions))
(import (rnrs (6)))                    ; assert
                                        ;

(read-set! keywords 'prefix)

(define-syntax-rule (def args ...) (define* args ...))
(define-syntax-rule (mini-test name body ...)
  (begin
    (test-begin name)
    body ...
    (test-end name)))
(define-syntax λs
  (syntax-rules ()
    ((_ ((inner ...) outer ...) body ...)
     (λs (inner ...)
       (lambda* (outer ...)
         body ...)))
    ((_ args body ...)
     (lambda* args body ...))))
(mini-test
 "test λs"
 (test-assert
     (= (((λs ((x) y)
            (+ x y))
          3) 5)
        8)))
(define-syntax-rule (defn name bodies ...)
  (def name (case-lambda* bodies ...)))
(define-syntax-rule (comment _ ...) #f)

(define-syntax-rule (if-let (name test) true-case false-case)
  (let ((name test))
    (if name true-case false-case)))

(define-syntax-parameter here
  (lambda (stx)
    (syntax-violation 'here "here undefined outside of define-syntax-case" stx)))
(define-syntax-rule (define-syntax-case (name . pattern) body ...)
  (define-syntax name
    (lambda (stx)
      (syntax-case stx ()
        ((k . pattern)
         (let ((here% #'k))
           (syntax-parameterize ((here (identifier-syntax here%)))
             (let () body ...))))))))



(define-syntax-rule (lazy-stream args ...)
  ((stream-lambda () args ...)))

(def (make-operator :key op2 zero (doc #f))
  (defn op
    (() zero)
    ((x) x)
    ((x y) (op2 x y))
    ((x . ys) (fold op2 x ys)))
  (if doc (set-procedure-property! op 'documentation doc))
  op)

(def subs-null  vlist-null)
(def subs-null? vlist-null?)
(def subs-assoc vhash-assoc)
(def subs-cons  vhash-cons)
(def subs-merge
  (make-operator
   :doc "Merge substitutions"
   :zero vlist-null
   :op2 (lambda (x y)
          (if (vlist-null? x)
              y
              (let ((h (vlist-head x))
                    (t (vlist-tail x)))
                (subs-cons (car h) (cdr h)
                           (subs-merge t y)))))))
(mini-test
 "merging vhashes results in a vhash containing keys from the inputs"
 (equal?
  (vlist->list
   (subs-merge (subs-cons 'c 3
                          (subs-cons 'a 1 subs-null))
               (subs-cons 'b 2 subs-null)))
  '((c . 3) (a . 1) (b . 2))))

(def name-cons cons)
(def name-null '())

(def root-cons cons)
(def root-null '())

(define-immutable-record-type <lvar>
  (lvar% id name) lvar?
  (id lvar-id)
  (name lvar-name))
(def (lvar id :optional (name #f))
  (lvar% id name))

(define-immutable-record-type <state>
  (state% subs counter diseqs names roots) state?
  (subs    state-subs    with-state-subs)
  (diseqs  state-diseqs  with-state-diseqs)
  (counter state-counter with-state-counter)
  (names   state-names   with-state-names)
  (roots   state-roots   with-state-roots))
(def (state :key (subs subs-null) (counter 0)
            (diseqs vlist-null) (names name-null) (roots root-null))
  (state% subs counter diseqs names roots))

(def (walk var subs)
  "Look up the value of var in subs"
  (if-let (pair (and (lvar? var)
                     (subs-assoc var subs)))
          (walk (cdr pair) subs)
          var))
(def (walk2 var old-subs new-subs)
  (walk (walk var old-subs) new-subs))
(def (walk* var subs)
  "Walk everything inside a list too"
  (let ((var (walk var subs)))
    (if (pair? var)
        (cons (walk (car var) subs)
              (walk (cdr var) subs))
        var)))

(def (occurs✓ x v s)
  "Does x occur in its definition, v?"
  (let ((v (walk v s)))
    (if (lvar? v) (equal? v x)
        (and (pair? v)
             (or (occurs✓ x (car v) s)
                 (occurs✓ x (cdr v) s))))))

(def extend-subs-no✓ vhash-cons)
(def (extend-subs x v s)
  (if (occurs✓ x v s) #f
      (extend-subs-no✓ x v s)))

;;; streams as an additive monad
(def (η x)
  "The unit for the stream monad. Takes x to the singleton stream of x."
  (stream x))
(def m0 stream-null)
(def m0? stream-null?)
(def m+
  (make-operator
   :doc  "The addition for the stream monad. Interleaves the incoming streams."
   :zero m0
   :op2  (lambda (s0 s1)
           (lazy-stream
            (if (stream-null? s0) s1
                (stream-cons (stream-car s0)
                             (m+ s1 (stream-cdr s0))))))))

(def (>>= s g)
  "Bind for the stream monad."
  (lazy-stream
   (if (stream-null? s) m0
       (m+ (g (stream-car s))
           (>>= (stream-cdr s) g)))))

(def (pre-unify u v old-subs :optional (new-subs subs-null))
  (let ((u (walk2 u old-subs new-subs))
        (v (walk2 v old-subs new-subs)))
    (cond
     ((and (lvar? u) (lvar? v) (equal? u v)) new-subs)
     ((lvar? u) (extend-subs u v new-subs))
     ((lvar? v) (extend-subs v u new-subs))
     ((and (pair? u) (pair? v))
      (and=> (pre-unify (car u) (car v) old-subs new-subs)
             (cut pre-unify (cdr u) (cdr v) old-subs <>)))
     (else (and (equal? u v) new-subs)))))
(def (unify u v subs)
  "Attempts to unify u and v wrt subs.
Returns:
  - #f if unification fails
  - the (possibly extended) substitution that results"
  (and=> (pre-unify u v subs)
         (cut subs-merge <> subs)))

(def (prefix vh suffix)
  "Find the part of vh that precedes suffix"
  (if (equal? vh suffix) vlist-null
      (let ((h (vlist-head vh)))
        (subs-cons (car h) (cdr h)
                   (prefix (vlist-tail vh) suffix)))))
(mini-test
 "Prefix returns the part of the vhash vh that precedes suffix"
 (test-assert
     (equal?
      (subs-cons 'a 'b subs-null)
      (prefix (subs-cons 'a 'b vlist-null) subs-null)))
 (test-assert
     (equal?
      (pre-unify (lvar 0) (lvar 1) vlist-null)
      (subs-cons (lvar 0) (lvar 1) vlist-null)))
 (test-assert
     (equal?
      (let ((subs (unify (lvar 0) (lvar 1) vlist-null)))
        (pre-unify (lvar 2) (lvar 3) subs))
      (unify (lvar 2) (lvar 3) vlist-null))))

(def (!=verify new-subs st)
  (cond
   ((not new-subs) (η st))
   ((subs-null? new-subs) m0)
   (else
    (η (with-state-diseqs st
                          (vlist-cons new-subs (state-diseqs st)))))))

(def (pre-unify* p* old-subs :optional (new-subs subs-null))
  (if (vlist-null? p*)
      old-subs
      (and=> (pre-unify (car (vlist-head p*)) (cdr (vlist-head p*)) old-subs)
             (cut pre-unify* (vlist-tail p*) old-subs <>))))
(def (unify* p* s)
  (and=> (pre-unify* p* s)
         (cut subs-merge <> s)))

(def (verify-diseqs constraints subs)
  (let loop ((pending constraints)
             (simplified vlist-null))
    (cond
     ((vlist-null? pending) simplified)
     ((pre-unify* (vlist-head pending) subs)
      => (lambda (new-subs)
           (if (subs-null? new-subs) #f
               (loop (vlist-tail pending)
                     (vlist-cons new-subs simplified)))))
     (else (loop (vlist-tail pending) simplified)))))

(def (==verify new-subs st)
  (cond
   ((not new-subs) m0)
   ((subs-null? new-subs) (η st))
   ((verify-diseqs (state-diseqs st)
                   (subs-merge new-subs (state-subs st)))
    => (lambda (d)
         (η (set-fields st
              ((state-diseqs) d)
              ((state-subs) (subs-merge new-subs
                                        (state-subs st)))))))
   (else m0)))

(def ((== u v) st)
  (lazy-stream
   (==verify (pre-unify u v (state-subs st)) st)))
(def ((!= u v) st)
  (lazy-stream
   (!=verify (pre-unify u v (state-subs st)) st)))


(mini-test
 "=="
 (test-assert "== is reflexive"
   (equal? (list (state))
           (stream->list ((== 1 1) (state)))))
 (test-assert "== failure gives empty stream"
   (stream-null? ((== 1 2) (state))))
 (test-assert "== two unbound lvars adds an entry equating them in the substitution"
   (equal? (vlist-head (state-subs (stream-car
                                    ((== (lvar 0) (lvar 1)) (state)))))
           (cons (lvar 0) (lvar 1)))))

(def (pop-root st)
  (with-state-roots st (cdr (state-roots st))))
(def ((call/fresh f :optional (name #f)) st)
  (stream-map
   pop-root
   (let ((ctr   (state-counter st))
         (names (state-names st))
         (roots (state-roots st)))
     ((f (lvar ctr name))
      (set-fields st
        ((state-roots)   (root-cons ctr roots))
        ((state-counter) (1+ ctr))
        ((state-names)   (name-cons name names)))))))

(def (fail st) m0)
(def (succeed st) (η st))

(def disj
  (make-operator
   :doc "Disjunctive goal (logical or)"
   :op2 (λs ((g1 g2) st)
          (m+ (g1 st) (g2 st)))
   :zero fail))
(def conj
  (make-operator
   :doc "Conjunctive goal (logical and)"
   :op2 (λs ((g1 g2) st)
          (>>= (g1 st) g2))
   :zero succeed))

(mini-test
 "contradiction yields no states"
 (test-assert "ditto"
   (stream-null?
    ((call/fresh
      (lambda (x)
        (conj (== x 0) (== x 1))))
     (state)))))



;; non relational μ style?
(def ((lif testg theng :optional (elseg fail)) st)
  (cond
   ((testg st) (negate m0?) => (cut >>= <> theng))
   (else (elseg st))))

(def ((only-one goal) st)
  (stream-take 1 (goal st)))
(def (lif1 testg theng :optional (elseg fail))
  (lif testg (only-one theng) elseg))
(def ((call/project var f) st)
  (f (walk var (state-subs st))))

(eval-when (expand load eval)
  (def (map-tree tree
                 :key
                 (leaf?     (const #f))
                 (kids      identity)
                 (on-leaf   identity)
                 (nil       '())
                 (make-node cons))
    (let ((leaf? (lambda (x)
                   (or (not (pair? x))
                       (leaf? x)))))
      (let loop ((tree tree))
        (let ((tree (kids tree)))
          (cond
           ((null? tree) nil)
           ((leaf? tree) (on-leaf tree))
           (else ;; (assert (pair? tree))
            (make-node (loop (car tree))
                       (loop (cdr tree))))))))))
(def (flatten tree :key (leaf? (const #f)))
  (def head (cons #f '()))
  (def tail head)
  (def (push-tail! tail next)
    (set-cdr! tail (cons next '()))
    (cdr tail))
  (map-tree tree
            :leaf?     leaf?
            :on-leaf   (lambda (x) (set! tail (push-tail! tail x)))
            :make-node (const #f))
  (cdr head))
(mini-test
 "flatten gives the list resulting from in-order traversal"
 (test-assert
     (equal? (flatten '(a (b (c)) (d e) f (g (h i) j k ())))
             '(a b c d e f g h i j k))))
(mini-test
 "flatten treats a leaf? as a leaf even if it is a list"
 (test-assert
     (equal? (flatten '((:guard a) (b (:guard c)))
                      :leaf? (lambda (x)
                               (eq? (car x) :guard)))
             '((:guard a) b (:guard c)))))
(def (ground? var subs)
  (not (any lvar? (flatten (walk* var subs)))))



(define-syntax-rule (zzz g) (lambda (st) (g st)))

(define-syntax-rule (conde (g ...) ...)
  (disj (zzz (conj (zzz g) ...)) ...))

(define-syntax fresh
  (syntax-rules ()
    ((fresh () body ...) (conj (zzz body) ...))
    ((fresh (v vs ...) body ...)
     (call/fresh (lambda (v)
                   (fresh (vs ...)
                     body ...))
                 'v))))



(eval-when (expand load eval)
  (def (peel-stx stx)
    (syntax-case stx ()
      ((x . y) (cons #'x (peel-stx #'y)))
      (()      '())
      (_       stx)))
  (def (unquote? x)
    (let ((x (syntax->datum x)))
      (and (pair? x)
           (eq? (car x) 'unquote))))
  (def ununquote cadr)
  (def (gentemp)
    (datum->syntax #f (gensym "_")))
  (def (wildcard-pat? stx)
    (eq? (syntax->datum stx) '_))
  (def (parse-pattern here pat)
    (def freshes '())
    (def (push-fresh! x)
      (set! freshes (lset-adjoin equal? freshes x)))
    (def (visitor x)
      (cond
       ((wildcard-pat? x)
        (let ((wild (gentemp)))
          (push-fresh! wild)
          wild))
       ((unquote? x) (ununquote x))
       (else
        (if (symbol? (syntax->datum x))
            (push-fresh! x))
        x)))
    (def unify-list (map-tree pat
                              :kids      peel-stx
                              :leaf?     unquote?
                              :on-leaf   visitor
                              :nil       #''()
                              :make-node (lambda (x y) #`(cons #,x #,y))))
    (values (reverse! freshes) unify-list)))

(parse-pattern #'here #'(a b))
(parse-pattern #'here #'(_ _))
(parse-pattern #'here #'(a ,b))
(parse-pattern #'here #'())

(parse-pattern #'here #'[(a d (a . d))])


(define-syntax-case (matche-case against (pat body ...))
  (let-values (((freshes unify-list) (parse-pattern here #'pat)))
    #`(fresh #,freshes
        (== against #,unify-list)
        body ...)))
(define-syntax-rule (matche against case ...)
  (let ((against% against))
    (conde ((matche-case against% case)) ...)))

(define-syntax-rule (λe cases ...)
  (lambda all-args
    (matche all-args
      cases ...)))

(define-syntax-rule (defne name cases ...)
  (def name (λe cases ...)))

(defne conso [(a d (a . d))])
(defne caro [(a . _) a])
(defne cdro [(_ . d) d])
(defne nullo [()])
(defne appendo
  [(()       y y       )]
  [((x . xs) y (x . zs))
   (appendo xs y zs)])
(defne rembero
  [(_ ()       ())]
  [(x (x . ys) ys)]
  [(x (y . ys) z)
   (!= x y)
   (rembero x ys z)])
(defne membero
  [(y (y . ys) (y . ys))]
  [(x (_ . ys) z       ) (membero x ys z)])
(defne first-membero
  [(y (y . ys) (y . ys))]
  [(x (y . ys) z       )
   (!= x y)
   (membero x ys z)])
(defne member?o
  [(_ ()      #f)]
  [(x (x . _) #t)]
  [(x (y . ys) flag)
   (!= x y)
   (member?o x ys flag)])
(defne never-membero
  [(_ ())]
  [(x (y . ys))
   (!= x y)
   (never-membero x ys)])
(defne reverse-appendo
  [((x . xs) y zs) (reverse-appendo xs (cons x y) zs)]
  [(()       y y )])
(def (reverseo X Y)
  (reverse-appendo X '() Y))
(def (appendo2 X Y Z)
  (fresh (rev-X)
    (reverseo X rev-X)
    (reverse-appendo rev-X Y Z)))

(comment
 (vlist->list
  (state-subs
   (stream-car
    ((fresh (q)
       (appendo '(1) '(2 3) q))
     (state))))))

(comment
 (vlist->list
  (state-subs
   (stream-car
    ((fresh (out)
       (appendo '(a) out '(a b c)))
     (state)))))

 (stream-car
  ((fresh (out)
     (appendo '(a) '(b) out))
   (state)))

 (walk (lvar 0 'out)
       (state-subs
        (stream-car
         ((fresh (out)
            (appendo '(a) out '(a b c)))
          (state))))))



;;; TODO: mukanren with work/time slices in m+ via generators


;; Local Variables:
;; eval: (geiser-syntax--scheme-indent (set-fields 1) (stream-lambda 1) (matche 1)(defne 1) (λs 1) (λe 0)  (def 1) (fresh 1)  )
;; eval: (font-lock-add-keywords 'scheme-mode (geiser-syntax--simple-keywords
;; '("define-stream" "def" "λs" "defn" "if-let" "matche" "defne" "stream-lambda" "λe" "define-syntax-rule" "define-syntax-case")))
;; End:
