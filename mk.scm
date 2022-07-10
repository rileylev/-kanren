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


(define-immutable-record-type <lvar>
  (lvar% id name) lvar?
  (id   lvar-id)
  (name lvar-name))
(def (lvar id :optional name)
  (lvar% id name))

(define-immutable-record-type <state>
  (state% subs counter diseqs) state?
  (subs    state-subs    with-state-subs)
  (diseqs  state-diseqs  with-state-diseqs)
  (counter state-counter with-state-counter))
(def (state :optional (subs vlist-null) (counter 0) (diseqs vlist-null))
  (state% subs counter diseqs))

(def (walk var subs)
  "Look up the value of var in subs"
  (if-let (pair (and (lvar? var)
                     (vhash-assoc var subs)))
          (walk (cdr pair) subs)
          var))
(def (walk* var subs)
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
   :op2
   (lambda (s0 s1)
     (lazy-stream
      (if (stream-null? s0) s1
          (stream-cons (stream-car s0)
                       (m+ s1 (stream-cdr s0))))))
   :zero m0
   :doc "The addition for the stream monad. Interleaves the incoming streams."))

(def (>>= s g)
  "Bind for the stream monad."
  (lazy-stream
   (if (stream-null? s) m0
       (m+ (g (stream-car s))
           (>>= (stream-cdr s) g)))))

(def (unify u v subs)
  "Attempts to unify u and v wrt subs.
Returns:
  - #f if unification fails
  - the (possibly extended) substitution that results"
  (let ((u (walk u subs))
        (v (walk v subs)))
    (cond
     ((and (lvar? u) (lvar? v) (equal? u v)) subs)
     ((lvar? u) (extend-subs u v subs))
     ((lvar? v) (extend-subs v u subs))
     ((and (pair? u) (pair? v))
      (and=> (unify (car u) (car v) subs)
             (cut unify (cdr u) (cdr v) <>)))
     (else (and (equal? u v) subs)))))

;;; TODO?: mapstack instead of vhash.
;;; look up in the top of the stack first. This gives
;;; some ordering on top of a fully unordered map
;;; obviates the need for prefix
(def (prefix vh suffix)
  "Find the part of vh that precedes suffix"
  (if (equal? vh suffix) vlist-null
      (let ((h (vlist-head vh)))
        (vhash-cons (car h) (cdr h)
                    (prefix (vlist-tail vh) suffix)))))
(mini-test
 "Prefix returns the part of the vhash vh that precedes suffix"
 (test-assert
     (equal?
      (vhash-cons 'a 'b vlist-null)
      (prefix (vhash-cons 'a 'b vlist-null) vlist-null)))
 (test-assert
     (equal?
      (prefix (unify (lvar 0) (lvar 1) vlist-null) vlist-null)
      (vhash-cons (lvar 0) (lvar 1) vlist-null)))
 (test-assert
     (equal?
      (let ((subs (unify (lvar 0) (lvar 1) vlist-null)))
        (prefix (unify (lvar 2) (lvar 3) subs) subs))
      (unify (lvar 2) (lvar 3) vlist-null))))

(def (!=verify new-subs st)
  (cond
   ((not new-subs) (η st))
   ((equal? new-subs (state-subs st)) m0)
   (else (let ((c (prefix new-subs (state-subs st))))
           (η (with-state-diseqs st (vlist-cons c (state-diseqs st))))))))

(def (unify* p* s)
  (cond
   ((vlist-null? p*) s)
   ((unify (car (vlist-head p*)) (cdr (vlist-head p*)) s)
    => (cut unify* (vlist-tail p*) <>))
   (else #f)))

(def (verify-diseqs constraints subs)
  (let loop ((pending constraints)
             (simplified vlist-null))
    (cond
     ((vlist-null? pending) simplified)
     ((unify* (vlist-head pending) subs)
      => (lambda (new-subs)
           (cond
            ((equal? subs new-subs) #f)
            (else (let ((c (prefix new-subs subs)))
                    (loop (vlist-tail pending)
                          (vlist-cons c simplified)))))))
     (else (loop (vlist-tail pending) simplified)))))

(def (==verify new-subs st)
  (cond
   ((not new-subs) m0)
   ((equal? (state-subs st) new-subs) (η st))
   ((verify-diseqs (state-diseqs st) new-subs)
    => (lambda (d)
         (η (set-fields st
              ((state-diseqs) d)
              ((state-subs) new-subs)))))
   (else m0)))

(def ((== u v) st)
  (lazy-stream
   (==verify (unify u v (state-subs st)) st)))
(def ((!= u v) st)
  (lazy-stream
   (!=verify (unify u v (state-subs st)) st)))


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

(def ((call/fresh f :optional name) st)
  (let ((ctr (state-counter st)))
    ((f (lvar ctr name))
     (with-state-counter st (1+ ctr)))))

(def (fail st) m0)
(def (succeed st) (η st))

(def disj
  (make-operator
   :op2 (λs ((g1 g2) st)
          (m+ (g1 st) (g2 st)))
   :zero fail))
(def conj
  (make-operator
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

(import (rnrs (6)))                     ; assert
(eval-when (expand load eval)
 (def (map-tree tree
                :key
                (leaf?     (const #f))
                (on-leaf   identity)
                (nil       '())
                (make-node cons))
   (let ((leaf? (lambda (x)
                  (or (not (pair? x))
                      (leaf? x)))))
     (let loop ((tree tree))
       (cond
        ((null? tree) nil)
        ((leaf? tree) (on-leaf tree))
        (else (assert (pair? tree))
         (make-node (loop (car tree))
                    (loop (cdr tree)))))))))
(def (flatten tree :key (leaf? (const #f)))
  (def head (cons #f '()))
  (def tail head)
  (def (push-tail! tail next)
    (set-cdr! tail (cons next '()))
    (cdr tail))
  (map-tree tree
            :leaf?     leaf?
            :on-leaf   (lambda (x)
                         (set! tail (push-tail! tail x)))
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
  (any lvar? (flatten (walk* var subs))))



(define-syntax-rule (zzz g)
  (lambda (st)
    (g st)))

(define-syntax-rule (conde (g ...) ...)
  (disj (zzz (conj (zzz g) ...)) ...))

(define-syntax fresh
  (syntax-rules ()
    ((fresh () body ...) (conj (zzz body) ...))
    ((fresh (v vs ...) body ...)
     (call/fresh (lambda (v)
                   (fresh (vs ...)
                     body ...))
                 (symbol->string 'v)))))

(comment
 (vlist-head
  (state-subs
   (stream-ca
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


(eval-when (expand load eval)
  (def (unquote? x)
    (and (pair? x)
         (eq? (car x) 'unquote)))
  (def ununquote cadr)
  (def (gentemp)
    (car (generate-temporaries '(a))))
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
       ((unquote? x) (datum->syntax here (ununquote x)))
       (else
        (let ((stx (datum->syntax here x)))
          (if (symbol? x) (push-fresh! stx))
          stx))))
    (def unify-list (map-tree (syntax->datum pat)
                              :leaf?     unquote?
                              :on-leaf   visitor
                              :nil       #''()
                              :make-node (lambda (x y) #`(cons #,x #,y))))
    (values (reverse! freshes) unify-list)))

(parse-pattern #'here #'(a b))
(parse-pattern #'here #'(a ,b))
(parse-pattern #'here #'())



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
  [(_ () #f)]
  [(x (x . _) #t)]
  [(x (y . ys) flag)]
  (!= x y)
  (member?o x ys flag))
(defne never-membero
  [(_ ())]
  [(x (y . ys))
   (!= x y)
   (never-membero x ys)])
(defne reverse-appendo
  [((x . xs) y zs) (reverse-appendo xs (cons x y) zs)]
  [(()       y y )])
(def (reverso X Y)
  (reverse-appendo X '() Y))
(def (appendo2 X Y Z)
  (fresh (rev-X)
    (reverseo X rev-X)
    (reverse-appendo rev-X Y Z)))


;;; TODO: mukanren with work/time slices in m+ via generators


;; Local Variables:
;; eval: (geiser-syntax--scheme-indent (set-fields 1) (stream-lambda 1) (matche 1)(defne 1) (λs 1) (λe 0)  (def 1) (fresh 1)  )
;; eval: (font-lock-add-keywords 'scheme-mode (geiser-syntax--simple-keywords
;; '("define-stream" "def" "λs" "defn" "if-let" "matche" "defne" "stream-lambda" "λe" "define-syntax-rule" "define-syntax-case")))
;; End:
