(use-modules (srfi srfi-9 gnu)
             (ice-9 vlist)
             (ice-9 match)
             (srfi srfi-26)             ; cut
             (srfi srfi-41)             ; streams
             (srfi srfi-64)             ; test
             (ice-9 curried-definitions))

(read-set! keywords 'prefix)

(define-syntax-rule (def args ...) (define* args ...))
(define-syntax-rule (comment _ ...) (begin))

(define-syntax-rule (if-let (name test) true-case false-case)
  (let ((name test))
    (if name true-case false-case)))

(define-syntax-rule (mini-test name body ...)
  (begin
    (test-begin name)
    body ...
    (test-end name)))

(define-syntax-rule (lazy-stream args ...)
  ((stream-lambda ()
     args ...)))


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

(def (copy-struct s)
  (let ((vt (struct-vtable s))
        (nfield (/ (string-length (symbol->string (struct-layout s)))
                   2)))
    (apply make-struct/no-tail vt
           (map (cut struct-ref s <>) (iota nfield)))))

(def (walk var subs)
  "Look up the value of var in subs"
  (if-let (pair (and (lvar? var)
                     (vhash-assoc var subs)))
          (walk (cdr pair) subs)
          var))

(def extend-subs vhash-cons)

;;; streams as an additive monad
(def (η x)
  "The unit for the stream monad. Takes x to the singleton stream of x."
  (stream x))
(def m0 stream-null)
(def m+
  (case-lambda
    "Stream interleaving, the monad's addition."
    (() m0)
    ((s) s)
    ((s0 s1)
     (lazy-stream
      (if (stream-null? s0) s1
          (stream-cons (stream-car s0)
                       (m+ s1 (stream-cdr s0))))))
    ((s0 s1 . s) (apply m+ (m+ s0 s1) s))))
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
 "bloop"
 (test-assert (equal?
               (vhash-cons 'a 'b vlist-null)
               (prefix (vhash-cons 'a 'b vlist-null) vlist-null)))
 (test-assert
     (equal?
      (prefix (unify (lvar 0) (lvar 1) vlist-null) vlist-null)
      (vhash-cons (lvar 0) (lvar 1) vlist-null))))

(def (!=verify new-subs st)
  (cond
   ((not new-subs) (η st))
   ((equal? new-subs (state-subs st)) m0)
   (else (let ((c (prefix new-subs (state-subs st))))
           (η (with-state-diseqs st (vlist-cons c (state-diseqs st))))))))

(!=verify vlist-null (state))
(equal? vlist-null (state-subs (state)))

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
    => (lambda (d) (η (set-fields st
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
     (with-state-counter st
                         (1+ ctr)))))

(def ((disj g1 g2) st)
  (m+ (g1 st) (g2 st)))
(def ((conj g1 g2) st)
  (>>= (g1 st) g2))



(mini-test "contradiction yields no states"
           (test-assert "ditto"
             (stream-null?
              ((call/fresh
                (lambda (x)
                  (conj (== x 0) (== x 1))))
               (state)))))

(vlist->list
 (state-subs
  (stream-car ((call/fresh
                (lambda (x) (== x 0))
                'x)
               (state)))))

(define-syntax-rule (zzz g)
  (lambda (st) (lazy-stream (g st))))

(def (fail st) m0)
(def (succeed st) (η st))

(define-syntax conj*
  (syntax-rules ()
    ((_) succeed)
    ((_ g) (zzz g))
    ((_ g gs ...) (conj (zzz g) (conj* gs ...)))))
(define-syntax disj*
  (syntax-rules ()
    ((_) fail)
    ((_ g) (zzz g))
    ((_ g gs ...) (disj (zzz g) (disj* gs ...)))))

(def (fives x)
  (disj* (== x 5) (fives x)))
(map vlist->list (map state-subs (stream->list 3 ((call/fresh fives) (state)))))

(define-syntax-rule (conde (g ...) ...)
  (disj* (conj* g ...) ...))

(define-syntax fresh
  (syntax-rules ()
    ((fresh () body ...) (conj* body ...))
    ((fresh (v vs ...) body ...)
     (call/fresh (lambda (v)
                   (fresh (vs ...)
                     body ...))
                 (symbol->string 'v)))))

(def (appendo l s out)
  (conde
   ((== l '()) (== out s))
   ((fresh (a d out%)
      (== l (cons a d))
      (== out (cons a out%))
      (appendo d s out%)))))

(comment
 (def (member x l)
   (match l
     ('() #f)
     ((a . d)
      (if (equal? x a) l
          (member x d))))))
(def (first-membero x l out)
  (fresh (a d)
    (== l (cons a d))
    (conde
     ((== x a) (== d out))
     ((!= x a)
      (first-membero x d out)))))
(def (membero x l out)
  (fresh (a d)
    (== l (cons a d))
    (conde
     ((== x a) (== d out))
     ((membero x d out)))))

(def (rembero x ls out)
  (conde
   ((== '() ls) (== '() out))
   ((fresh (a d)
      (== (cons a d) ls)
      (conde
       ((== a x) (== d out))
       ((!= a x)
        (fresh (res)
          (== (cons a res) out)
          (rembero x d res))))))))

(vlist-head
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
         (state)))))


;;; TODO: mukanren with work/time slices in m+ via generators


;; Local Variables:
;; eval: (geiser-syntax--scheme-indent (stream-lambda 1)  (def 1) (fresh 1)  )
;; eval: (font-lock-add-keywords 'scheme-mode (geiser-syntax--simple-keywords
;; '("define-stream" "def" "if-let" "stream-lambda" "define-syntax-rule" "define-syntax-case")))
;; End:
