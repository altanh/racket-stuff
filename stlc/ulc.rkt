; The untyped lambda calculus, with a little Lisp-y compiler
;
; References used:
; https://en.wikipedia.org/wiki/Lambda_calculus
; https://en.wikipedia.org/wiki/De_Bruijn_index
; https://www.cs.cornell.edu/courses/cs4110/2018fa/lectures/lecture15.pdf
; https://www.cs.tufts.edu/comp/105-2019f/reduction.pdf
;
; Definitely an exercise in irony since I'm doing this in Racket

#lang racket

(require racket/set)

; the standard lambda calculus
(struct var (sym) #:transparent)
(struct abs (var body) #:transparent)
(struct app (func arg) #:transparent)

; term[fv := target]
(define (substitute term fv target)
  (match term
    [(struct var (sym))
     (if (equal? sym (var-sym fv))
         target
         (var sym))]
    [(struct abs (v body))
     (if (equal? (var-sym v) (var-sym fv))
         (abs v body)
         (abs v (substitute body fv target)))]
    [(struct app (func arg))
     (app (substitute func fv target) (substitute arg fv target))]
    [t t]))

; (app (abs (var sym) body) term) -> body[sym := term]
(define (β-reduce term)
  (match term
    [(struct app (func arg))
     (if (abs? func)
         (substitute (abs-body func) (abs-var func) arg)
         (app (β-reduce func) (β-reduce arg)))]
    [(struct abs (v body))
     (abs v (β-reduce body))]
    [t t]))

(define (free-vars term)
  (match term
    [(struct var (sym))
     (set (var sym))]
    [(struct abs (v body))
     (set-remove (free-vars body) v)]
    [(struct app (func arg))
     (set-union (free-vars func) (free-vars arg))]))

;; the lambda calculus with de Bruijn indices (starting at 1)
(struct db-abs (body) #:transparent)

; shift operator
(define (↑ term i c)
  (match term
    [(? integer? n)
     (if (< n c)
         n
         (+ n i))]
    [(struct db-abs (body))
     (db-abs (↑ body i (+ c 1)))]
    [(struct app (func arg))
     (app (↑ func i c) (↑ arg i c))]
    [t t]))

; convert standard LC term to use de Bruijn indices
;   - context maps free variables in term to indices
(define (to-db term context)
  (define (to-db-rec term bindings)
    (match term
      [(struct var (sym))
       (define sym-idx (index-of bindings sym))
       (cond
         [sym-idx (+ sym-idx 1)]
         [else (+ (hash-ref context sym) (length bindings))])]
      [(struct abs (v body))
       (define sym (var-sym v))
       (db-abs (to-db-rec body (cons sym bindings)))]
      [(struct app (func arg))
       (app (to-db-rec func bindings)
            (to-db-rec arg bindings))]
      [t (raise t)]))
  (to-db-rec term empty))

(define (substitute-db term fvn target)
  (match term
    [(? integer? n)
     (if (= n fvn)
         target
         n)]
    [(struct db-abs (body))
     (db-abs (substitute-db body (+ fvn 1) (↑ target 1 1)))]
    [(struct app (func arg))
     (app (substitute-db func fvn target)
          (substitute-db arg fvn target))]
    [t (raise t)]))

(define (free-vars-db term)
  (match term
    [(? integer? n)
     (set n)]
    [(struct db-abs (body))
     (define unshifted (set-remove (free-vars-db body) 1))
     (apply set (set-map unshifted (λ (n) (- n 1))))]
    [(struct app (func arg))
     (set-union (free-vars-db func) (free-vars-db arg))]))

; -------------------- (β)
; (λx.M)N -> M[x := N]
(define (rule-β-db term reducer)
  (match term
    [(struct app ((struct db-abs (body)) arg))
     (↑ (substitute-db body 1 (↑ arg 1 1)) -1 1)]
    [_ #f]))

;   a -> a'
; ---------- (μ)
; f a -> f a'
(define (rule-μ-db term reducer)
  (match term
    [(struct app (func arg))
     (define try-reduce-arg (reducer arg))
     (and try-reduce-arg (app func try-reduce-arg))]
    [_ #f]))

;   f -> f'
; ----------- (ν, nu)
; f a -> f' a
(define (rule-nu-db term reducer)
  (match term
    [(struct app (func arg))
     (define try-reduce-func (reducer func))
     (and try-reduce-func (app try-reduce-func arg))]
    [_ #f]))

;    M -> M'
; ------------- (ξ)
; λx.M -> λx.M'
(define (rule-ξ-db term reducer)
  (match term
    [(struct db-abs (body))
     (define try-reduce-body (reducer body))
     (and try-reduce-body (db-abs try-reduce-body))]
    [_ #f]))

;   x ∉ FV(f)
; ------------- (η)
; λx.(f x) -> f
(define (rule-η-db term reducer)
  (match term
    [(struct db-abs ((struct app (f 1))))
     (if (set-member? (free-vars-db f) 1)
         #f
         f)]
    [_ #f]))

; normal-order reduction strategy
(define (normal-reducer-db term)
  (match term
    [(? db-abs? t)
     (or (rule-η-db t normal-reducer-db)
         (rule-ξ-db t normal-reducer-db))]
    [(? integer? n) #f]
    [(? app? t)
     (or (rule-β-db t normal-reducer-db)
         (rule-nu-db t normal-reducer-db)
         (rule-μ-db t normal-reducer-db))]
    [_ #f]))

(define (reduce*-db term reducer)
  (define try-reduce (reducer term))
  (if try-reduce
      (reduce*-db try-reduce reducer)
      term))

; helper to make a mapping of free vars to indices, needed for de Bruijn conversion
(define (make-db-context term)
  (define fvs (free-vars term))
  (for/hash ([fv fvs]
             [n (in-naturals)])
    (values (var-sym fv) (+ n 1))))

; (curry-app f x y z) -> (app (app (app f x) y) z)
(define (curry-app f . args)
  (for/fold ([result (app f (car args))])
            ([arg (rest args)])
    (app result arg)))

; combinators
(define KC
  (db-abs (db-abs 2)))
(define SC
  (db-abs (db-abs (db-abs (curry-app 3 1 (app 2 1))))))
(define IC
  (db-abs 1))
(define YC
  (db-abs
   (app (db-abs (app 2 (app 1 1)))
        (db-abs (app 2 (app 1 1))))))

; boolean logic and branching
(define TRUE (db-abs (db-abs 2)))
(define FALSE (db-abs (db-abs 1)))
(define ITE (db-abs (db-abs (db-abs (curry-app 3 2 1)))))
(define NOT (db-abs (curry-app 1 FALSE TRUE)))
(define AND (db-abs (db-abs (curry-app 2 1 FALSE))))
(define OR (db-abs (db-abs (curry-app 2 TRUE 1))))

; natural numbers (Church numerals) and ordering
(define ZERO (db-abs (db-abs 1)))
(define SUCC (db-abs (db-abs (db-abs (app 2 (curry-app 3 2 1))))))
(define PLUS (db-abs (db-abs (curry-app 2 SUCC 1))))
(define MUL (db-abs (db-abs (curry-app 2 (app PLUS 1) ZERO))))
(define ISZERO (db-abs (curry-app 1 (db-abs FALSE) TRUE)))
(define ONE (app SUCC ZERO))
(define PRED
  (db-abs
   (curry-app 1
              (db-abs (db-abs (curry-app ISZERO (app 2 ONE) 1 (curry-app PLUS (app 2 1) ONE))))
              (db-abs ZERO)
              ZERO)))
(define SUB (db-abs (db-abs (curry-app 1 PRED 2))))
(define LEQ (db-abs (db-abs (app ISZERO (curry-app SUB 2 1)))))

; pairs
(define CONS (db-abs (db-abs (db-abs (curry-app 1 3 2)))))
(define CAR (db-abs (curry-app 1 TRUE)))
(define CDR (db-abs (curry-app 1 FALSE)))
(define EMPTY (db-abs TRUE))
(define ISEMPTY (db-abs (app 1 (db-abs (db-abs FALSE)))))

; simple lispy thing compiler to lambda calculus
(define intrinsic-map
  (make-immutable-hash
   (list
    (cons `true TRUE)
    (cons `false FALSE)
    (cons `ite ITE)
    (cons `not NOT)
    (cons `and AND)
    (cons `or OR)
    (cons `+ PLUS)
    (cons `* MUL)
    (cons `zero? ISZERO)
    (cons `- SUB)
    (cons `<= LEQ)
    (cons `cons CONS)
    (cons `car CAR)
    (cons `cdr CDR)
    (cons `empty EMPTY)
    (cons `empty? ISEMPTY))))

(define (intrinsic? sym)
  (hash-has-key? intrinsic-map sym))

(define (compile-nat n)
  (if (<= n 0)
      ZERO
      (app SUCC (compile-nat (- n 1)))))

; the compiler. context refers to symbols bound by λ, bindings refers to symbols bound by let/letrec
(define (compile-rec program #:context context #:bindings bindings)
  (match program
    [`(let ,sym = ,val in ,body)
     (define compiled-val (compile-rec val #:context context #:bindings bindings))
     (compile-rec body #:context context #:bindings (hash-set bindings sym compiled-val))]
    [`(letrec ,sym = (λ (,args ...) ,defn) in ,body)
     (define self-fun `(λ (,sym ,@args) ,defn))
     (define compiled-self-fun (compile-rec self-fun #:context context #:bindings bindings))
     (define compiled-rec-fun (app YC compiled-self-fun))
     (compile-rec body #:context context #:bindings (hash-set bindings sym compiled-rec-fun))]
    [`(λ (,args ...) ,body)
     ; shift existing context. I think everything works out with the compiled indices,
     ; since all my "intrinsics" have no free variables.
     (define shift-amt (length args))
     (define shift-ctx
       (make-immutable-hash
        (for/fold ([ctx-list (hash-map context (λ (k v) (cons k (+ v shift-amt))))])
                  ([arg args]
                   [n (in-naturals)])
          (cons (cons arg (- shift-amt n)) ctx-list))))
     (define compiled-body (compile-rec body #:context shift-ctx #:bindings bindings))
     (for/fold ([acc compiled-body])
               ([_ args])
       (db-abs acc))]
    [`(,f ,args ...)
     (apply curry-app
            (cons
             (compile-rec f #:context context #:bindings bindings)
             (map (λ (arg) (compile-rec arg #:context context #:bindings bindings)) args)))]
    [(? integer? n)
     (compile-nat n)]
    [(? intrinsic? f)
     (hash-ref intrinsic-map f)]
    [(? (λ (s) (hash-has-key? context s)) lambda-bound)
     ; simply return the de Bruijn index
     (hash-ref context lambda-bound)]
    [(? (λ (s) (hash-has-key? bindings s)) let-bound)
     (hash-ref bindings let-bound)]
    [id (raise id)]))

(define (compile program)
  (compile-rec program #:context (make-immutable-hash) #:bindings (make-immutable-hash)))

;; tests

(define (normal-reduce* term)
  (reduce*-db term normal-reducer-db))

(define def-add-2
  `(let add-2 = (λ (n) (+ n 2)) in
     (add-2 3)))

(define letrec-fact
  `(letrec fact =
     (λ (n) (ite (zero? n)
                 1
                 (* n (fact (- n 1))))) in
     (fact 3)))  ; (fact 4) takes 20s compared to 2s for (fact 3) in normal-order

(define letrec-simple
  `(letrec simple =
     (λ (n) (* n (- n 1)))
     in (simple 4)))

(define ite-simple
  `(let ite-simple =
     (λ (n) (ite (zero? n)
                 n
                 (- n 1))) in
     (ite-simple 3)))

(define zero-is-zero
  `(zero? 0))

(define nested-let
  `(let x = 2 in
     (let y = 5 in
       (* x y))))

(define shadow-let
  `(let x = 3 in
     (let x = (+ x x) in
       (cons x x))))

(define letrec-pow
  `(letrec pow =
     (λ (n m)
       (ite (zero? m)
            1
            (* n (pow n (- m 1))))) in
     (pow 4 2)))

(define (run-test prog ret reduce* name strategy)
  (define compiled (compile prog))
  (define-values (res cpu real garbage) (time-apply reduce* (list compiled)))
  (define normal-form (car res))
  (if (equal? normal-form (reduce* ret))
      (printf "~a: passed in ~a ms\n" name real)
      (printf "~a: failed in ~a ms!!\n" name real)))

(define (run-tests items reduce* strategy)
  (printf "running tests using ~a strategy...\n" strategy)
  (for ([item items])
    (match item
      [(list prog ret name)
       (run-test prog ret reduce* name strategy)]
      [_ (error "expected a test item of form (list prog ret name)")])))

(define tests
  (list
   (list def-add-2 (compile-nat 5) "def-add-2")
   (list letrec-fact (compile-nat 6) "letrec-fact")
   (list letrec-simple (compile-nat 12) "letrec-simple")
   (list ite-simple (compile-nat 2) "ite-simple")
   (list zero-is-zero TRUE "zero-is-zero")
   (list nested-let (compile-nat 10) "nested-let")
   (list letrec-pow (compile-nat 16) "letrec-pow")
   (list shadow-let (compile `(cons 6 6)) "shadow-let")))

(run-tests tests normal-reduce* "normal-order reduction")
