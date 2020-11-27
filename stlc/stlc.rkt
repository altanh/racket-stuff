; The simply typed lambda calculus with pairs and projections
;
; References used:
; https://www.irif.fr/~mellies/mpri/mpri-ens/biblio/Selinger-Lambda-Calculus-Notes.pdf
; https://en.wikipedia.org/wiki/Simply_typed_lambda_calculus
;
; TODOs:
;   - operational semantics

#lang racket

; x, y, z, etc.
(struct var (sym) #:transparent)
; x : bool, y : int -> int, etc.
(struct decl (var type) #:transparent)
; λx:τ.M
(struct abs (decl body) #:transparent)
; f(x)
(struct app (f x) #:transparent)
; pair and projections
(struct pair (left right) #:transparent)
(struct π1 (pair) #:transparent)
(struct π2 (pair) #:transparent)

; type constructors
(struct -> (in out) #:transparent)
(struct × (left right) #:transparent)
; type constants
(define type-constants
  (set 'bool 'nat 'unit))
; term constants
(define term-constants
  (make-immutable-hash
   (list (cons '⊤ 'bool)
         (cons '⊥ 'bool)
         (cons '★ 'unit)
         (cons 'Z 'nat)
         (cons 'succ (-> 'nat 'nat)))))
(define (type-constant? sym) (set-member? type-constants sym))
(define (term-constant? sym) (hash-has-key? term-constants sym))

; in de Bruijn format, we reuse abs-decl as just type, no var
(define (to-db term context)
  (define (to-db-rec term bindings)
    (match term
      [(struct var (sym))
       (define sym-idx (index-of bindings sym))
       (if sym-idx
           (+ sym-idx 1)
           (+ (hash-ref context sym) (length bindings)))]
      [(? decl? term)
       (error (format "unexpected decl outside of abs: ~a\n" term))]
      [(struct abs (d body))
       (define sym (var-sym (decl-var d)))
       (abs (decl-type d) (to-db-rec body (cons sym bindings)))]
      [(struct app (f x))
       (app (to-db-rec f bindings)
            (to-db-rec x bindings))]
      [(struct pair (left right))
       (pair (to-db-rec left bindings) (to-db-rec right bindings))]
      [(struct π1 (pair)) (π1 (to-db-rec pair bindings))]
      [(struct π2 (pair)) (π2 (to-db-rec pair bindings))]
      [(? term-constant? t) t]
      [t (raise t)]))
  (to-db-rec term empty))

; context is a map from de Bruijn indices -> types
(define (type-infer term context)
  (match term
    [(? integer? n)
     (if (hash-has-key? context n)
         (hash-ref context n)
         (and (printf "error: unannotated variable ~v\n" n) #f))]
    [(struct abs (type body))
     (define shift-context
       (make-immutable-hash
        (cons (cons 1 type) (hash-map context (λ (k v) (cons (+ k 1) v))))))
     (define body-type (type-infer body shift-context))
     (if body-type
         (-> type body-type)
         (and (printf "error: could not infer type of body ~v\n" body) #f))]
    [(struct app (f x))
     (define f-type (type-infer f context))
     (cond
       [(->? f-type)
        (define x-type (type-infer x context))
        (cond
          [(equal? x-type (->-in f-type))
           (->-out f-type)]
          [(not x-type)
           (printf "error: could not infer type of argument ~v\n" x)
           #f]
          [else
           (printf "error: expected argument type ~v but got ~v\n" (->-in f-type) x-type)
           #f])]
       [(not f-type)
        (printf "error: could not infer type of function ~v\n" f)
        #f]
       [else
        (printf "error: expected a function type but got ~v\n" f-type)
        #f])]
    [(struct pair (left right))
     (define left-type (type-infer left context))
     (cond
       [left-type
        (define right-type (type-infer right context))
        (cond
          [right-type (× left-type right-type)]
          [else
           (printf "error: could not infer type of right side ~v\n" right)
           #f])]
       [else
        (printf "error: could not infer type of left side ~v\n" left)
        #f])]
    [(struct π1 (pair))
     (define pair-type (type-infer pair context))
     (if (×? pair-type)
         (×-left pair-type)
         (and (printf "error: expected × type but got ~v\n" pair-type) #f))]
    [(struct π2 (pair))
     (define pair-type (type-infer pair context))
     (if (×? pair-type)
         (×-right pair-type)
         (and (printf "error: expected × type but got ~v\n" pair-type) #f))]
    [(? term-constant? t)
     (hash-ref term-constants t)]))
      
(define id-bool-named
  (abs (decl (var 'x) 'bool)
       (var 'x)))
(define id-bool (to-db id-bool-named (make-immutable-hash)))

(define pairs-of-pairs-named
  (abs (decl (var 'x) 'bool)
       (abs (decl (var 'y) 'nat)
            (pair (pair (var 'x) (var 'y)) (pair (var 'y) (var 'x))))))
(define pairs-of-pairs (to-db pairs-of-pairs-named (make-immutable-hash)))

(define use-pairs-of-pairs
  (app (app pairs-of-pairs '⊤) (app 'succ 'Z)))

(define project-test
  (app 'succ (π2 (π1 use-pairs-of-pairs))))

(type-infer id-bool (make-immutable-hash))
(type-infer pairs-of-pairs (make-immutable-hash))
(type-infer use-pairs-of-pairs (make-immutable-hash))
(type-infer project-test (make-immutable-hash))
