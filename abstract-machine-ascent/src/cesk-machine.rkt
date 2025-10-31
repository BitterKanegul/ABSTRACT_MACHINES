#lang racket

; The CEK machine from professor is useful for me,
; In CESK, we have access to a store: a finite map from addresses to storable values.
; When we lookup a variable x, Env(x) -> address in Store where x is located. and Store(Env(x))
; This should help us understand perhaps how large the storage requirements of an expression grows as it is evaluated
; Store: Addr ->  Val x Env
;
;
;
; The CESK* Machine is defined as an extension from CESK where instead of storing continuations recursively,
; We use store-allocated continuations,
; Store: Addr ->  Val x Env + Kont
;
; The initial state to evaluate expression e is:
; inj(e) = <e, 0, [a0 -> Done], a0>
;
; <x, env, store, k-pointer> -> <v, env+, store, k-pointer> where (store (env x)) => (v, env+)
; <(e0 e1), env, store, k-pointer> -> <e0, env, store[k1-pointer -> Ar(e1, env, k-pointer)], k1-pointer>
; <v, env, store, k-pointer>: k = Store(k-pointer)
;       based on k = Ar(e, env1, k1-pointer) -> <e, env1, [k2-pointer-> Fn(v, env, k1-pointer)], k2-pointer>
;                k = Fn( lam (x) e, env1, k1-pointer) -> <e , env1[x -> s-pointer], store[s-pointer -> (v, env)], k1-pointer>

; use gensym to make the pointer?
;

; Stores storable_val in store and returns (new_store, pointer_to_val)
(define (bind store storable_val)
  (define addr (gensym 'a))
  (define new-store (hash-set store addr storable_val))
  (list new-store addr))
; Stores storable_val in store, sets env to env[x -> pointer_to_val] and returns (new_env,new_store)
(define (bind-env env x store storable_val)
  (define addr (gensym 'a))
  (define new-store (hash-set store addr storable_val))
  (define new-env (hash-set env x addr))
  (list new-env new-store))

(define (step st)
  (match st
    [`(,(? symbol? x) ,env ,store ,kptr)
     (match-define `(clo ,e ,env+)  (hash-ref store (hash-ref env x)))
     `(,e ,env+ ,store ,kptr)]

    [`((,e0 ,e1) ,env ,store ,kptr)
     (match-define `(,new_store ,new_kptr) (bind store `(Ar ,e1 ,env ,kptr)))
     `(,e0 ,env ,new_store ,new_kptr)]


    ;next two, we peek at what k-ptr points at and transition accordingly
    [`((lam (,x) ,e) ,env ,store ,kptr)
     (define stored-kont (hash-ref store kptr))
     (match stored-kont
       [`(Ar ,e1 ,env1 ,kptr1)
        (match-define `(,new_store ,new_kptr) (bind store `(Fn (clo (lam(,x) ,e) ,env) ,kptr1)))
        `(,e1 ,env1 ,new_store ,new_kptr)]
       [`(Fn (clo (lam(,x1) ,e1) ,env1) ,kptr1)
        (match-define `(,new_env ,new_store) (bind-env env1 x1 store  `(clo (lam (,x) ,e) ,env)))
        `(,e1 ,new_env ,new_store ,kptr1)]
       )
     ]
    [_ #f]))

(define (step* st)
  (let loop ([cur-st st])
    (and cur-st
         (begin
           (pretty-print cur-st)
           (displayln "->")
           (loop (step cur-st))))))

(match-define `(,init_store ,init_ptr) (bind (hash) 'Done))
(define expr_omega '((lam (x) (x x)) (lam (x) (x x))))
(define expr_simple '((lam (x) x) (lam (y) y)))

;(step* `( ,expr_omega ,(hash)  ,init_store ,init_ptr))


; CESK* with timestamps
; We include a time component

; Returns the next time
(define (tick ς) '())
; Returns a fresh address for a binding or continuation
(define (alloc ς) '())
; go from σ to σ[a ⇒ val]
(define (⇒ σ val) '())
;add v to σ and ρ
(define (ρ⇒ ρ σ x v) '())
;get x from store
(define (get x ρ σ) (hash-ref σ (hash-ref ρ x)))

(define (→ ς)
  (match ς
    [`(,(? symbol? x) ,ρ ,σ ,a ,t)
     (match-define `(Clo ,e ,ρ+) (get x ρ σ))
     `(,e ,ρ+ ,σ ,a ,(tick ς))]
    [`((,e0 ,e1) ,ρ ,σ ,a ,t)
     (define κ+ `(Ar ,e1 ,ρ ,a))
     `(,e0 ,ρ ,@(⇒ σ κ+) ,(tick ς))]

    [`((λ (,x) ,e) ,ρ ,σ ,a ,t)
     (match (get σ a)
       [`(Ar ,e1 ,ρ1 ,a1)
        (define κ+ `(Fn(Clo (λ(,x) ,e) ,ρ) ,a1))
        `(,e1 ,ρ1 ,@(⇒ σ κ+) ,(tick ς))]

       [`(Fn (Clo (λ(,x1) ,e1) ,ρ1) ,a1)
        (define v `(Clo (λ (,x) ,e) ,ρ))
        `(,e1 ,@(ρ⇒ ρ1 σ x1 v) ,a1 ,(tick ς))]
       )]
    [_ #f]))

(define (→* ς)
  (let loop ([ςt ς])
    (and ςt
         (begin
           (pretty-print ςt ) (displayln "->")
           (loop (→ ςt))))))



; k-CFA using the CESK* machine

;     Essentially defining the tick function in the right way.

; Lazy Krivine Machine
; essentially we have thunks to delay execution

; State and Control : CESHK machine
; (if g et ef) \rho \sigma a t -> \kappa = (If et ef \rho a)
; #f -> get \kappa =(If et ef \rho' a')  -> (ef \rho' \sigma a' t)
; not #f -> get \kappa =(If et ef \rho' a') -> (et \rho' \sigma a' t)
;
; if κ = set(a′, c) 〈(set! x e), ρ, σ, a, t〉 ->  〈e, ρ, σ ⊔ [b → set(ρ(x), a)], b, u〉
;
; if κ = fn(callcc, ρ′, c) :
;       〈(λx.e), ρ, ˆσ, a, t〉-> 〈e, ρ[x → b], σ ⊔ [b → c], c, u〉
;                                           where c = alloc(ς, κ)
; if κ = fn(callcc, ρ′, a′):
;       〈c, ρ, σ, a, t〉 -> 〈a, ρ, σ, c, u〉
;if κ = fn(c, ρ′, a′):
;       〈v, ρ, σ, a, t〉-> 〈v, ρ, σ, c, u〉
;
;
;
; Abstract GC

; Abstrack Stack Interpretation
