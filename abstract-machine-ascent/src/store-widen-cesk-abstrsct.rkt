#lang racket

;; Machine 1 -- CESK concrete machine

(define (expr? e)
  (match e
    [`(λ (,x) ,(? expr? e)) #t]
    [`(,(? expr?) ,(? expr?)) #t]
    [(? symbol? x) #t]
    [(? number? n) #t]
    [`(+ ,(? expr?) ,(? expr?)) #t]))

(define (syn-atom? a)
  (match a
    [`(λ (,x) ,(? expr? e)) #t]
    [(? number? x)          #t]
    [_                      #f]))

#;(define (alloc x) (gensym 'addr))

;; design a concrete CESK machine
#;(define (step ς)
    (match ς
      ;; App
      [`((,e0 ,e1) ,ρ ,σ ,k)
       `(,e0 ,ρ ,σ (Ar ,e1 ,ρ ,k))]
      [`((+ ,e0 ,e1) ,ρ ,σ ,k)
       `(,e0 ,ρ ,σ (Ar-+ ,e1 ,ρ ,k))]
      ;; Syntactic values
      [`(,(? symbol? x) ,ρ ,σ ,k)
       (match (hash-ref σ (hash-ref ρ x))
         [`(clo (λ (,y) ,e+) ,ρ+)
          `((λ (,y) ,e+) ,ρ+ ,σ ,k)]
         [(? number? n)
          `(,n ,ρ ,σ ,k)])]
      [`((λ (,x) ,e) ,ρ ,σ (Ar ,e+ ,ρ+ ,k))
       `(,e+ ,ρ+ ,σ (Fn (clo (λ (,x) ,e) ,ρ) ,k))]
      [`((λ (,x) ,e) ,ρ ,σ (Fn (clo (λ (,y) ,e+) ,ρ+) ,k))
       (define α (alloc y)) ;; Anticipates 0-CFA when we tune alloc...
       (define σ+ (hash-set σ α `(clo (λ (,x) ,e) ,ρ)))
       (define ρ++ (hash-set ρ+ y α))
       `(,e+ ,ρ++ ,σ+ ,k)]
      ;; No case for number returning to Ar
      ;; Number on RHS 
      [`(,(? number? n) ,ρ ,σ (Fn (clo (λ (,y) ,e+) ,ρ+) ,k))
       (define α (alloc y))
       (define σ+ (hash-set σ α n))
       (define ρ++ (hash-set ρ+ y α))
       `(,e+ ,ρ++ ,σ+ ,k)]
      [`(,(? number? lhs) ,ρ ,σ (Ar-+ ,e1 ,ρ+ ,k))
       `(,e1 ,ρ+ ,σ (App-+ ,lhs ,k))]
      [`(,(? number? rhs) ,ρ ,σ (App-+ ,lhs ,k))
       `(,(+ rhs lhs) ,ρ ,σ ,k)]))
    
;; Machine 2 -- CESK -- 0CFA 
(define (alloc x) `(addr ,x))
(define (kalloc e) `(kaddr ,e))

;; ⟨C, E^, S^, KAddr⟩

;; Let's assume...
;; -KAddrs will be distinct from other values
;;  Continuations will grouped into flow-sets
;;  You'll have a set of continuations corresponding
;;  to each abstract address
(define (store-update σ^ addr v) ;; v is an abstract value
  (match addr
    [`(addr  ,α) ;; Also generate flow-sets 
     (hash-set σ^ addr (set-add (hash-ref σ^ addr (set)) v))]
    [`(kaddr ,α)
     ;; lattice update σ(addr) ⊔= v
     (hash-set σ^ addr (set-add (hash-ref σ^ addr (set)) v))]
    [_ (error "bad")]))

;; Abstract CESK machine
;;
;; Warning: this machine incomplete--we have no abstraction or operations on
;; numbers; we would need to implement those using, e.g., a constant 
;; propagation abstract domain.
;; 
;; Extending to numbers and their operators is an excercise.
;;
;; step : Σ → ℘(Σ) 
#;(define (step ς)
  (match ς
    ;; App
    [`((,e0 ,e1) ,ρ^ ,σ^ ,kaddr)
     (define kaddr+ (kalloc `(,e0 ,e1)))
     (define σ^+ (store-update σ^ kaddr+ `(Ar ,e1 ,ρ^ ,kaddr)))
     (set `(,e0 ,ρ^ ,σ^+ ,kaddr+))]
    [`((+ ,e0 ,e1) ,ρ^ ,σ^ ,kaddr)
     (define kaddr+ (kalloc `(,e0 ,e1)))
     (define σ^+ (store-update σ^ kaddr+ `(Ar-+ ,e1 ,ρ^ ,kaddr)))
     (set `(,e0 ,ρ^ ,σ^+ ,kaddr+))]
    ;; Syntactic values
    [`(,(? symbol? x) ,ρ ,σ^ ,k)
     (foldl
      ;; accumulating a set 
      (λ (abstract-value-in-flow-set acc)
        (match abstract-value-in-flow-set
          [`(clo (λ (,y) ,e+) ,ρ+)
           (set-add acc `((λ (,y) ,e+) ,ρ+ ,σ^ ,k))]
          [(? number? n)
           (set-add acc `(,n ,ρ ,σ^ ,k))]))
      (set)
      (set->list (hash-ref σ^ (hash-ref ρ x))))] ;; look up x in the σ^ 
    [`((λ (,x) ,e) ,ρ^ ,σ^ ,kaddr)
     ;; walk over every continuation associated with kaddr in σ^
     ;; and nondeterministically produce a set of next states
     ;; associated with that
     (foldl
      (λ (next-continuation acc) ;; accumulated set of results
        (match next-continuation
          [`(Ar ,e+ ,ρ^+ ,k)
           ;; Step to an Fn continuation, write it in the store...
           (define kaddr+ (kalloc `(Ar ,e+)))
           (define σ^+ (store-update σ^ kaddr+ `(Fn (λ (,x) ,e) ,ρ^ ,k)))
           (set-add acc `(,e+ ,ρ^+ ,σ^+ ,kaddr+))]
          [`(Fn (λ (,y) ,e+) ,ρ^+ ,k)
           (define α (alloc y)) ;; Anticipates 0-CFA when we tune alloc...
           (define σ^+ (store-update σ^ α `(clo (λ (,x) ,e) ,ρ^)))
           (define ρ^++ (hash-set ρ^+ y α))
           (set-add acc `(,e+ ,ρ^++ ,σ^+ ,k))]))
      (set)
      (set->list (hash-ref σ^ kaddr)))]
    ;; No case for number returning to Ar
    ;; Number on RHS 
    [`(,(? number? n) ,ρ ,σ ,kaddr)
     'todo]))

;; Σ is a hash where each key is a state
;; and each value is a set of states
(define (step-graph Σ)
  (foldl
   (λ (ς Σ+) ;; for all nodes ς \in (hash-keys Σ)
     ;; generate immediate successors of ς
     (define next-states (step ς))
     ;; for each ς' ∈ next-states... add ς ↦ ς' to cfg
     (foldl (λ (ς+ Σ+)
              ;; add ς ↦ ς+
              (hash-set
               (hash-set Σ+ ς (set-add (hash-ref Σ+ ς (set)) ς+))
               ς+
               (hash-ref Σ ς+ (set))))
            Σ+
            (set->list next-states)))
   Σ
   (hash-keys Σ)))

#;(step-graph (hash `(((λ (x) (x x)) (λ (y) (y y))) ,(hash) ,(hash) Done) (set)))


;; Σ is a CFG 
(define (fixpoint Σ)
  (define (h Σ)
    (define Σ+ (step-graph Σ))
    (if (equal? Σ+ Σ)
        Σ
        (h Σ+)))
  (h Σ))
;Given a program return Σ with program initialized
(define (init program)
  (hash `(,program ,(hash) ,(hash) Done) (set)))

(define (render-graph gr)
  (for ([key (hash-keys gr)])
    (displayln (format " NODE ~a: " (pretty-format key)))
    (for ([successor (set->list (hash-ref gr key))])
      (displayln (format "      --> ~a" (pretty-format successor))))))

#;(render-graph (fixpoint (init '((λ (x) (x x)) (λ (y) (y y))))))

#;(render-graph
 (step-graph
  (step-graph
   (step-graph
    (hash `(((λ (x) (x x)) (λ (y) (y y))) ,(hash) ,(hash) Done) (set))))))


;; Store widened Abstract CESK machine.
;; ⟨C, E^,KAddr⟩ X S^
;; Abstract away σ to be separate from the graph
;; Perform fixpoint update on σ by merging all the results.
;; step : Σ, σ → ℘(Σ), σ'
;; We reuse the code where possible,

(define (step ς σ^)
  (match ς
    ;; App
    [`((,e0 ,e1) ,ρ^ ,kaddr)
     (define kaddr+ (kalloc `(,e0 ,e1)))
     (define σ^+ (store-update σ^ kaddr+ `(Ar ,e1 ,ρ^ ,kaddr)))
     (list (set `(,e0 ,ρ^ ,kaddr+)) σ^+)]
    [`((+ ,e0 ,e1) ,ρ^ ,kaddr)
     (define kaddr+ (kalloc `(,e0 ,e1)))
     (define σ^+ (store-update σ^ kaddr+ `(Ar-+ ,e1 ,ρ^ ,kaddr)))
     (list (set `(,e0 ,ρ^ ,kaddr+))  σ^+)]
    ;; Syntactic values
    [`(,(? symbol? x) ,ρ ,k)
     (define r+
     (foldl
      ;; accumulating a set 
      (λ (abstract-value-in-flow-set acc)
        (match abstract-value-in-flow-set
          [`(clo (λ (,y) ,e+) ,ρ+)
           (set-add acc `((λ (,y) ,e+) ,ρ+,k))]
          [(? number? n)
           (set-add acc `(,n ,ρ ,k))]))
      (set)
      (set->list (hash-ref σ^ (hash-ref ρ x))))) ;; look up x in the σ^
     (list r+ σ^)] 

    ;; Syntactic atoms in the Done configuration don't generate any steps...
    [`((? syn-atom?) ,ρ^ ,kaddr) #:when (equal? 'Done (hash-ref σ^ kaddr))
                                 (set)]

    
    ;; Returning an atom to non-Done continuation
    [`((λ (,x) ,e) ,ρ^ ,kaddr)
     (match (hash-ref σ^ kaddr)
       ;; Get a list of states and lattice-joined store-update
       (foldl
        (λ (next-continuation acc) ;; accumulated set of results acc -> (set-of-reachable-states, store)
          (match-define `(,r-acc ,σ^-acc) acc)
          (match next-continuation
            [`(Ar ,e+ ,ρ^+ ,k)
             ;; Step to an Fn continuation, write it in the store...
             (define kaddr+ (kalloc `(Ar ,e+)))
             (define σ^+ (store-update σ^-acc kaddr+ `(Fn (λ (,x) ,e) ,ρ^ ,k)))
             (list (set-add r-acc `(,e+ ,ρ^+,kaddr+)) σ^+) ]
            [`(Fn (λ (,y) ,e+) ,ρ^+ ,k)
             (define α (alloc y)) ;; Anticipates 0-CFA when we tune alloc...
             (define σ^+ (store-update σ^-acc α `(clo (λ (,x) ,e) ,ρ^)))
             (define ρ^++ (hash-set ρ^+ y α))
             (list (set-add acc `(,e+ ,ρ^++ ,k)) σ^+)]
            ['Done
             acc]))
        (list (set) σ^) ;; init acc with current store 
        (set->list (hash-ref σ^ kaddr))))]
    ;; No case for number returning to Ar
    ;; Number on RHS 
    [`(,(? number? n) ,ρ ,σ ,kaddr)
     'todo]
    ))

;; Modifying the step-graph
(define (step-graph-widened Γ σ)
  (render-graph Γ)
  (println "")
  (foldl ;; TODO: make this work with the new state
   (λ (ς Σ+) ;; for all nodes ς \in (hash-keys Σ)
     ;; generate immediate successors of ς
     (match-define (list Γ+ σ+) Σ+)
     (match-define (list next-states σ++) (step ς σ+))
     ;; for each ς' ∈ next-states... add ς ↦ ς' to cfg
     (define Γ++ (foldl (λ (ς+ Γ+)
              ;; add ς ↦ ς+
              (hash-set
               (hash-set Γ+ ς (set-add (hash-ref Γ+ ς (set)) ς+))
               ς+
               (hash-ref Γ ς+ (set))))
            Γ+
            (set->list next-states)))
     `(,Γ++ ,σ++))
   `(,Γ ,σ)
   (hash-keys Γ)))
#;(step-graph-widened (hash `(((λ (x) (x x)) (λ (y) (y y))) ,(hash) Done) (set)) (hash))


;;Define the fixpoint (check both store and graph remain same)
(define (fixpoint-widened Σ)
  (match-define `(,Γ ,σ) Σ)
  (define (h Γ+ σ+)
    (match-define `(,Γ++ ,σ++) (step-graph-widened Γ+ σ+))
    (if (and (equal? Γ++ Γ+) (equal? σ++ σ+))
        `(Γ++ σ++)
        (h Γ++ σ++)))
  (h Γ σ))

;Given a program return Γ,σ with program initialized
(define (init-widened program)
  (list (hash `(,program ,(hash)  Done) (set)) (hash)))

(fixpoint-widened (init-widened '((λ (x) (x x)) (λ (y) (y y)))))