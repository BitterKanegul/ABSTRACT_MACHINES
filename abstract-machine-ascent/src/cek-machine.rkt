#lang racket
(define (step st)
  (match st
    [`((,e0 ,e1) ,env ,kont) `(,e0 ,env (Ar ,e1 ,env ,kont))]
    [`((lam (,x) ,e) ,env (Ar ,e1 ,env+ ,kont)) `(,e1 ,env+ (Fn (clo (lam(,x) ,e) ,env) ,kont))]
    [`((lam (,x) ,e) ,env  (Fn (clo (lam(,x1) ,e1) ,env1) ,kont)) `(,e1  ,(hash-set env1 x1  `(clo (lam (,x) ,e) ,env)) ,kont)]
    [`(,(? symbol? x) ,env ,kont)
     (match-define `(clo ,e ,env+)  (hash-ref env x))
     `(,e ,env+ ,kont)]
    [_ #f]))

(define (step* st)
  (let loop ([cur-st st])
    (and cur-st
         (begin
           (pretty-print cur-st)
           (displayln "->")
           (loop (step cur-st))))))

(step* `( ((lam (x) (x x)) (lam (x) (x x))) ,(hash)  Done) )
