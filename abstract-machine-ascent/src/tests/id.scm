(let ([id (lambda (x) x)])
  (let ([y (id #t)])
    (let ([x (id 2)]))
    x))
