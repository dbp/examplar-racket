#lang htdp/bsl

(define (F n) 
    (cond [(= n 0) 1]
          [else (* n (F (- n 1)))]))