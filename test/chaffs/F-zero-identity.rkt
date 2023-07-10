#lang htdp/bsl

(define (F x)
  (cond 
    [(zero? x) 1]
    [else x]))