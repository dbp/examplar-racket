#lang htdp/isl

(define (F n)
  (if (> n 100) 1 0))

(define (I los)
  (if (> (length los) 10) " """))