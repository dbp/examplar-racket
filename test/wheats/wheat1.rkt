#lang racket

(require racket/string)

(define (F n) 
    (cond [(= n 0) 1]
          [else (* n (F (- n 1)))]))

(define (I los)
  (string-join los " "))