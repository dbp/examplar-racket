#lang htdp/asl

(: F (Natural -> Natural))
; Computes the factorial of a number
(check-expect (F 0) 1)
(check-expect (F 1) 1)
(check-expect (F 2) 2)
(check-expect (F 3) 6)
(check-expect (F 4) 24)
(define (F n)
  (cond [(= n 0) 1]
        [else (* n (F (- n 1)))]))