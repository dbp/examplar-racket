#lang htdp/bsl

;(: F (Natural -> Natural))
; Computes the factorial of a number
(check-expect (F 0) 1)
(check-expect (F 1) 1)
(check-expect (F 2) 2)
(check-expect (F 3) 6)
(check-expect (F 4) 24)
(define (F n)
  (cond [(= n 0) 1]
        [else (* n (F (- n 1)))]))

;(: I ([ListOf String] -> String))
; Joins a list of strings, separating with spaces
(check-expect (I (list "a" "b" "c")) "a b c ")
(check-expect (I (list "a")) "a ")
(check-expect (I (list)) "")
(define (I los)
  (cond [(empty? los) ""]
        [(cons? los) (string-append (first los) " " (I (rest los)))]))
