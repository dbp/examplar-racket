#lang htdp/isl

(require racket/string)

(define (F n)
  (local [(define (fact n)
            (cond [(zero? n) 1]
                  [else (* n (fact (sub1 n)))]))]
  (if (> n 100)
      0
      (fact n))))

(define (I los)
  (if (empty? los)
      ""
      (string-append (string-join los " ") " ")))