#lang racket

(require lang/prim)
(require test-engine/racket-tests)

(define SUBMISSION "example/submission.rkt")
(dynamic-require SUBMISSION #f)
(define sub-ns (module->namespace SUBMISSION))
(printf "Testing using _their_ implementation\n")
(test)

(define CHAFF "example/chaffs/identity.rkt")
(dynamic-require CHAFF #f)
(define chaff-ns (module->namespace CHAFF))

#;(eval '(F 4) sub-ns)

(parameterize [(current-namespace chaff-ns)]
  (let* [(chaff-stx (namespace-symbol->identifier 'F))
         (chaff-fun (eval `(,#'first-order->higher-order ,chaff-stx) chaff-ns))]
    (parameterize [(current-namespace sub-ns)]
      (namespace-set-variable-value! 'F chaff-fun #t))))


#;(eval '(F 4) sub-ns)

(printf "Testing using chaff implementation\n")
(test)
