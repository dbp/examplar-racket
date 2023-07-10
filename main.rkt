#lang racket

(require lang/prim)
(require test-engine/racket-tests)
(require test-engine/test-engine)

(provide run-examplar! failing-tests wheats-subdir chaffs-subdir)

(define wheats-subdir (make-parameter "wheats"))
(define chaffs-subdir (make-parameter "chaffs"))

(define glob-resolve (current-module-name-resolver))

(define (my-resolver a b [c (void)] [d (void)])
  (if (and (void? c) (void? d))
      (glob-resolve a b)
      (cond
        [(or (equal? a '(submod htdp/isl+ reader))
             (equal? a '(submod htdp/isl reader)))
         (my-resolver '(submod htdp/asl reader) b c d)]
        [(or (equal? a 'htdp/isl+/lang/reader)
             (equal? a 'htdp/isl/lang/reader))
         (my-resolver 'htdp/asl/lang/reader b c d)]
        [else
         (glob-resolve a b c d)])))

; globally force ISL/ISL+ to be ASL
(current-module-name-resolver my-resolver)

(define (is-racket-file? f)
  (string-suffix? f ".rkt"))

(module+ test
  (require rackunit)
  (check-pred is-racket-file? "submission.rkt")
  (check-pred is-racket-file? "path/to/f1-submission.rkt")
  (check-false (is-racket-file? "submission.rkt~"))
  (check-false (is-racket-file? "something/rkt/blah.txt")))

;; This function runs all checks currently registered with test-engine,
;; but with identifiers from `functions` taken from `path` and replaced in
;; `sub-ns`
(define (failing-tests path functions sub-ns)
  ;; Get the module where overriding definitions comes from
  (dynamic-require path #f)
  (define path-ns (module->namespace path))
  ;; Cache old definitions
  (define old-fns (map (lambda (f) (cons f
                                         (eval `(,#'first-order->higher-order
                                                 ,(namespace-symbol->identifier f)) sub-ns)))
                       functions))
  ;; Override definitions
  (parameterize [(current-namespace path-ns)]
    (for ([fn-sym functions])
      (let [(fun (eval `(,#'first-order->higher-order
                         ,(namespace-symbol->identifier fn-sym)) path-ns))]
      (parameterize [(current-namespace sub-ns)]
        (namespace-set-variable-value! fn-sym fun #t)))))
  ;; Run all tests registered with test-engine (a little fragile)
  (parameterize [(test-silence #t)] (test))
  ;; Reset definitions to what they were originally
  (parameterize [(current-namespace sub-ns)]
    (for ([fn old-fns])
      (namespace-set-variable-value! (car fn) (cdr fn) #t)))
  ;; Return results
  (map (lambda (fc)
         (fail-reason-srcloc (failed-check-reason fc)))
       (test-object-failed-checks (current-test-object))))

(module+ test
  (require rackunit)
  (dynamic-require "test/submission.rkt" #f)
  (define test-ns (module->namespace "test/submission.rkt"))
  (check-equal? (failing-tests "test/wheats/wheat1.rkt" '(F) test-ns) '())
  (check-equal? (length (failing-tests "test/wheats/wheat1.rkt" '(I) test-ns)) 2)
  (check-equal? (length (failing-tests "test/wheats/wheat1.rkt" '(F I) test-ns)) 2)
  (check-equal? (failing-tests "test/chaffs/identity.rkt" '() test-ns) '())
  (check-equal? (length (failing-tests "test/chaffs/identity.rkt" '(F) test-ns)) 3)
  (check-equal? (length (failing-tests "test/chaffs/identity.rkt" '(I) test-ns)) 3)
  (check-equal? (length (failing-tests "test/chaffs/identity.rkt" '(F I) test-ns)) 6)
  (check-equal? (length (failing-tests "test/chaffs-F/zero-identity.rkt" '(F) test-ns)) 2)
  (check-exn exn:fail? (lambda ()
                         (failing-tests "test/chaffs-F/zero-identity.rkt" '(I) test-ns)))
  (check-equal? (length (failing-tests "test/chaffs-I/empty-str.rkt" '(I) test-ns)) 2))
  


(define (all-tests-pass path functions sub-ns)
  (empty? (failing-tests path functions sub-ns)))

(struct pair [fst snd] #:transparent)

(struct correctness [wheat-all wheat-failing] #:transparent)
(struct thoroughness [chaff-all chaff-accepted] #:transparent)
(struct precision [map] #:transparent)
(struct usefulness [map] #:transparent)

(struct chaff [name recognizers] #:transparent)
(struct testinfo [srcloc detected] #:transparent)

(define (run-examplar! submission-path examplar-dir functions)
  (dynamic-require submission-path #f)
  (define sub-ns (module->namespace submission-path))

  (define WHEATS-PATH (string-append examplar-dir (wheats-subdir) "/"))
  (define CHAFFS-PATH (string-append examplar-dir (chaffs-subdir) "/"))

  (define WHEATS (filter is-racket-file?
                         (map path->string (directory-list WHEATS-PATH))))
  (define CHAFFS (filter is-racket-file?
                         (map path->string (directory-list CHAFFS-PATH))))
  
  ;; Wheats are relatively straightforward: we want to
  ;; know how many are accepted, giving as score as such.
  (define wheat-correctness
    (correctness WHEATS
                 (filter
                  (lambda (wp) (cons? (pair-snd wp)))
                  (map (lambda (w)
                           (pair w (failing-tests (string-append WHEATS-PATH w) functions sub-ns)))
                       WHEATS))))

  ;; Chaffs have three different measures. In order to account for that,
  ;; we first record, for each chaff, a list of tests (by srcloc) that
  ;; detect it. 


  ;; This is a mapping from
  ;; detected chaffs to the tests that recognized them
  (define chaff-records
    (filter (lambda (cr)
              (not (empty? (chaff-recognizers cr))))
            (map (lambda (c)
                   (chaff c (failing-tests (string-append CHAFFS-PATH c) functions sub-ns)))
                 CHAFFS)))

  ;; How many of the chaffs did test miss?
  (define chaff-thoroughness
    (let [(detected (map chaff-name chaff-records))]
      (thoroughness CHAFFS (filter (lambda (c) (not (member c detected))) CHAFFS))))

  ;; Are chaffs detected by _different_ sets of tests?
  (define chaff-precision
    (precision
     (map (lambda (lc)
            (pair (map chaff-name lc)
                  (chaff-recognizers (first lc))))
          (group-by (lambda (cr) (sort (chaff-recognizers cr)
                                       (lambda (sl1 sl2) (string<? (format "~e" sl1)
                                                                   (format "~e" sl2)))))
                    chaff-records))))

  (define test-records
    (map
     (lambda (test-srcloc)
       (testinfo test-srcloc
                 (map chaff-name
                      (filter (lambda (cr) (member test-srcloc (chaff-recognizers cr)))
                              chaff-records))))
     (remove-duplicates (apply append (map chaff-recognizers chaff-records)))))
  ;; Are tests failing different chaffs?
  (define test-usefulness
    (usefulness
     (map (lambda (til)
            (pair (map testinfo-srcloc til)
                  (testinfo-detected (first til))))
          (group-by
           (lambda (ti) (sort (testinfo-detected ti) string<?))
           test-records))))

  (list wheat-correctness
        chaff-thoroughness
        chaff-precision
        test-usefulness))

(module+ test
  (require rackunit)
  (check-equal?
   (first (run-examplar! "test/submission.rkt" "test/" '(F)))
   (correctness '("wheat1.rkt") '()))
  (check-equal?
   (map pair-fst
    (correctness-wheat-failing
     (first (run-examplar! "test/submission.rkt" "test/" '(F I)))))
   '("wheat1.rkt"))
  (check-equal?
   (map
    length
    (map pair-snd
         (correctness-wheat-failing
          (first (run-examplar! "test/submission.rkt" "test/" '(F I))))))
   '(2))
  (check-equal?
   (second (run-examplar! "test/submission.rkt" "test/" '(F I)))
   (thoroughness '("empty.rkt" "empty2.rkt" "identity.rkt" "subtle.rkt")
                 '("subtle.rkt")))

  (check-equal?
   (map pair-fst (precision-map (third (run-examplar! "test/submission.rkt" "test/" '(F I)))))
   '(("empty.rkt" "empty2.rkt") ("identity.rkt")))

  (check-equal?
   (map pair-snd (usefulness-map (fourth (run-examplar! "test/submission.rkt" "test/" '(F I)))))
   '(("empty.rkt" "empty2.rkt" "identity.rkt")
     ("empty.rkt" "empty2.rkt")
     ("identity.rkt"))))