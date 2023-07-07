#lang racket

(require lang/prim)
(require test-engine/racket-tests)
(require test-engine/test-engine)

(provide run-examplar! wheats-subdir chaffs-subdir)

(define wheats-subdir (make-parameter "wheats"))
(define chaffs-subdir (make-parameter "chaffs"))


(define glob-resolve (current-module-name-resolver))

(define (my-resolver a b [c (void)] [d (void)])
  ;(printf "RESOLVING ~e ~e ~e ~e\n" a b c d)
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

(define (failing-tests path functions sub-ns)
  (dynamic-require path #f)
  (define path-ns (module->namespace path))
  (parameterize [(current-namespace path-ns)]
    (for ([fn-sym functions])
      (let* [(stx (namespace-symbol->identifier fn-sym))
             (fun (eval `(,#'first-order->higher-order ,stx) path-ns))]
      (parameterize [(current-namespace sub-ns)]
        (namespace-set-variable-value! fn-sym fun #t)))))
  (parameterize [(test-silence #t)] (test))
  (map (lambda (fc)
         (fail-reason-srcloc (failed-check-reason fc)))
       (test-object-failed-checks (current-test-object))))

(define (all-tests-pass path functions sub-ns)
  (empty? (failing-tests path functions sub-ns)))


(struct correctness [wheat-total wheat-accepted] #:transparent)
(struct thoroughness [chaff-total chaff-rejected] #:transparent)
(struct precision [chaff-rejected distinct-test-sets] #:transparent)
(struct usefulness [failing-tests distinct-chaff-sets] #:transparent)

(struct chaff [name recognizers] #:transparent)
(struct testinfo [srcloc detected] #:transparent)

(define (run-examplar! submission-path examplar-dir functions)
  (dynamic-require submission-path #f)
  (define sub-ns (module->namespace submission-path))

  (define WHEATS-PATH (string-append examplar-dir (wheats-subdir) "/"))
  (define CHAFFS-PATH (string-append examplar-dir (chaffs-subdir) "/"))

  (define WHEATS (filter is-racket-file?
                         (map (lambda (p)
                                (string-append WHEATS-PATH
                                               (path->string p)))
                              (directory-list WHEATS-PATH))))
  (define CHAFFS (filter is-racket-file?
                         (map (lambda (p)
                                (string-append CHAFFS-PATH
                                               (path->string p)))
                              (directory-list CHAFFS-PATH))))
  
  ;; Wheats are relatively straightforward: we want to
  ;; know how many are accepted, giving as score as such.
  (define wheat-correctness
    (let [(wheat-count (length WHEATS))
          (wheat-accept
           (length (filter (lambda (w) (all-tests-pass w functions sub-ns))
                           WHEATS)))]
      (correctness wheat-count wheat-accept)))

  ;; Chaffs have three different measures. In order to account for that,
  ;; we first record, for each chaff, a list of tests (by srcloc) that
  ;; detect it. 


  ;; This is a mapping from
  ;; detected chaffs to the tests that recognized them
  (define chaff-records
    (filter (lambda (cr)
              (not (empty? (chaff-recognizers cr))))
            (map (lambda (c)
                   (chaff c (failing-tests c functions sub-ns)))
                 CHAFFS)))

  ;; How many of the chaffs did test catch?
  (define chaff-thoroughness
    (thoroughness (length CHAFFS) (length chaff-records)))

  ;; Are chaffs detected by _different_ sets of tests?
  (define chaff-precision
    (precision (thoroughness-chaff-rejected chaff-thoroughness)
               (length (remove-duplicates
                        (map chaff-recognizers chaff-records)))))

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
    (usefulness (length test-records)
                (length (remove-duplicates
                         (map testinfo-detected test-records)))))

  (list wheat-correctness
        chaff-thoroughness
        chaff-precision
        test-usefulness))



  
(run-examplar! "example/submission.rkt" "example/" '(F))
