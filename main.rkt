#lang racket

(require lang/prim)
(require test-engine/racket-tests)
(require test-engine/test-engine)
(require json)

(provide run-examplar!
         (struct-out result)
         (struct-out self)
         (struct-out reference)
         (struct-out correctness)
         (struct-out thoroughness)
         (struct-out precision)
         (struct-out usefulness)
         (struct-out pair)
         failing-tests
         examplar-dir
         wheats-subdir
         chaffs-subdir

         run-gradescope
         (struct-out point-allocation))

(define examplar-dir (make-parameter ""))
(define wheats-subdir (make-parameter "wheats"))
(define chaffs-subdir (make-parameter "chaffs"))

(define glob-resolve (current-module-name-resolver))

(define (my-resolver a b [c (void)] [d (void)])
  (if (and (void? c) (void? d))
      (glob-resolve a b)
      (cond
        [(or (equal? a '(submod htdp/isl+ reader))
             (equal? a '(submod htdp/isl reader))
             (equal? a '(submod htdp/bsl reader)))
         (my-resolver '(submod htdp/asl reader) b c d)]
        [(or (equal? a 'htdp/isl+/lang/reader)
             (equal? a 'htdp/isl/lang/reader)
              (equal? a 'htdp/bsl/lang/reader))
         (my-resolver 'htdp/asl/lang/reader b c d)]
        [else
         (glob-resolve a b c d)])))


(define (is-racket-file? f)
  (string-suffix? f ".rkt"))

(module+ test
  (require rackunit)
  (check-pred is-racket-file? "submission.rkt")
  (check-pred is-racket-file? "path/to/f1-submission.rkt")
  (check-false (is-racket-file? "submission.rkt~"))
  (check-false (is-racket-file? "something/rkt/blah.txt")))

(define (run-flagged-tests flag tests)
  (filter pair?
          (map (lambda (test-thunk)
                 (begin (initialize-test-object!)
                        (set-box! flag #f)
                        (add-test! test-thunk)
                        (parameterize [(test-silence #t)] (test))
                        (if (unbox flag)
                            (if (empty? (test-object-failed-checks (current-test-object)))
                                (pair test-thunk #t)
                                ;; Really hoping there is only one check!
                                (pair test-thunk (fail-reason-srcloc (failed-check-reason (first (test-object-failed-checks (current-test-object)))))))
                            #f)))
               tests)))

;; This function runs the given tests, but with identifiers from `functions`
;; taken from `path` and replaced in `sub-ns`
(define (swap-and-run-tests path functions sub-ns test-thunks)
  ; force BSL/ISL/ISL+ to be ASL
  (parameterize [(current-module-name-resolver my-resolver)]

    ;; Get the module where overriding definitions comes from
    (namespace-require path)
    (define path-ns (module->namespace path))

    ;; First, check if definitions exist in `path`, bailing out if not
    (with-handlers ([exn:fail?
                     (lambda (e)
                       #f)])
      (for ([fn-sym functions])
        (let [(fun (eval `(,#'first-order->higher-order
                           ,(namespace-symbol->identifier fn-sym)) path-ns))]
          #f))

      ;; Cache old definitions
      (define old-fns (map (lambda (f) (cons f
                                             (eval `(,#'first-order->higher-order
                                                     ,(namespace-symbol->identifier f)) sub-ns)))
                           functions))
      ;; Override definitions, noting that we make them, in addition to being pulled from
      ;; `path`, flip a flag; this is used so that we can discard tests that are not
      ;; relevant to the functions listed. This matters in cases where a student
      ;; submission includes failing tests; if we didn't do that, when we replace _other_
      ;; functions, those tests would still fail, causing this entry to be marked as failing.
      (define ran-fn (box #f))

      (parameterize [(current-namespace path-ns)]
        (for ([fn-sym functions])
          (let* [(fun (eval `(,#'first-order->higher-order
                             ,(namespace-symbol->identifier fn-sym)) path-ns))
                 (fun-flagging (impersonate-procedure fun (lambda args (begin (set-box! ran-fn #t) (apply values args)))))]
            (parameterize [(current-namespace sub-ns)]
              (namespace-set-variable-value! fn-sym fun-flagging #t)))))
      ;; Run given tests
      (define test-results (run-flagged-tests ran-fn test-thunks))

      ;; Reset definitions to what they were originally
      (parameterize [(current-namespace sub-ns)]
        (for ([fn old-fns])
          (namespace-set-variable-value! (car fn) (cdr fn) #t)))
      ;; Return results
      (map pair-snd test-results))))

(define (failing-tests path functions sub-ns test-thunks)
  (let [(r (swap-and-run-tests path functions sub-ns test-thunks))]
    (if (false? r)
        r
        (filter (lambda (t) (not (equal? t #t))) r))))

(module+ test
  (require rackunit)
  (define test-path
    (make-temporary-file "examplartmp~a.rkt" #:copy-from "test/submission.rkt"))
  ; force BSL/ISL/ISL+ to be ASL
  (parameterize [(current-module-name-resolver my-resolver)]
    (namespace-require test-path)
    (define test-ns (module->namespace test-path))
    (define test-tests (test-object-tests (current-test-object)))
    (check-equal? (failing-tests "test/wheats/wheat1.rkt" '(F) test-ns test-tests) '())
    (check-equal? (length (failing-tests "test/wheats/wheat1.rkt" '(I) test-ns test-tests)) 2)
    (check-equal? (length (failing-tests "test/wheats/wheat1.rkt" '(F I) test-ns test-tests)) 2)
    (check-equal? (failing-tests "test/chaffs/identity.rkt" '() test-ns test-tests) '())
    (check-equal? (length (failing-tests "test/chaffs/identity.rkt" '(F) test-ns test-tests)) 3)
    (check-equal? (length (failing-tests "test/chaffs/identity.rkt" '(I) test-ns test-tests)) 3)
    (check-equal? (length (failing-tests "test/chaffs/identity.rkt" '(F I) test-ns test-tests)) 6)
    (check-equal? (length (failing-tests "test/chaffs-F/zero-identity.rkt" '(F) test-ns test-tests)) 2)
    (check-equal? (failing-tests "test/chaffs-F/zero-identity.rkt" '(I) test-ns test-tests) #f)
    (check-equal? (length (failing-tests "test/chaffs-I/empty-str.rkt" '(I) test-ns test-tests)) 2))

  (delete-file test-path))


(struct pair [fst snd] #:transparent)

(struct self [tests-run tests-failed] #:transparent)
(struct reference [tests-run tests-failed] #:transparent)
(struct correctness [wheat-all wheat-failing] #:transparent)
(struct thoroughness [chaff-all chaff-accepted] #:transparent)
(struct precision [map] #:transparent)
(struct usefulness [map] #:transparent)

(struct result [self reference wheat chaff precision usefulness] #:transparent)

(struct chaff [name recognizers] #:transparent)
(struct testinfo [srcloc detected] #:transparent)

(define (run-examplar! submission-path-orig reference-path-orig functions)
  ;; For two reasons, we will copy the submission / reference files into new temporary files:
  ;; 1. namespace-require/dynamic-require/anything-i've-found will not instantiate/load
  ;;    a module _twice_, which means that test-engine tests will not be registered
  ;;    if the module has ever been required before. This is very bad, since
  ;;    we want to be able to call `run-examplar!` once _per_ function, rather
  ;;    than once _per_ file.
  ;; 2. If, for some reason, a file has already been compiled _outside_ of our
  ;;    resolver hackery, our interposition will not work. I don't expect this
  ;;    to occur outside of debugging contexts, but I'd rather not mess with it:
  ;;    if the file has never been seen by Racket before, it cannot have already been
  ;;    compiled.
  ;;
  ;; Note that currently, we are _not_ doing this for wheats/chaffs, as:
  ;; - We do not use test-engine in them
  ;; - We only ever _extract_ definitions from them, so we don't actually need to
  ;;   change the language (and, indeed, they could be written in, e.g. #lang racket)

  (define submission-path (make-temporary-file "examplartmp~a.rkt" #:copy-from submission-path-orig))
  (define reference-path (make-temporary-file "examplartmp~a.rkt" #:copy-from reference-path-orig))

  ; force BSL/ISL/ISL+ to be ASL
  (parameterize [(current-module-name-resolver my-resolver)]

    ;; test-engine stores tests, which get registered on module load,
    ;; in a (private) global variable, so we have to do a little bit
    ;; of manipulation to get what we want.

    ;; First, we'll get the reference tests
    (initialize-test-object!)
    (namespace-require reference-path)
    (define reference-tests (test-object-tests (current-test-object)))

    ;; Now, we'll get the submission tests
    (initialize-test-object!)
    (namespace-require submission-path)
    (define submission-tests (test-object-tests (current-test-object)))

    ;; Finally, we'll reset the test-engine tests. When we want
    ;; to run specific tests, we'll have to set them again using `add-test!`.
    (initialize-test-object!)


    (define sub-ns (module->namespace submission-path))

    ;; First task: run their own tests on their own code! Self-consistency is important,
    ;; though it is not everything: it may be that you couldn't figure out how to get
    ;; a given test to pass, and we don't want to encourage deleting tests.
    ;;
    ;; This would seem to be easy: just run the submission-tests. The problem is that not
    ;; all of those are relevant to the given functions... So we end up having to play
    ;; interposition hackery.
    ;;
    ;; First, we tag all of the functions in question so that they, when running, first
    ;; flip a flag.
    (define ran-fn (box #f))
    (parameterize [(current-namespace sub-ns)]
      (for ([fn-sym functions])
        (let* [(fun (eval `(,#'first-order->higher-order
                            ,(namespace-symbol->identifier fn-sym)) sub-ns))
               (fun-flagging (impersonate-procedure fun (lambda args (begin (set-box! ran-fn #t) (apply values args)))))]
          (parameterize [(current-namespace sub-ns)]
            (namespace-set-variable-value! fn-sym fun-flagging #t)))))

    (define self-tests
      (run-flagged-tests ran-fn submission-tests))

    (define self-result
      (self (map pair-fst self-tests)
            (map pair-snd (filter (lambda (p) (not (equal? (pair-snd p) #t))) self-tests))))
    
    ;; Now we reset what test-engine knows about.
    (initialize-test-object!)



    ;; Next, we run their solution against our reference test suite

    ;; TODO: refactor this, as its copy-paste from `failing-tests` above.
    ;; To do this, we put their functions into our reference modules
    (define ref-ns (module->namespace reference-path))
    (define old-fns (map (lambda (f) (cons f
                                           (eval `(,#'first-order->higher-order
                                                   ,(namespace-symbol->identifier f)) ref-ns)))
                         functions))

    (parameterize [(current-namespace sub-ns)]
      (for ([fn-sym functions])
        (let [(fun (eval `(,#'first-order->higher-order
                           ,(namespace-symbol->identifier fn-sym)) sub-ns))]
          (parameterize [(current-namespace ref-ns)]
            (namespace-set-variable-value! fn-sym fun #t)))))
    ;; Now run our tests
    (initialize-test-object!)
    (for-each (lambda (thnk) (add-test! thnk)) reference-tests)
    (parameterize [(test-silence #t)] (test))

    ;; Reset definitions to what they were originally
    (parameterize [(current-namespace sub-ns)]
      (for ([fn old-fns])
        (namespace-set-variable-value! (car fn) (cdr fn) #t)))

    (define reference-result
      (reference (test-object-tests (current-test-object))
                 (map (lambda (fc)
                        (fail-reason-srcloc (failed-check-reason fc)))
                      (test-object-failed-checks (current-test-object)))))

    ;; Now we reset what test-engine knows about.
    (initialize-test-object!)



    (define WHEATS-PATH (string-append (examplar-dir) (wheats-subdir) "/"))
    (define CHAFFS-PATH (string-append (examplar-dir) (chaffs-subdir) "/"))

    (define WHEATS (filter is-racket-file?
                           (map path->string (directory-list WHEATS-PATH))))
    (define CHAFFS (filter is-racket-file?
                           (map path->string (directory-list CHAFFS-PATH))))

    ;; Wheats are relatively straightforward: we want to
    ;; know how many are accepted, giving as score as such.
    (define wheat-fs (map (lambda (w)
                            (pair w (swap-and-run-tests (string-append WHEATS-PATH w) functions sub-ns submission-tests)))
                          WHEATS))
    (define wheat-correctness
      (correctness (map pair-fst (filter (lambda (p) (not (false? (pair-snd p)))) wheat-fs))
                   (map (lambda (p) (pair (pair-fst p)
                                          (filter (lambda (b) (not (equal? b #t))) (pair-snd p))))
                        (filter
                         ;; a failed wheat either:
                         ;; - has no tests at all
                         ;; - has at least one failing test
                         (lambda (wp) (or (empty? (pair-snd wp))
                                          (not (andmap (lambda (b) (equal? b #t)) (pair-snd wp))))) wheat-fs))))

    ;; Chaffs have three different measures. In order to account for that,
    ;; we first record, for each chaff, a list of tests (by srcloc) that
    ;; detect it.


    ;; This is a mapping from
    ;; detected chaffs to the tests that recognized them
    (define chaff-fs (map (lambda (c)
                            (chaff c (failing-tests (string-append CHAFFS-PATH c) functions sub-ns submission-tests)))
                          CHAFFS))
    (define relevant-chaffs (map chaff-name (filter (lambda (c) (not (false? (chaff-recognizers c)))) chaff-fs)))
    (define chaff-records
      (filter (lambda (cr)
                (and (not (false? (chaff-recognizers cr)))
                     (not (empty? (chaff-recognizers cr)))))
              chaff-fs))

    ;; How many of the chaffs did test miss?
    (define chaff-thoroughness
      (let [(detected (map chaff-name chaff-records))]
        (thoroughness relevant-chaffs
                      (filter (lambda (c) (not (member c detected))) relevant-chaffs))))

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

    (define the-result
      (result
       self-result
       reference-result
       wheat-correctness
       chaff-thoroughness
       chaff-precision
       test-usefulness))

    ;; Clean up temp files
    (delete-file submission-path)
    (delete-file reference-path)

    the-result))

(module+ test
  (require rackunit)
  (define er (parameterize [(examplar-dir "test/")]
               (run-examplar! "test/submission.rkt" "test/reference.rkt" '(F I))))

  (check-equal? (length (self-tests-failed (result-self er))) 0)

  (check-equal? (length (reference-tests-failed (result-reference er))) 2)

  (check-equal?
   (map pair-fst
    (correctness-wheat-failing
     (result-wheat er)))
   '("wheat1.rkt"))

  (check-equal?
   (map
    length
    (map pair-snd
         (correctness-wheat-failing
          (result-wheat er))))
   '(2))
  (check-equal?
   (result-chaff er)
   (thoroughness '("empty.rkt" "empty2.rkt" "identity.rkt" "subtle.rkt")
                 '("subtle.rkt")))
  (check-equal?
   (map pair-fst (precision-map (result-precision er)))
   '(("empty.rkt" "empty2.rkt") ("identity.rkt")))
  (check-equal?
   (map pair-snd (usefulness-map (result-usefulness er)))
   '(("empty.rkt" "empty2.rkt" "identity.rkt")
     ("empty.rkt" "empty2.rkt")
     ("identity.rkt")))

  ;; in this test, we have a chaff with _no_ implementation for the I function;
  ;; we want this to work fine!
  (define er1 (parameterize [(examplar-dir "test/")
                             (chaffs-subdir "chaffs-F")]
                (run-examplar! "test/submission.rkt" "test/reference.rkt" '(I))))

  ;; wheat is unchanged
  (check-equal? (map length (map pair-snd (correctness-wheat-failing (result-wheat er1))))
                '(2))
  ;; for chaffs, there are none that have an I implementation, so none we need to detect
  (check-equal? (result-chaff er1) (thoroughness '() '()))

  )


;; What follows is code to run / format the results for gradescope. Obviously, no requirement
;; to use it! Currently, it is _ignoring_ the last two chaff measures, as giving actionable
;; feedback from that will require more work.

(struct point-allocation [pth fn self ref wht chf] #:transparent)

(define (self-calc pa r)
  (if (empty? (self-tests-run r))
      0
      (* (point-allocation-self pa)
         (/ (- (length (self-tests-run r))
               (length (self-tests-failed r)))
            (length (self-tests-run r))))))

(define (self-results pa r)
  `#hasheq((score . ,(exact->inexact (self-calc pa r)))
           (max_score . ,(point-allocation-self pa))
           (name . ,(string-append "'" (symbol->string (point-allocation-fn pa)) "' on own tests"))
           (output . ,(string-append "'" (symbol->string (point-allocation-fn pa)) "' passed "
                                     (number->string (- (length (self-tests-run r))
                                                        (length (self-tests-failed r))))
                                     "/"
                                     (number->string (length (self-tests-run r)))
                                     " of its own tests."))))


(define (reference-calc pa r)
  (if (empty? (reference-tests-run r))
      0
      (* (point-allocation-ref pa)
         (/ (- (length (reference-tests-run r))
               (length (reference-tests-failed r)))
            (length (reference-tests-run r))))))

(define (reference-results pa r)
  `#hasheq((score . ,(exact->inexact (reference-calc pa r)))
           (max_score . ,(point-allocation-ref pa))
           (name . ,(string-append "'" (symbol->string (point-allocation-fn pa)) "' on reference tests"))
           (output . ,(string-append "'" (symbol->string (point-allocation-fn pa)) "' implementation passed "
                                     (number->string (- (length (reference-tests-run r))
                                                        (length (reference-tests-failed r))))
                                     "/"
                                     (number->string (length (reference-tests-run r)))
                                     " reference tests."))))

(define (wheat-calc pa w)
  (if (empty? (correctness-wheat-all w))
      0
      (* (point-allocation-wht pa)
         (/ (- (length (correctness-wheat-all w))
               (length (correctness-wheat-failing w)))
            (length (correctness-wheat-all w))))))

(define (wheat-results pa w)
  `#hasheq((score . ,(exact->inexact (wheat-calc pa w)))
           (max_score . ,(point-allocation-wht pa))
           (name . ,(string-append "'" (symbol->string (point-allocation-fn pa)) "' tests validated on known good implementations"))
           (output . ,(string-append "'" (symbol->string (point-allocation-fn pa)) "' tests passed against "
                                     (number->string (- (length (correctness-wheat-all w))
                                                        (length (correctness-wheat-failing w))))
                                     "/"
                                     (number->string (length (correctness-wheat-all w)))
                                     " known good implementations."
                                     ))))


(define (chaff-calc pa c)
  (if (empty? (thoroughness-chaff-all c))
      0
      (* (point-allocation-chf pa)
         (/ (- (length (thoroughness-chaff-all c))
               (length (thoroughness-chaff-accepted c)))
            (length (thoroughness-chaff-all c))))))

(define (chaff-results pa c)
  `#hasheq((score . ,(exact->inexact (chaff-calc pa c)))
           (max_score . ,(point-allocation-chf pa))
           (name . ,(string-append "'" (symbol->string (point-allocation-fn pa)) "' tests identifying known bad implementations"))
           (output . ,(string-append "'" (symbol->string (point-allocation-fn pa)) "' tests identified "
                                     (number->string (- (length (thoroughness-chaff-all c))
                                                        (length (thoroughness-chaff-accepted c))))
                                     "/"
                                     (number->string (length (thoroughness-chaff-all c)))
                                     " known buggy implementations."
                                     ))))


(define (function-results pa submission-path)
  (let* ([er (run-examplar! submission-path (point-allocation-pth pa) (list (point-allocation-fn pa)))])
    (begin
      #;(printf "~a: ~a\n" pa er)
         (cons
          (+ (self-calc pa (result-self er))
             (reference-calc pa (result-reference er))
             (wheat-calc pa (result-wheat er))
             (chaff-calc pa (result-chaff er)))
          (list (self-results pa (result-self er))
                (reference-results pa (result-reference er))
                (wheat-results pa (result-wheat er))
                (chaff-results pa (result-chaff er)))))))

(define (run-gradescope assignment submission-path)
  (write-json
   (with-handlers ([exn:fail?
                    (lambda (e)
                      `#hasheq((score . "0")
                               ;; This is perhaps a little bold, as it assumes the error will never
                               ;; arise from _our_ code...
                               (output . ,(string-append "Your program failed to run, giving error: \n"
                                                         (exn-message e)
                                                         "\nIf you believe this to to an issue with the autograding infrastructure, please contact course staff."))))])
     (let* ([rs (map (lambda (pa) (function-results pa submission-path)) assignment)]
            [total-points (apply + (map car rs))]
            [score-str (number->string (exact->inexact total-points))])
       `#hasheq((score . ,score-str)
                (tests . ,(apply append (map cdr rs))))))))
