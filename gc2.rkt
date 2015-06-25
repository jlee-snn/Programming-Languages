#lang plai/gc2/collector

; Joseph lee
; EECS 321 Programming Languages
; Homework 6

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;Honor Code
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define eight-principles
  (list
   "Know your rights."
   "Acknowledge your sources."
   "Protect your work."
   "Avoid suspicion."
   "Do your own work."
   "Never falsify a record or permit another person to do so."
   "Never fabricate data, citations, or experimental results."
   "Always tell the truth when discussing your work with your instructor."))


; init-allocator
(define (init-allocator)
  (heap-set! 0 2) 
  (heap-set! 1 'left) 
  ;(heap-set! 2 'null)
  ;(heap-set! 3 'null)
  (for ([ii (in-range 2 (heap-size))])
    (heap-set! ii 'free)))


;helper functions
(define (mid2) ; 4 state
  (+ 4 (round (* (- (heap-size) 4) 1/2))))

(define (mid2state)  ; 2 state
  (+ 1 (round (* (heap-size) 1/2))))

(define (end) ;last state
  (heap-size))

;; gc:deref : location? -> void?
;; lecture 12 notes
(define (gc:deref loc)
  (cond
    [(equal? (heap-ref loc) 'flat)
     (heap-ref (+ loc 1))]
    [else (error 'gc:deref
            "attempted to deref a non flat value, loc ~s"
            loc)]))

;; find-addr : loc -> loc
;; keep track of loc
(define (find-addr loc)
  (case (heap-ref loc)
    [(frwd) (heap-ref (+ loc 1))]
    [(flat pair proc) loc]
    [else (error 'find-addr 
           "unknown tag : ~a" 
           loc)]))

;; gc:alloc-flat : heap-value -> loc
;; lecture 12 notes
(define (gc:alloc-flat fv)
  (define ptr (alloc 2 #f #f))
  (heap-set! ptr 'flat)
  (heap-set! (+ ptr 1) fv)
  ptr)

;; gc:cons : root root -> loc
(define (gc:cons hd tl)
  (define ptr (alloc 3 hd tl))
  (heap-set! ptr 'pair)
  (heap-set! (+ ptr 1) (find-addr hd))
  (heap-set! (+ ptr 2) (find-addr tl))
  (when (or (switch-from-space? hd)
            (switch-from-space? tl))
    (free-from-space))
  ptr)


;; gc:first : location? -> location?
(define (gc:first pr-ptr)
  (if (equal? (heap-ref pr-ptr) 'pair)
      (heap-ref (+ pr-ptr 1))
      (error 'first "non pair" pr-ptr)))

;; gc:rest : loc -> loc
(define (gc:rest pr-ptr)
  (if (equal? (heap-ref pr-ptr) 'pair)
      (heap-ref (+ pr-ptr 2))
      (error 'rest "non pair" pr-ptr)))

;; gc:flat? : loc -> boolean
(define (gc:flat? loc)
  (case (heap-ref loc)
    [(frwd) (gc:flat? (heap-ref (+ loc 1)))]
    [(flat) #t]
    [else #f]))

;; gc:cons? : location? -> boolean?
(define (gc:cons? loc)
  (case (heap-ref loc)
    [(frwd) (gc:cons? (heap-ref (+ loc 1)))]
    [(pair) #t]
    [else #f]))

;; gc:set-first! : location? location? -> void?
(define (gc:set-first! pr-ptr new)
  (if (equal? (heap-ref pr-ptr) 'pair)
      (heap-set! (+ pr-ptr 1) new)
      (error 'set-first! "non pair")))

;; gc:set-rest! : location? location? -> void?
(define (gc:set-rest! pr-ptr new) 
  (if (equal? (heap-ref pr-ptr) 'pair)
      (heap-set! (+ pr-ptr 2) new)
      (error 'set-rest! "non pair")))

;; gc:closure : heap-value (listof loc) -> loc
(define (gc:closure code-ptr fvs)
  (define number-fvs (length fvs))
  (define next (alloc (+ number-fvs 3)
                      fvs
                      (get-root-set)))
  (heap-set! next 'proc)
  (heap-set! (+ next 1) code-ptr)
  (heap-set! (+ next 2) number-fvs)
  (for ([x (in-range 0 number-fvs)])
    (heap-set! (+ next 3 x)
               (read-root (list-ref fvs x))))
  next)


;; gc:closure-code-ptr : loc -> heap-value
(define (gc:closure-code-ptr loc)
  (if (gc:closure? loc)
      (heap-ref (+ (find-addr loc) 1))
   (error 'gc:closure-code "non closure @ ~a, got ~s"
             loc (heap-ref loc))) )

;; gc:closure-env-ref : loc number -> loc
(define (gc:closure-env-ref loc i)
  (if (gc:closure? loc)
      (heap-ref (+ (find-addr loc) 3 i))
      (error 'gc:closure-env-ref "non-closure : ~a" loc)))

;; gc:closure? : loc -> boolean
(define (gc:closure? loc)
  (case (heap-ref loc)
    [(frwd) (gc:closure? (heap-ref (+ loc 1)))]
    [(proc) #t]
    [else #f]))


;a roots is either:
;   - root
;   - loc
;   - (listof roots)

;; alloc : number[size] roots roots -> loc
(define (alloc n some-roots some-more-roots)
  (let([ addr (heap-ref 0)])
  (cond [(<= (+ addr n) (heap-max-limit))(heap-set! 0 (+ addr n)) addr]
        [else
         (collect-garbage some-roots some-more-roots)
         (define next (heap-ref 0))
         (unless (<= (+ next n) (heap-max-limit))
           (error 'alloc "out of space"))
         (heap-set! 0 (+ next n))
         (unless (or (switch-from-space? some-roots)
                     (switch-from-space? some-more-roots))
           (free-from-space))
         next])))

;; collect-garbage : roots roots -> void
(define (collect-garbage some-roots some-more-roots)
  (switch-active-space)
  (rforward (get-root-set))
  (rforward some-roots)
  (rforward some-more-roots))

;; heap-max-limit -> integer 
;; find limit of current semi-heap
(define (heap-max-limit)
  (if (equal? (heap-ref 1) 'left) (mid2state) (heap-size)))

;; two-space-init
(define (two-space-init)
  (if (equal? (heap-ref 1) 'left) 2 (mid2state)))

;; switch-active-space -> void
(define (switch-active-space)
  (case (heap-ref 1)
    [(left)
     (heap-set! 1 'right)
     (heap-set! 0 (mid2state))]
    [(right)
     (heap-set! 1 'left)
     (heap-set! 0 2)]))

;; rforward : loc/(listof loc) -> loc
(define (rforward thing)
  (cond
    [(pair? thing)
     (for-each rforward thing)]
    [(root? thing)
     (define new-addr (qforward (read-root thing)))
     (set-root! thing new-addr)
     (forward/ref new-addr)]
    [(number? thing)
     (define new-addr (qforward thing))
     (forward/ref new-addr)]))

;; qforward : loc -> loc
(define (qforward loc)
  (cond
    [(switch-to-space loc) loc]
    [else
      (case (heap-ref loc)
        [(flat) (define new-addr (gc/alloc 2))
                (heap-set! new-addr 'flat)
                (heap-set! (+ new-addr 1) (heap-ref (+ loc 1))) 
                (heap-set! loc 'frwd)
                (heap-set! (+ loc 1) new-addr)
                new-addr]
        [(pair) (define new-addr (gc/alloc 3))
                (heap-set! new-addr 'pair)
                (heap-set! (+ new-addr 1) (find-addr (heap-ref (+ loc 1))))
                (heap-set! (+ new-addr 2) (find-addr (heap-ref (+ loc 2))))
                (heap-set! loc 'frwd)
                (heap-set! (+ loc 1) new-addr)
                new-addr]
        [(proc) (define length (+ 3 (heap-ref (+ loc 2))))
                (define new-addr (gc/alloc length))
                (for ([x (in-range 0 3)])
                     (heap-set! (+ new-addr x) (heap-ref (+ loc x))))
                (for ([x (in-range 3 length)])
                     (heap-set! (+ new-addr x) (find-addr (heap-ref (+ loc x)))))
                (heap-set! loc 'frwd)
                (heap-set! (+ loc 1) new-addr)
                new-addr]
        [(frwd) (heap-ref (+ loc 1))]
        [else (error 'qforward "wrong tag at ~a" loc)])]))

;; gc/alloc : num[size] -> loc
(define (gc/alloc n)
  (define addr (heap-ref 0))
  (unless (<= (+ addr n) (heap-max-limit))
    (error 'gc/alloc "no space"))
  (heap-set! 0 (+ addr n))
  addr)

;; forward/ref : loc -> loc
(define (forward/ref loc)
  (case (heap-ref loc)
    [(flat) (void)]
    [(pair) (gc:set-first! loc (qforward (heap-ref (+ loc 1))))
            (gc:set-rest! loc (qforward (heap-ref (+ loc 2))))
            (forward/ref (heap-ref (+ loc 1)))
            (forward/ref (heap-ref (+ loc 2)))]
    [(proc) (define fv-count (heap-ref (+ loc 2)))
            (for ([x (in-range 0 fv-count)])
                 (define l (+ loc 3 x))
                 (heap-set! l (qforward (heap-ref l)))
                 (forward/ref (heap-ref l)))]
    [else (error 'forward/ref "wrong tag at ~a" loc)]))

;; free the from space 
;; after moved all live objects and their offsprings 
;; over to space
(define (free-from-space)
  (case (heap-ref 1)
    [(left)
     (for ([i (in-range (mid2state) (heap-size))])
       (heap-set! i 'free))]
    [(right)
     (for ([i (in-range 2 (mid2state))])
       (heap-set! i 'free))]))

(define (switch-to-space loc)
  (case (heap-ref 1)
    [(left) (and (>= loc 2)
                 (< loc (mid2state)))]
    [(right) (and (>= loc (mid2state))
                  (< loc (heap-size)))]))

(define (switch-from-space? thing)
  (cond
    [(list? thing)
     (ormap switch-from-space? thing)]
    [(root? thing)
     (not (switch-to-space (read-root thing)))]
    [(number? thing)
     (not (switch-to-space thing))]
    [(not thing)
     thing]))




;;;;;;;;;;;;;;;;;;;
;;Test cases
;;;;;;;;;;;;;;;;;;;

(print-only-errors #t)

(define hw-heap1 (make-vector 10 'f))
(define hw-heap2 (make-vector 20 'f))
(define hw-heap3 (make-vector 12 'f))
(define hw-heap4 (make-vector 15 'f))

(test (with-heap hw-heap1
                 (init-allocator)
                 (gc:alloc-flat 0)
                 (alloc 1 #f #f))
      4)

(test/exn (with-heap hw-heap1
                 (init-allocator)
                 (gc:alloc-flat 0)
                 (alloc 8 #f #f))
      "out of space")


;init allocator
(test (with-heap hw-heap4
                 (init-allocator)
                 (gc:alloc-flat 0)
                 (gc:alloc-flat 0)
                 (alloc 3 #f #f))
6)
(test (with-heap hw-heap4       
                 (init-allocator)
                 (gc:alloc-flat 0)
                 (gc:alloc-flat 0)
                 (alloc 1 #f #f)
                 hw-heap4)
      (vector 7 'left 'flat 0 'flat 0 'free 'free 'free 'free 'free 'free 'free 'free 'free))


;;alloc 
(test (with-heap hw-heap3
                 (init-allocator)
                 (gc:alloc-flat 0)
                 (alloc 1 #f #f)
                 hw-heap3)
      (vector 5 'left 'flat 0
              'free 'free 'free 'free 'free 'free 'free 'free))



;foward
(test (with-heap hw-heap3
                 (init-allocator)
                 (gc:alloc-flat 0)
                 (switch-active-space)
                 (qforward 2)
                 hw-heap3)
      (vector 9 'right 'frwd 7 
              'free 'free 'free 
              'flat 
              0 'free 'free 'free
              ))

; garbage collect
(test (with-heap hw-heap3
                 (init-allocator)
                 (gc:alloc-flat 0)
                 (gc:alloc-flat 0)
                 (collect-garbage 2 2)
                 hw-heap3)
      (vector 9 'right 'frwd 7
              'flat 0 'free 'flat
              0 'free 'free 'free))

;closure
(test (with-heap hw-heap4
                 (init-allocator)
                 (gc:alloc-flat 0)
                 (gc:closure 'f (list))
                 hw-heap4)
      (vector 7 'left 'flat 0 'proc 'f 0 'free 'free 'free 'free 'free 'free 'free 'free))


;cons

(test/exn (with-heap hw-heap3
                 (init-allocator)
                 (gc:alloc-flat 0)
                 (gc:alloc-flat 1)
                 (gc:cons 2 4))
          "out of space")

(test (with-heap hw-heap3
                 (init-allocator)
                 (gc:alloc-flat 0)
                 (gc:cons 4 4)
                 hw-heap3)
      (vector 7 'left 'flat 0
              'pair 4 4 'free
              'free 'free 'free 'free))

(test/exn (with-heap hw-heap3
                 (init-allocator)
                 (gc:alloc-flat 0)
                 (gc:alloc-flat 1)
                 (gc:cons 2 4))
          "out of space")

(define test-heap3 (make-vector 14 'f))
(test (with-heap test-heap3
                 (init-allocator)
                 (gc:alloc-flat 0)
                 (gc:alloc-flat 0)
                 (gc:closure 'f (list))
                 (gc:alloc-flat 0)
                 test-heap3)
      (vector 13 'right 'free 'free
              'free 'free 'free 'free
              'proc 'f 0 'flat
              0 'free))
;forward
(test (with-heap hw-heap3
                 (init-allocator)
                 (gc:alloc-flat 0)
                 (switch-active-space)
                 (qforward 2)
                 (qforward 11)
                 hw-heap3)
      (vector 9 'right 'frwd 7 
              'free 'free 'free 'flat 
              0 'free 'free 'free
              ))

