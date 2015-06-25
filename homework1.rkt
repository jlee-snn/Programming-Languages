#lang plai
(expt 2 100)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Joseph Lee
; EECS 321 Programming Languages
; Homework 1

;;;; 1/5/14 First Edit
;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;
; Part 1: Honor Code
;;;;;;;;;;;;;;;;;;;;

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




; Tree data type
(define-type Tree
    [leaf]
    [node (val number?)
          (left Tree?)
          (right Tree?)])


;defined tree(s) for tests
(define tree1 (node 5 (leaf) (leaf)))
(define tree2 (node 10 (node 5 (node 1 (leaf) (leaf)) (leaf)) (leaf)))
(define tree3 (node 5 (leaf) (leaf)))
(define tree4 (node 5 (node 3 (leaf) (leaf)) (leaf)))
(define tree5 (node 13 (node 4 (node 5 (leaf) (leaf)) (leaf)) (node 2 (leaf) (leaf))))
(define tree6 (node 15 (node 2 (leaf) (leaf)) (node 4 (leaf) (node 6 (leaf) (leaf)))))

;;;;;;;;;;;;;;;;
; Part 2: Trees
;;;;;;;;;;;;;;;;


; smallest : tree -> number
; returns the samllest number that exists in a tree.
; if empty, returns +inf.0

(define (smallest t)
  (type-case Tree t
    [leaf () +inf.0]
    [node (val left right) (min val 
                                (smallest left) 
                                (smallest right))])) 

(test (smallest tree1) 5)
(test (smallest tree2) 1)
(test (smallest tree6) 2)
(test (smallest (leaf)) +inf.0)
  
         
;;;;;;;;;;;;;;;
;Part 3: Negate
;;;;;;;;;;;;;;;

; negate: tree -> -tree
; returns a tree withthe same shape but with negative nodes
(define (negate t)
  (type-case Tree t
    [leaf () t]
    [node (val left right) (node (* -1 val) (negate left) (negate right))])) 
 
(test (negate tree1) (node -5 (leaf) (leaf)))
(test (negate tree4) (node -5 (node -3 (leaf) (leaf)) (leaf)))

;;;;;;;;;;;;;;;;;;
;Part 4: Contains?
;;;;;;;;;;;;;;;;;;


; contains?: tree number -> boolean
; returns true if the tree t does contain number num
(define (contains? t num)
  (type-case Tree t
    [leaf () #f]
    [node (val left right) (or (equal? val num)
                               (contains? left num) 
                               (contains? right num))]))

(test (contains? (node 0 (leaf) (leaf)) 0) #t)
(test (contains? (node 0 (leaf) (leaf)) 1) #f)
(test (contains? tree1 5) #t)
(test (contains? tree1 6) #f)
(test (contains? tree6 4) #t)

;;;;;;;;;;;;;;;;
;Part 5: Sorted?
;;;;;;;;;;;;;;;;

; sorted?: tree ->boolean
; determines if tree is in inorder traversal order
(define (sorted? t)
  (type-case Tree t
    [leaf () #t]
    [node (v l r) (and (sorted? l)
                       (sorted-helper l v r)
                       (sorted? r))]))

; getter-val : tree -> number
; returns the value of the node, an integer. 
(define (getter-val t)
  (type-case Tree t
    [leaf () '()]
    [node (val left right) val]))

(test (getter-val tree1) 5)

; sorted-helper: left-node val-node right-node -> boolean
; returns true if all values meet the boolean conidtions associated with inorder.
(define (sorted-helper lx v rx)
  (let ([l (getter-val lx)]
        [r (getter-val rx)])
    (or 
     (and (equal? l '()) 
          (equal? r '()))
     (and (equal? l '()) 
          (number? r) 
          (<= v r))
     (and (equal? r '()) 
          (number? l) 
          (<= l v))
     (and (number? l) 
          (number? r) 
          (<= l v) 
          (<= v r)))))


(test (sorted? tree5) #f)
(test (sorted? tree3) #t)
(test (sorted? tree6) #f)


;;;;;;;;;;;;;;;;;;
;Part 6: is-braun?
;;;;;;;;;;;;;;;;;;

; is-braun? : tree -> boolean
; Returns the boolean value of the status of the braun.
(define (is-braun? t)
  (type-case Tree t
    [leaf () true]
    [node (val left right) 
           (b-check (is-braun-helper left) 
                    (is-braun-helper right))]))

; is-braun-helper : tree -> boolean
; Returns the boolean value of the status of the braun.
; Acts as a sub processing function.
(define (is-braun-helper t)
  (type-case Tree t
    [leaf () 0]
    [node (val left right) 
            (cond[(b-check (is-braun-helper left) 
                           (is-braun-helper right))
                  (+ 1 (is-braun-helper left) 
                     (is-braun-helper right))]
                 [else #f])]))
;b-check : left right -> boolean
;returns the boolean result if the left and right values meet
; the crtieria to be a braun tree or not.
(define (b-check ls rs)
  (and (number? ls)(number? rs)
       (or (equal? ls rs) (equal? (- ls 1) rs))))

;tests
(test (is-braun? tree1) #t)
(test (is-braun? tree5)  #t)
(test (is-braun? tree6) #f)
(test (is-braun? (leaf)) #t)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;Part 7: Making Braun Trees
;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;make-sorted-braun: number-> sorted braun tree
;returns a braun tree given the number as the acting root.
;primarily acts as a wrapper structure
(define (make-sorted-braun n1)
  (make-sorted-braun-helper (leaf) (decf-fxn n1) 0))



;auxilliary functions
(define (decf-fxn num)
  (- num 1))
(define (incf-fxn num)
  (+ num 1))



; make-sorted-braun-helper
; helper function that decrements increments each 
; node addition.
(define (make-sorted-braun-helper t nnum1 acc)
  (let ([bis-rt (mid-find nnum1 acc)])
    (cond
      [(= nnum1 acc) (node nnum1 t t)]
      [(> nnum1 acc) (node bis-rt 
                  (make-sorted-braun-helper t (decf-fxn bis-rt) acc)
                  (make-sorted-braun-helper t nnum1 (incf-fxn bis-rt)))]
      [else t])))

; mid-find: high low -> midpoint
; returns the rounded middle value between two boundaries.
; rounds to nearest number.
(define (mid-find high low)
    (cond
      [(equal? (mid-calculator high low) 
               (floor (mid-calculator high low))) (mid-calculator high low)]
      [else (floor (+ (/ 1 2) (mid-calculator high low)))]))

;mid-calculator 
;returns mid-point of two numbers
(define (mid-calculator high low)
    (/ (+ high low) 2))


; mid-find tests
(test (mid-find 36 2) 19)
(test (mid-find 100 0) 50)

;;Tests for Braun
(test (make-sorted-braun 0) (leaf))
(test (is-braun? (make-sorted-braun 10)) #t)
(test (is-braun? (make-sorted-braun 20)) #t)
(test (is-braun? (make-sorted-braun 25)) #t)
(test (is-braun? (make-sorted-braun 14)) #t)
(test (sorted? (make-sorted-braun 10)) #t)
(test (sorted? (make-sorted-braun 20)) #t)
(test (sorted? (make-sorted-braun 4)) #t)
(test (= (smallest (make-sorted-braun 10)) 0)#t)
(test (= (smallest (make-sorted-braun 15)) 0)#t)
(test (= (smallest (negate (make-sorted-braun 10))) (- 1 10))  #t)
(test (= (smallest (negate (make-sorted-braun 20))) (- 1 10))  #f)
(test (make-sorted-braun 4)
      (node 2
            (node 1
                  (node 0 (leaf) (leaf))
                  (leaf))
            (node 3 (leaf) (leaf))))

