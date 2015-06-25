#lang plai

; Joseph Lee
; EECS 321
; Homework 2

(print-only-errors)

;; Part 0
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

;;Part 1
(define-type WAE
  [num (n number?)]
  [add (lhs WAE?)
       (rhs WAE?)]
  [sub (lhs WAE?)
       (rhs WAE?)]
  [with (name symbol?)
        (named-expr WAE?)
        (body WAE?)]
  [id (name symbol?)])

;interp
(define/contract (interp a-wae)
  (-> WAE? number?)
  (type-case WAE a-wae
    [num (n) n]
    [add (l r) (+ (interp l) (interp r))]
    [sub (l r) (- (interp l) (interp r))]
    [with (name expr body-expr) (interp
                                 (subst-custom name
                                               (interp expr)
                                               body-expr))]
    [id (name) (error 'interp "free identifier: ~s" name)]))



;;subst
(define/contract (subst-custom a-id a-val a-wae)
  (-> symbol? number? WAE? WAE?)
  (type-case WAE a-wae
    [num (n) a-wae]
    [add (lhs rhs) (add (subst-custom a-id a-val lhs) (subst-custom a-id a-val rhs))]
    [sub (lhs rhs) (sub (subst-custom a-id a-val lhs) (subst-custom a-id a-val rhs))]
    [with (name expr body) (cond[(equal? name a-id)(with name (subst-custom a-id a-val expr) body)]
                                [else (with name (subst-custom a-id a-val expr) (subst-custom a-id a-val body))])]
    [id (name) (cond [(equal? name a-id)(num a-val)]
                     [else a-wae])]))


;; Part 1
; free-ids: wae -> wae
; wrapper for free-ids-helper 
(define (free-ids a-wae) 
  (let ([lst '()])
  (clean-up (free-ids-helper a-wae lst))))

; free-ids-helper: wae -> list-of-free-ids
; returns list of free ids
(define (free-ids-helper a-wae acc)
  (-> symbol? number? WAE? WAE?)
  (type-case WAE a-wae
    [num (n) '()]
    [add (lhs rhs) (append (free-ids-helper lhs acc)
                           (free-ids-helper rhs acc))]
    [sub (lhs rhs) (append (free-ids-helper lhs acc)
                           (free-ids-helper rhs acc))]
    [with (name named-expr body-expr) 
          (append (list (free-ids-helper named-expr acc)) 
                   (list (free-ids-helper body-expr (cons name acc))))]
    [id (name) (cond[(member name acc) '()]
                    [else (list name)])]))


(define (uniquify-helper lst)
  (cond
    [(equal? lst null) null]
    [else (cond
            [(member (car lst) (cdr lst)) (uniquify-helper (cdr lst))]
            [else (cons (car lst) (uniquify-helper (cdr lst)))])]))


(define (uniquify lst)
  (uniquify-helper 
   (sort lst symbol<?)))


(define (compress lst)
  (remove-duplicates (flatten lst) symbol=?))

; clean-up : wae -> list
; returns sorted list
(define (clean-up a-wae)
  (sort(compress a-wae) symbol<?))

;; binding-helper
(define (binding-ids-helper a-wae)
  (type-case WAE a-wae
    [num (n) null]
    [add (lhs rhs) (append (binding-ids-helper lhs) (binding-ids-helper rhs))]
    [sub (lhs rhs) (append (binding-ids-helper lhs) (binding-ids-helper rhs))]
    [with (name expr body) (cons name
                                 (append (binding-ids-helper expr)
                                         (binding-ids-helper (subst-custom name 0 body))))]
    [id (name) null]))


;; binding-ids : WAE -> list-of-sym
(define (binding-ids a-wae)
  (uniquify (binding-ids-helper a-wae)))

;; Part 3
;; is-wae? : symbol WAE -> boolean
(define (is-wae? id-s a-wae)
  (type-case WAE a-wae
    [num (n) false]
    [add (lhs rhs) (or (is-wae? id-s lhs) (is-wae? id-s rhs))]
    [sub (lhs rhs) (or (is-wae? id-s lhs) (is-wae? id-s rhs))]
    [with (name expr body-expr) (or (is-wae? id-s (subst-custom name 0 body-expr))
                               (is-wae? id-s expr))]
    [id (name) (equal? name id-s)]))




;; bound-ids : WAE -> list-of-sym
;; acs as wrapper
(define (bound-ids a-wae)
  (uniquify (bound-ids-sub a-wae)))
     
;; Does most of the work returning bound-id
;; bound-ids-sub : WAE -> list-of-sym
(define (bound-ids-sub a-wae)
  (type-case WAE a-wae
    [num (n) null]
    [add (l r) (append (bound-ids-sub l) (bound-ids-sub r))]
    [sub (l r) (append (bound-ids-sub l) (bound-ids-sub r))]
    [with (name expr body) (cond[(is-wae? name body)(cons name (append (bound-ids-sub expr)(bound-ids-sub (subst-custom name 0 body))))]
                                [else (append (bound-ids-sub expr) (bound-ids-sub (subst-custom name 0 body)))])]
    [id (name) null]))





;; Part 4

;; wae-count? : symbol WAE -> number
(define (wae-count? sym a-wae)
  (type-case WAE a-wae
    [num (n) 0]
    [add (lhs rhs) (+ (wae-count? sym lhs) (wae-count? sym rhs))]
    [sub (lhs rhs) (+ (wae-count? sym lhs) (wae-count? sym rhs))]
    [with (name expr body) (+ (wae-count? sym (subst-custom name 0 body))
                              (wae-count? sym expr))]
    [id (name) (cond [(equal? name sym) 1]
                     [else 0])]))

;; wae-member-check : symbol WAE -> number
(define (wae-member-check sym a-wae)
  (type-case WAE a-wae
    [num (n) 0]
    [add (lhs rhs) (+ (wae-member-check sym lhs) (wae-member-check sym rhs))]
    [sub (lhs rhs) (+ (wae-member-check sym lhs) (wae-member-check sym rhs))]
    [with (name expr body-expr) (+ (wae-member-check sym body-expr)
                                   (wae-member-check sym expr))]
    [id (name) (cond [(equal? name sym) 1]
                     [else 0])]))


(define (is-shadowed? sym a-wae)
  (not (equal? (wae-count? sym a-wae) (wae-member-check sym a-wae))))

;; shadowed-variable? 
(define (shadowed-variable? a-wae)
  (type-case WAE a-wae
    [num (n) #f]
    [add (lhs rhs) (or (shadowed-variable? lhs) (shadowed-variable? rhs))]
    [sub (lhs rhs) (or (shadowed-variable? lhs) (shadowed-variable? rhs))]
    [with (name expr body) (or (is-shadowed? name body)
                               (shadowed-variable? (subst-custom name 0 body))
                               (shadowed-variable? expr))]
    [id (name) #f]))




;;Tests

(test (free-ids (num 11)) '())
(test (free-ids (id 'bob)) (list 'bob))
(test (free-ids (id 'x)) '(x))

; sub
(test (free-ids (sub (num 6) (num 8))) '())
(test (free-ids (sub (num 6) (id 'i))) (list 'i))
(test (free-ids (sub (id 'i) (num 6))) (list 'i))
(test (free-ids (sub (id 'x) (id 'y))) (list 'x 'y))
(test (free-ids (sub (id 'y) (id 'x))) (list 'x 'y))
(test (free-ids (sub (id 'x) (sub (id 'y) (id 'z)))) (list 'x 'y 'z))

; add
(test (free-ids (add (num 6) (num 8))) '())
(test (free-ids (add (num 6) (id 'i))) (list 'i))
(test (free-ids (add (id 'i) (num 6))) (list 'i))
(test (free-ids (add (id 'x) (id 'y))) (list 'x 'y))
(test (free-ids (add (id 'y) (id 'x))) (list 'x 'y))
(test (free-ids (add (id 'x) (sub (id 'y) (id 'z)))) (list 'x 'y 'z))

;extra
(test (free-ids (num 3)) null)
(test (free-ids (add (id 'x) (id 'y))) '(x y))
(test (free-ids (sub (id 'x) (id 'c))) '(c x))
(test (free-ids (with 'x (add (num 5) (num 4)) (add (id 'x) (id 'y)))) '(y))

(test (binding-ids (num 24)) null)
(test (binding-ids (id 'a)) null)
(test (binding-ids (with 'a (num 3) (add (id 'a) (id 'a))))'(a))
(test (binding-ids (with 'a (num 3) (add (id 'b) (id 'b))))'(a))
(test (binding-ids (with 'a (num 3) (sub (id 'a) (id 'a))))'(a))
(test (binding-ids (with 'a (num 3) (sub (id 'b) (id 'b))))'(a))
(test (binding-ids (with 'a (num 3) (with 'b (num 1) (with 'c (num 1) (num 1)))))'(a b c))
(test (binding-ids (with 'c (num 3) (with 'b (num 1) (with 'a (num 1) (num 1)))))'(a b c))
(test (binding-ids (with 'a (num 3) (with 'b (num 0) (with 'b (num 1) (num 1)))))'(a b))
(test (binding-ids (with 'c (num 3) (with 'b (num 3) (with 'c (num 1) (num 1)))))'(b c))
(test (binding-ids (with 'a (num 3) (with 'b (num 0) (with 'b (add (num 1) (num 4)) (num 1)))))'(a b))
(test (binding-ids (with 'a (num 3) (with 'b (num 0) (with 'b (sub (num 1) (num 4)) (num 1)))))'(a b))
(test (binding-ids (with 'c (num 3) (with 'b (num 3) (with 'c (num 1) (num 1)))))'(b c))
(test (binding-ids (with 'a (num 3) (with 'b (num 1) (with 'c (num 50) (sub (id 'x) (id 'b))))))'(a b c))
(test (binding-ids (with 'a (num 3) (with 'b (num 1) (with 'c (num 50) (add (id 'x) (id 'b))))))'(a b c))


; bound-ids

(test (bound-ids (num 0)) '())
(test (bound-ids (with 'a (num 0) (num 0))) '())
(test (bound-ids (with 'a (num 0) (id 'a))) '(a))
(test (bound-ids (with 'a (num 0) (with 'b (num 0) (add (id 'a) (num 0)))))'(a))
(test (bound-ids (with 'b (num 0) (with 'a (num 0) (add (id 'a) (id 'b)))))'(a b))

(test (bound-ids (add (num 4) (num 4)) )'() )
(test (bound-ids (with 'a (sub (num 4) (num 4)) (num 2))) '())
(test (bound-ids (with 'a (sub (num 4) (num 4)) (id 'a))) '(a))
(test (bound-ids (with 'a (sub (num 4) (num 4)) (with 'b (num 2) (add (id 'a) (num 2)))))'(a))
(test (bound-ids (with 'b (sub (num 4) (num 4)) (with 'a (num 2) (add (id 'a) (id 'b)))))'(a b))



; shadowed-variable

(test (bound-ids (with 'x (num 1) (with 'y (id 'x) (id 'y)))) '(x y))

(test (shadowed-variable? (with 'a (num 1) (with 'b (num 1) (with 'a (num 1) (add (id 'a) (id 'b)))))) true)
(test (shadowed-variable? (with 'a (num 1) (with 'b (num 1) (with 'a (num 1) (sub (id 'a) (id 'b)))))) true)
(test (shadowed-variable? (sub (num 0) (num 1))) #f)
(test (shadowed-variable? (add (num 1) (num 0))) #f)
(test (shadowed-variable? (with 'a (num 3) (with 'b (num 3) (with 'c (num 4) (sub (id 'a) (id 'y)))))) #f)
(test (shadowed-variable? (with 'a (num 3) (with 'b (num 3) (with 'c (num 4) (add (id 'a) (id 'y)))))) #f)
(test (shadowed-variable? (with 'a (num 3) (with 'b (num 3) (with 'c (num 4) (sub (id 'a) (num 3)))))) #f)
(test (shadowed-variable? (with 'a (num 3) (with 'b (num 3) (with 'c (num 4) (add (id 'a) (num 3)))))) #f)
(test (shadowed-variable? (with 'a (num 3) (with 'b (num 3) (with 'c (num 4) (sub (id 'a) (num 3)))))) #f)
(test (shadowed-variable? (with 'a (num 3) (with 'b (num 3) (with 'c (num 4) (add (id 'a) (num 3)))))) #f)

(test (shadowed-variable? (num 0)) #f)
(test (shadowed-variable? (id 'x)) #f)
(test (shadowed-variable? (add (num 1) (num 0))) #f)
(test (shadowed-variable?
  (with 'y (with 'x (id 'x) (id 'x)) (with 'y (id 'x) (id 'y)))) #t)

(test (shadowed-variable?
  (add
   (with 'x (num 1) (with 'x (id 'x) (num 1)))
   (with 'x (id 'x) (with 'x (id 'x) (id 'x))))) #t)