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


(define-type WAE
  [num (n number?)]
  [add (lhs WAE?)
       (rhs WAE?)]
  [sub (lhs WAE?)
       (rhs WAE?)]
  [with (name symbol?)
        (named-expr WAE?)
        (body-expr WAE?)]
  [id (name symbol?)])



(define/contract (interp a-wae)
  (-> WAE? number?)
  (type-case WAE a-wae
    [num (n) n]
    [add (l r) (+ (interp l) (interp r))]
    [sub (l r) (- (interp l) (interp r))]
    [with (name named-expr body-expr) (interp
                            (subst-custom name
                                   (interp named-expr)
                                   
                                   body-expr))]
    [id (name) (error 'interp "free identifier: " name)]))





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
          (append  (list (free-ids-helper named-expr acc)) 
                   (list (free-ids-helper body-expr (cons name acc))))]
    [id (name) (if (member name acc) '() (list name))]))

;; Part 2

; binding-ids : wae -> wae
; wrapper that cleans up WAE
(define (binding-ids a-wae)
  (clean-up (binding-ids-helper a-wae)))


; binding-ids-helper : wae -> bindings
; returns list of binding ids
(define (binding-ids-helper a-wae)
  (-> symbol? number? WAE? WAE?)
  (-> WAE? number?)
  (type-case WAE a-wae
    [num (n) '()]
    [add (lhs rhs) (append (binding-ids-helper lhs) (binding-ids-helper rhs))]
    [sub (lhs rhs) (append (binding-ids-helper lhs) (binding-ids-helper rhs))]
    [with (name named-expr body-expr) 
          (append (list name) 
                (list (binding-ids-helper body-expr)
                (binding-ids-helper named-expr)))]
    [id (name) '()]))


;;;;;;;;;;
;; Part 3
;;;;;;;;;;;;





; bound-ids : WAE -> list-of-symbols
; returns sorted and uniquified list of symbols
(define (bound-ids a-wae)
  (clean-up (bound-ids-helper a-wae)))


; bound-ids : WAE -> list-of-symbols
; returns list of bound ids

(define (bound-ids-helper a-wae)
  (-> symbol? number? WAE? WAE?)
  (type-case WAE a-wae
    [num (n) '()]
    [add (lhs rhs) (list (bound-ids-helper lhs) (bound-ids-helper rhs))]
    [sub (lhs rhs) (list (bound-ids-helper lhs) (bound-ids-helper rhs))]
    [with (name named-expr body-expr) (if (wae-descendent? name body-expr)
                               (append (list name) (bound-ids-helper (subst-custom name (interp named-expr) body-expr)))
                               (bound-ids-helper (subst-custom name (interp named-expr) body-expr)))]
    [id (name) '()]))

(test (bound-ids-helper (id 'x)) '())


; compress : list -> list
; returns unique list with no duplicates
(define (compress lst)
  (remove-duplicates (flatten lst) symbol=?))



; clean-up : wae -> list
; returns sorted list
(define (clean-up a-wae)
  (sort(compress a-wae) symbol<?))



; Part 4 

;; customized substitution function from class notes
(define/contract (subst-custom sub-id val a-wae)
  (-> symbol? number? WAE? WAE?)
  (type-case WAE a-wae
    [num (n) a-wae]
    [add (lhs rhs) (add (subst-custom sub-id val lhs) (subst-custom sub-id val rhs))]
    [sub (lhs rhs) (sub (subst-custom sub-id val lhs) (subst-custom sub-id val rhs))]
    [with (name named-expr body-expr) (if (symbol=? name sub-id) 
                                          (with name 
                                                (subst-custom sub-id val named-expr)) 
                                          (with name
                                                (subst-custom sub-id val named-expr)
                                                (subst-custom sub-id val body-expr)))]
    [id (name) (if (symbol=? sub-id  name)
                   (num val)
                   a-wae)]))

; specialized member function
(define (wae-descendent? id-name a-wae)
  (type-case WAE a-wae
    [num (n) #f]
    [add (lhs rhs) (or (wae-descendent?  id-name lhs) (wae-descendent?  id-name rhs))]
    [sub (lhs rhs) (or (wae-descendent?  id-name lhs) (wae-descendent?  id-name rhs))]
    [with (name named-expr body-expr) 
          (wae-descendent? id-name (subst-custom name (interp named-expr) body-expr))]
    [id (name) (equal? name id-name)]))



; Counts number of bindings w/ with
(define (wae-descendent-count? s1 a-wae)
  (let ([count 0])
  (type-case WAE a-wae
    [num (n) 0]
    [add (lhs rhs) (+ (wae-descendent-count? s1 lhs) (wae-descendent-count? s1 rhs))]
    [sub (lhs rhs) (+ (wae-descendent-count? s1 lhs) (wae-descendent-count? s1 rhs))]
    [with (name named-expr body) (wae-descendent-count? s1 (subst-custom name 
                                                                          (interp named-expr) 
                                                                body))]
     [id (name) (if (equal? name s1)
                   (+ count 1)
                   (+ count 0))])))

; Counts number of bindings without with
(define (wae-shadow-count? s2 a-wae)
  (let ([count 0])
  (type-case WAE a-wae
    [num (n) 0]
    [add (lhs rhs) (+ (wae-shadow-count? s2 lhs) (wae-shadow-count? s2 rhs))]
    [sub (lhs rhs) (+ (wae-shadow-count? s2 lhs) (wae-shadow-count? s2 rhs))]
    [with (name named-expr body) (wae-shadow-count? s2 body)]
      [id (name) (if (equal? name s2)
                   (+ count 1)
                   (+ count 0))])))

; is-shadowed? 
; boolean comparision between two counts with with or no with
(define (is-shadowed? s a-wae)
  (let ([s1 (wae-descendent-count? s a-wae)]
        [s2 (wae-shadow-count? s a-wae)])
  (not (equal? s1 s2))))


; shadowed-variable? : a-wae -> boolean
; returns boolean if variable is shadowed
(define (shadowed-variable? a-wae)
  (type-case WAE a-wae
    [num (n) #f]
    [add (lhs rhs) (or (shadowed-variable? lhs) (shadowed-variable? rhs))]
    [sub (lhs rhs) (or (shadowed-variable? lhs) (shadowed-variable? rhs))]
    [with (name named-expr body-expr) 
          (or (is-shadowed? name body-expr)
                                          (shadowed-variable? (subst-custom name (interp named-expr) body-expr)))]
    [id (name) #f]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;Test Cases
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



(test (compress (list 'a 'b 'c 'c 'd 'f 'c 'a)) (list 'a 'b 'c 'd 'f))
(test (clean-up (list 'b 'a 'c 'c 'd 'f 'c 'a)) (list 'a 'b 'c 'd 'f))

; free-ids

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
(test (free-ids (with 'x (add (num 5) (num 4)) (add (id 'x) (id 'x)))) '())


;with
(test (free-ids (with 'x (add (num 6) (num 3)) (sub (id 'x) (id 'y))))'(y))
(test (free-ids (with 'x (add (num 6) (num 3)) (sub (id 'x) (id 'x))))'())
(test (free-ids (with 'x (sub (num 6) (num 3)) (add (id 'x) (id 'y))))'(y))
(test (free-ids (with 'x (sub (num 6) (num 3)) (add (id 'x) (id 'x))))'())


; binding-ids

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

(test (wae-shadow-count? 'a (add (id 'b) (id 'a))) 1)

(test (wae-descendent-count? 'a (add (id 'a) (id 'a))) 2)
(test (wae-descendent-count? 'a (sub (id 'a) (id 'a))) 2)

(test (subst-custom 'a 0 (num 1)) (num 1))
(test (subst-custom 'a 0 (id 'a)) (num 0))
(test (subst-custom 'a 0 (id 'b)) (id 'b))
(test (subst-custom 'a 0 (add (id 'b) (id 'a)))(add (id 'b) (num 0)))

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




