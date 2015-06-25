#lang plai

; Joseph lee
; EECS 321 Programming Languages
; Homework 3

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Part O: Honor Code
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

(print-only-errors)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;Part 1: Multiple Arguments
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;  <FunDef> = {deffun {<id> <id>*} <FnWAE>}
(define-type FunDef
  [fundef (name symbol?)
          (arg-names list?)
          (body FnWAE?)])


;  <FnWAE> = <number>
;          | {+ <FnWAE> <FnWAE>}
;          | {- <FnWAE> <FnWAE>}
;          | {with {<id> <FnWAE>} <FnWAE>}
;          | <id>
;          | {<id> <FnWAE>*}

(define-type FnWAE
  [num (n number?)]
  [add (lhs FnWAE?)(rhs FnWAE?)]
  [sub (lhs FnWAE?)(rhs FnWAE?)]
  [with (name symbol?)(named-expr FnWAE?)(body FnWAE?)]
  [id (name symbol?)]
  [app (fun-name symbol?) (arg (listof FnWAE?))])


;  <a-FnWAE> = <number>
(define-type a-FnWAE
  [num-val (n number?)])

;  <id-key> = <none> <Fxn>
(define-type id-key 
  [none] 
  [symF (sym (lambda (x) true))])


;;;;;;;;;;;;
;Parser
;;;;;;;;;;;;

;; parse: expr -> FnWAE
;; returns FnWAE structure from expression
(define (parse expr)
  (cond
    [(number? expr) (num expr)]
    [(symbol? expr) (id expr)]
    [(pair? expr)
     (case (car expr)
       [(+) (add (parse (cadr expr))(parse (caddr expr)))]
       [(-) (sub (parse (cadr expr))(parse (caddr expr)))]
       [(with) (with (car (cadr expr))(parse (cadr (cadr expr)))(parse (caddr expr)))]
       [(deffun) (parse-defn expr)]
       [else (app (car expr) (map parse (cdr expr)))]
       )]
    [else (error "unexpected token")]
    ))

;; parse-defn : expr -> FunDef
;; returns function definition from passed expression expr
(define (parse-defn expr)
  (cond
    [(pair? expr)
     (case (car expr)
       [(deffun) (fundef (car (cadr expr)) 
                         (uniquify-length? (cdr (cadr expr)) "bad syntax")
                         (parse (caddr expr)))]
       )]
    [else (error "unexpected token")]))

;;;;;;;;;;;;;;;
;Extra/Utility
;;;;;;;;;;;;;;;
; uniquify-length?: lst str -> lst
; returns a passed string, str, message if lengths of original and uniquified list are not equal. 
(define (uniquify-length? lst str)
  (cond [(equal? (length lst) (length (remove-duplicates lst symbol=?))) lst]
        [else (error str)]))

; lookup-fundef : sym list-of-FunDef -> FunDef
(define (lookup-fundef fname lst)
  (index-lookup
   (is-symbol? lst fname) lst 
   (undeff fname)))

; undeff : sybol -> string
; appends the name of undefined function symbol
(define (undeff name)
  (let ([err (symbol->string name)])
  (string-append "undefined function: " err)))

(test (undeff 'test) "undefined function: test")

; is-symbol? : list name -> boolean
; checks if name if in list
(define (is-symbol? lst fname)
  (lambda (x) (symbol=? (fundef-name x) fname)))
  
; subst : FnWAE sym a-FnWAE -> FnWAE
; substitutes symbol with val
(define (subst expr sub-id datum)
  (type-case FnWAE expr
    [num (n) expr]
    [add (lhs rhs) (add (subst lhs sub-id datum)(subst rhs sub-id datum))]
    [sub (lhs rhs) (sub (subst lhs sub-id datum)(subst rhs sub-id datum))]
    [with (bound-id named-expr body-expr)
          (with bound-id 
                (subst named-expr sub-id datum)
                (cond[(symbol=? bound-id sub-id) body-expr]
                     [else (subst body-expr sub-id datum)]))]
    [id (name) (cond [(symbol=? name sub-id) (a-FnWAE->FnWAE datum)]
                     [else expr])]
    [app (name arg-exprs)
         (app name (map (lambda (i) (subst i sub-id datum)) arg-exprs))]))

;; subst-parallel: FnWAE list-of-sym list-of-a-FnWAE -> FnWAE
;; substitutes id in sub-ids to corresponding vals
(define (subst-parallel expr sub-ids vals)
  (cond [(empty? sub-ids) expr]
        [else (subst-parallel (subst expr (car sub-ids)(car vals)) 
                      (cdr sub-ids) (cdr vals))]))

;; a-FnWAE->FnWAE : a-FnWAE -> FnWAE
;; changes a-FnWAE into FnWAE
(define (a-FnWAE->FnWAE a-wae)
  (type-case a-FnWAE a-wae
    [num-val (n) (num n)]))
  
; add-with : val val -> val
; returns sum of val, else error message
(define (add-with lhs rhs) 
    (if (and (num-val? lhs)(num-val? rhs))
      (num-val (+ (num-val-n lhs) (num-val-n rhs)))
      (error "invalid arithmetic use")))


; sub-with : val val -> val
; returns sum of val, else error message
(define (sub-with lhs rhs) 
  (if (and (num-val? lhs)(num-val? rhs))
      (num-val (- (num-val-n lhs) (num-val-n rhs)))
      (error "invalid arithmetic use")))

; find-id : symbol list -> list-of-symbols
; returns specified symbols as list
(define (find-id s1 lst)
  (cond [(empty? lst) (none)]
        [(s1 (car lst)) (symF (car lst))]
        [else (find-id s1 (cdr lst))]))

; index-lookup
; checks the symbol of interest to see if contained
; in id-key, otherwise prints an error message
(define (index-lookup s lst error-string)
  (type-case id-key (find-id s lst) 
    [none () (error error-string)]
    [symF (sym) sym]))


;;;;;;;;;;;;;;;;;
; Interpretor
;;;;;;;;;;;;;;;;;

; interp : FnWAE list-of-FunDef -> interp-helper
; returns num-wal if a-FnWAE, else passes to interp-helper
; essentially acts as wrapper
(define (interp a-wae fundefs)
  (type-case a-FnWAE (interp-helper a-wae fundefs)
    [num-val (n) n]))

; interp-helper : interp -> a-FnWAE
; interpret FnWAE for multiple arugments
(define (interp-helper expr fun-defs)
  (type-case FnWAE expr 
    [num (n) (num-val n)]
    [add (lhs rhs) (add-with (interp-helper lhs fun-defs) (interp-helper rhs fun-defs))]
    [sub (lhs rhs) (sub-with (interp-helper lhs fun-defs) (interp-helper rhs fun-defs))]
    [with (bound-id named-expr body-expr)
          (interp-helper (subst body-expr bound-id (interp-helper named-expr fun-defs)) fun-defs)]
    [id (name) (error 'interp-helper "free identifier")]
    [app (fname arg-exprs)
         (interp-arity arg-exprs fname fun-defs "wrong arity")]))

; interp-arity: FnWae -> error
; checks for wrong arity and returns error-message if wrong arity is valid error
(define (interp-arity arg-exprs fname fun-defs error-message)
  (local [(define fi (lookup-fundef fname fun-defs))]
           (cond[(equal? (length (fundef-arg-names fi))(length arg-exprs))
                 (case (length arg-exprs)
                   [(0) (interp-helper (fundef-body fi) fun-defs)]
                   [else (interp-helper 
                          (subst-parallel (fundef-body fi) 
                                  (fundef-arg-names fi) 
                                  (map (lambda (i) (interp-helper i fun-defs)) arg-exprs))
                          fun-defs)])]
                [else (error error-message)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Test Cases
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; parse test cases
(test (parse 1) (num 1))
(test (parse 0) (num 0))
(test (parse 'x) (id 'x))
(test (parse 'bobob) (id 'bobob))

(test (parse '(+ 1 4)) (add (num 1) (num 4)))
(test (parse '(- 1 4)) (sub (num 1) (num 4)))

(test (parse '(+ 1 (+ 2 3))) (add (num 1) (add (num 2) (num 3))))
(test (parse '(- 1 (- 2 3))) (sub (num 1) (sub (num 2) (num 3))))
(test (parse '(+ 0 (- 2 3))) (add (num 0) (sub (num 2) (num 3))))
(test (parse '(- 0 (+ 2 3))) (sub (num 0) (add (num 2) (num 3))))

(test (parse '(with (x 1) x)) (with 'x (num 1) (id 'x)))
(test (parse '(with (x 1) x)) (with 'x (num 1) (id 'x)))
(test (parse '(with (x 1) y)) (with 'x (num 1) (id 'y)))
(test (parse '(with (x 1) x)) (with 'x (num 1) (id 'x)))

(test (parse '(with (x (+ 1 2)) x)) (with 'x (add (num 1) (num 2)) (id 'x)))
(test (parse '(with (x (- 1 2)) x)) (with 'x (sub (num 1) (num 2)) (id 'x)))

(test (parse '(f x x)) (app 'f (list (id 'x) (id 'x))))
(test (parse '(f x y)) (app 'f (list (id 'x) (id 'y))))
(test (parse '(f x y z)) (app 'f (list (id 'x) (id 'y) (id 'z))))
(test (parse '(f x z z)) (app 'f (list (id 'x) (id 'z) (id 'z))))

(test (parse '(f x y z a)) (app 'f (list (id 'x) (id 'y) (id 'z) (id 'a))))
(test (parse '(f x z z a)) (app 'f (list (id 'x) (id 'z) (id 'z) (id 'a))))

(test (parse '(f 1 1)) (app 'f (list (num 1) (num 1))))
(test (parse '(f x 1)) (app 'f (list (id 'x) (num 1))))
(test (parse '(f 1 x)) (app 'f (list (num 1) (id 'x))))
(test (parse '(f 1 1)) (app 'f (list (num 1) (num 1))))
(test (parse '(f x 1)) (app 'f (list (id 'x) (num 1))))
(test (parse '(f 1 x)) (app 'f (list (num 1) (id 'x))))
(test (parse '(f 1 x)) (app 'f (list (num 1)(id 'x))))
(test (parse '(f x y)) (app 'f (list (id 'x)(id 'y))))
(test (parse '(f 1 y z)) (app 'f (list (num 1)(id 'y)(id 'z))))
(test (parse '(f 1 1 1 a)) (app 'f (list (num 1)(num 1)(num 1)(id 'a))))

; parse-defn test cases
(test (parse-defn '{deffun {f} x}) (fundef 'f '() (id 'x)))
(test (parse-defn '{deffun {f} 1}) (fundef 'f '() (num 1)))
(test (parse-defn '{deffun {f} 0}) (fundef 'f '() (num 0)))

(test (parse-defn '{deffun {f x} x}) (fundef 'f (list 'x) (id 'x)))
(test (parse-defn '{deffun {f x y} {+ x y}})(fundef 'f '(x y) (add (id 'x) (id 'y)))) ; 2 arg
(test (parse-defn '{deffun {f x y} {with {x 1} x}})(fundef 'f '(x y)(with 'x (num 1) (id 'x))))
(test (parse-defn '{deffun {f x y} {f y x}}) (fundef 'f '(x y) (app 'f (list (id 'y) (id 'x)))))
(test (parse-defn '{deffun {f x y z} {f  z y x}})(fundef 'f '(x y z) (app 'f (list (id 'z) (id 'y) (id 'x)))))  ;3 arg
(test (parse-defn '{deffun {f x y z} {f  3 2 1}}) (fundef 'f '(x y z) (app 'f (list (num 3) (num 2) (num 1)))))

(test/exn (parse-defn '(deffun (f x x) (+ x 1))) "bad syntax")
(test/exn (parse-defn '(deffun (f y y) (+ y 1))) "bad syntax")
(test/exn (parse-defn '(deffun (f y x y) (+ y 1))) "bad syntax")


; subst test cases
(test (subst (id 'x) 'x (num-val 1)) (num 1))
(test (subst (id 'y) 'x (num-val 1)) (id 'y))
(test (subst (sub (id 'x) (num 1)) 'y (num-val 1))(sub (id 'x) (num 1)))
(test (subst (add (num 1) (id 'x)) 'x (num-val 1)) (add (num 1) (num 1)))
(test (subst (app 'x (list (num 1))) 'y (num-val 12))(app 'x (list (num 1))))
(test (subst (app 'x (list (id 'y))) 'y (num-val 12))(app 'x (list (num 12))))
(test (subst (app 'y (list (num 1))) 'y (num-val 12)) (app 'y (list (num 1))))
(test (subst (app 'f (list (id 'x) (id 'y))) 'x (num-val 0)) (app 'f (list (num 0) (id 'y))))
(test (subst (with 'y (num 1) (id 'x)) 'x (num-val 1))(with 'y (num 1) (num 1)))
(test (subst (with 'y (id 'x) (id 'y)) 'x (num-val 1))(with 'y (num 1) (id 'y)))
(test (subst (with 'x (id 'y) (id 'x)) 'x (num-val 1))(with 'x (id 'y) (id 'x)))

; subst-parallel test cases
(test (subst-parallel (app 'f (list (id 'x) (id 'y))) (list 'x 'y) (list (num-val 1)(num-val 1)))(app 'f (list (num 1) (num 1))))
(test (subst-parallel (app 'f (list (id 'x) (id 'y))) (list 'y 'x) (list (num-val 1)(num-val 1)))(app 'f (list (num 1) (num 1))))
(test (subst-parallel (app 'f (list (id 'x) (id 'y) (id 'z))) (list 'x 'y 'z) (list (num-val 1)(num-val 1) (num-val 1)))(app 'f (list (num 1) (num 1)(num 1))))
(test (subst-parallel (app 'f (list (id 'y) (id 'y) (id 'x))) (list 'z 'y 'x) (list (num-val 1)(num-val 1) (num-val 1)))(app 'f (list (num 1) (num 1)(num 1))))
(test (subst-parallel (id 'x) (list 'x 'y)(list (num-val 1)(num-val 3)))(num 1))
(test (subst-parallel (id 'y) (list 'x 'y)(list (num-val 1)(num-val 3)))(num 3))
(test (subst-parallel (num 0) (list 'x 'y)(list (num-val 1)(num-val 3)))(num 0))
(test (subst-parallel (add (id 'x)(id 'y)) (list 'x 'y)(list (num-val 1)(num-val 1)))(add (num 1)(num 1)))
(test (subst-parallel (sub (id 'x)(id 'y)) (list 'x 'y)(list (num-val 1)(num-val 1)))(sub (num 1)(num 1)))
(test (subst-parallel (with 'y (id 'x) (id 'y)) (list 'y)(list (num-val 1)))(with 'y (id 'x) (id 'y)))




; lookup-fundef cases

(test/exn (lookup-fundef 'x '()) "undefined function: x")
(test (lookup-fundef 'f (list (fundef 'f (list 'x) (id 'z))))(fundef 'f (list 'x) (id 'z)))
(test (lookup-fundef 'f (list (fundef 'f (list 'x) (num 1))))(fundef 'f (list 'x) (num 1)))
(test (lookup-fundef 'f (list (fundef 'f '() (id 'x))))(fundef 'f '() (id 'x)))
(test (lookup-fundef 'f (list (fundef 'f '() (num 1))))(fundef 'f '() (num 1)))
(test/exn (lookup-fundef 'xx (list (fundef 'f (list 'x) (id 'y)))) "undefined function: xx")
(test/exn (lookup-fundef 'xx (list (fundef 'f (list 'x) (num 0)))) "undefined function: xx")

(test (find-id (lambda (x) (= x 10)) (list 1 2 2 2 5 6 7)) (none))
(test (find-id (lambda (x) (= x 1)) (list 1 2 3 4 5)) (symF 1))

(test (find-id (lambda (x) (equal? x 10)) (list 1 2 2 2 5 6 7)) (none))
(test (find-id (lambda (x) (equal? x 1)) (list 1 2 3 4 5)) (symF 1))

(test (find-id (lambda (x) null) (list 1 2 3 4 5)) (symF 1))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; interpreter tests
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;trivial cases
(test (interp (num 0) empty) 0)
(test (interp (num 1) empty) 1)
(test (interp (num 0) (num 1)) 0)
(test (interp (parse '(+ 1 2)) '(+ 2 3)) 3)
(test (interp (parse '(+ 1 2)) '(+ 2 3 {f 2})) 3)
(test (interp (parse '(- 1 2)) empty) -1)

;intermeddiate
(test (interp (parse '{f 1 1}) (list (parse-defn '{deffun {f x y} {+ x y}})))2)
(test (interp (parse '(with (x (+ 1 1)) (+ x 1))) empty) 3)
(test (interp (parse '(with (x (- 1 1)) (- x 1))) empty) -1)
(test (interp (parse '(with (x (+ 1 1)) (- x 1))) empty) 1)
(test (interp (parse '(with (x (- 1 1)) (+ x 1))) empty) 1)

(test (interp (parse '{+ {f} {f}})(list (parse-defn '{deffun {f} 1}))) 2)
(test (interp (parse '{- {f} {f}})(list (parse-defn '{deffun {f} 1}))) 0)
(test (interp (parse '{+ {f} {f}})(list (parse-defn '{deffun {f} 1}))) 2)
(test (interp (parse '{- {f} {f}})(list (parse-defn '{deffun {f} 1}))) 0)
(test (interp (parse '(f 1))(list (parse-defn '{deffun {f y} {+ y 1}}))) 2)


(test (interp (parse '(f 999))(list (parse-defn '{deffun {f y} {with {y 0} y}}))) 0)
(test (interp (parse '{f 1}) (list (parse-defn '{deffun {f x} {+ x 999}}))) 1000)
(test (interp (parse '{f 1}) (list (parse-defn '{deffun {f x} {- x 999}}))) -998)

(test (interp (parse '{f 1 3}) (list (parse-defn '{deffun {f x y} {+ x y}}))) 4)
(test (interp (parse '{f 1 3}) (list (parse-defn '{deffun {f x y} {+ x x}}))) 2)
(test (interp (parse '{f 1 3}) (list (parse-defn '{deffun {f x y} {+ 0 y}}))) 3)
(test (interp (parse '{f 1 3}) (list (parse-defn '{deffun {f x y} {+ 0 x}}))) 1)
(test (interp (parse '{f 1 2}) (list (parse-defn '{deffun {f x y} {+ x y}}))) 3)
(test (interp (parse '{+ {f} {f}}) (list (parse-defn '{deffun {f} 2}))) 4)


; advanced test cases
(test (interp (parse '{+ {f 1 0} {z 1 2 1}})(list (parse-defn '{deffun {f x y} {- x {+ y y}}})
                                                  (parse-defn '{deffun {z x y z} {+ z {- x {+ y y}}}}))) -1)

(test (interp (parse '{f 1 0})(list (parse-defn '{deffun {f x y} {+ x {+ 1 y}}})  ;picks first match from list of functions
                                    (parse-defn '{deffun {f x y} {+ x {+ 4 y}}})
                                    (parse-defn '{deffun {z x y z} {+ z {- x {+ y y}}}}))) 2)



; error test cases

(test/exn (parse null) "unexpected token")  ; not being tested for this assignment
(test/exn (interp (id 'x) empty) "free identifier")
(test/exn (interp (parse '{with {x {with {y 2} {with {x x} y}}}2})empty) "free identifier")
(test/exn (interp (parse '(f 1)) empty) "undefined function: f")
(test/exn (interp (parse '{f 1})(list (parse-defn '{deffun {f x y} {+ x y}}))) "wrong arity")
(test/exn (interp (parse '{f 1})(list (parse-defn '{deffun {f} {+ 1 0}}))) "wrong arity")
(test/exn (interp (parse '{f 1}) (list (parse-defn '{deffun {f x y} {+ x y}}))) "wrong arity")
(test/exn (interp (parse '{f 1})(list (parse-defn '{deffun {f x y} {+ x 2}}))) "wrong arity")
(test/exn (interp (parse '{f 1}) (list (parse-defn '{deffun {f x y} {- x y}}))) "wrong arity")
(test/exn (interp (parse '{f 1})(list (parse-defn '{deffun {f x y} {- x y}}))) "wrong arity")
(test/exn (interp (parse '{f1 1 56 3 (f2 z)})(list (parse-defn '{deffun {f1 x x} {+ x y}}))) "bad syntax")
(test/exn (interp (parse '{+ {f 3 3}{f 21}})(list (parse-defn '{deffun {f x x} {- x x}})))"bad syntax")











