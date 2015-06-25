#lang plai

; Joseph lee
; EECS 321 Programming Languages
; Homework 4

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
  [if0 (x FnWAE?) (y FnWAE?) (z FnWAE?)]
  [app (fun-name symbol?) (arg (listof FnWAE?))])

;  <id-key> = <none> <Fxn>
(define-type id-key 
  [none] 
  [symF (sym (lambda (x) true))])

;  <id-key> = <none> <Fxn>
(define-type PairSymNum 
  [PofSym-Num (name symbol?)(num number?)])



;;;;;;;;;;;;
;Parser
;;;;;;;;;;;;

;; parse: expr -> FnWAE
;; returns FnWAE structure from expression
(define (parse expr)
  (cond
    [(number? expr) (num expr)]
    [(symbol? expr) (id expr)]
    [(list? expr)
     (case (car expr)
       [(+) (add (parse (cadr expr))(parse (caddr expr)))]
       [(-) (sub (parse (cadr expr))(parse (caddr expr)))]
       [(with) (with (car (cadr expr))
                     (parse (cadr (cadr expr)))
                     (parse (caddr expr)))]
       [(if0) (if0 (parse (cadr expr))
                   (parse (caddr expr))
                   (parse (cadddr expr)))]
       
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
     (case (first expr)
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
   (is-symbol? fname) lst 
   (undeff fname)))

; undeff : sybol -> string
; appends the name of undefined function symbol
(define (undeff name)
  (let ([err (symbol->string name)])
  (string-append "undefined function: " err)))

(test (undeff 'test) "undefined function: test")

; is-symbol? : list name -> boolean
; checks if name if in list
(define (is-symbol? fname)
  (lambda (x) (symbol=? (fundef-name x) fname)))
  
; dfs-lookup
; looks up elements of deferred substitution
(define (dfs-lookup name dfsubst)
  (PofSym-Num-num (index-lookup
                   (lambda (x) (symbol=? (PofSym-Num-name x) name)) dfsubst "free variable")))
 

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


; zip-cons 
; returns a compressed list of smaller list types
(define (zip-cons op lhs rhs)
  (cond [(or (empty? lhs) (empty? rhs)) '()]
        [else (cons (op (car lhs) (car rhs))
                    (zip-cons op (cdr lhs) (cdr rhs)))]))


;;;;;;;;;;;;;;;;;
; Interpretor
;;;;;;;;;;;;;;;;;




; interp-expr 
; acts as a wrapper that accepts 2 arguments and passes 3 arguments to interp. 
; contract with FnWAE type
(define (interp-expr expr defs) 
  (-> FnWAE? (listof FunDef?) number?)
  (interp expr defs '()))

; interp
; interpreter for df subst 
(define (interp expr defs dfsubst)
  (type-case FnWAE expr 
    [num (n) n]
    [add (lhs rhs) (+ (interp lhs defs dfsubst) (interp rhs defs dfsubst))]
    [sub (lhs rhs) (- (interp lhs defs dfsubst) (interp rhs defs dfsubst))]
    [with (bound-id named-expr body-expr)
      (interp body-expr defs
              (cons (PofSym-Num bound-id (interp named-expr defs dfsubst)) dfsubst))]
    [id (name) (dfs-lookup name dfsubst)]
    [if0 (x1 x2 x3)
          (cond[(equal? 0 (interp x1 defs dfsubst)) (interp x2 defs dfsubst)]
               [else (interp x3 defs dfsubst)])]
    [app (fname arg-exprs)
         (arity-error fname arg-exprs defs dfsubst)]))

; arity-error
; checks for wrong arity
(define (arity-error fname arg-exprs defs dfsubst)
         (local [(define fxn (lookup-fundef fname defs))
                 (define zippy (zip-cons PofSym-Num (fundef-arg-names fxn) (map (lambda (x) (interp x defs dfsubst)) arg-exprs)))]  
           (cond [(= (length (fundef-arg-names fxn))(length arg-exprs))(interp (fundef-body fxn) defs zippy)]
                 [else (error "wrong arity")])))


; mult-and-neg-deffuns
(define mult-and-neg-deffuns
  (list
   ; logic deffun
   '(deffun (not p) (if0 p 1 0))
   '(deffun (or p q) (if0 p 0 (if0 q 0 1)))
   '(deffun (and p q) (if0 p (if0 q 0 1) 1))
   '(deffun (nand p q) (not (and p q)))
   '(deffun (nor p q) (not (or p q)))
      ; predicate deffun 
   '(deffun (zero? p) (and 0 p))
   '(deffun (pos? p) (not(or (zero? p)(neg? p))))
   '(deffun (is-neg? p n) (if0 (or (zero? p)(zero? n)) 1
      (if0 (+ n 1) 0 
           (if0 (zero? (- p 1)) 1 
                (is-neg? (- p 1) (+ n 1))))))
   ; operators
   '(deffun (abs p) (if0 (pos? p) p (- 0 p)))
   '(deffun (summation n p) (if0 n 0 (+ p (summation (- n 1) p))))
   '(deffun (mult p q)
      (with (n (summation (abs p) q)) (if0 (pos? p) n (- 0 n))))
   '(deffun (neg? p) (is-neg? p p))))
 

; library-defn 
; defines a function that contains the library
; mainly for test cases
(define library-defn (map parse-defn mult-and-neg-deffuns))

; library tests
(test (interp-expr (num 5) library-defn) 5)
(test (interp-expr (parse '(neg? 5)) library-defn) 1)



(test (interp-expr (parse '(pos? 5)) library-defn) 0)
(test (interp-expr (parse '(mult 5 5)) library-defn) 25)
(test (interp-expr (parse '(mult -5 5)) library-defn) -25)
(test (interp-expr (parse '(mult  5 -5)) library-defn) -25)
(test (interp-expr (parse '(mult -5 -5)) library-defn) 25)
(test (interp-expr (parse '(and  1 1)) library-defn) 1)
(test (interp-expr (parse '(or 0 1)) library-defn) 0)

(test (interp-expr (parse '(abs 3)) library-defn) 3)
(test (interp-expr (parse '(abs -3)) library-defn) 3)
(test (interp-expr (parse '(zero? -3)) library-defn) 1)
(test (interp-expr (parse '(not 1)) library-defn) 0)



;; parser tests

;trival 
(test (parse 1) (num 1))
(test (parse 'x) (id 'x))
(test (parse '(+ 1 1)) (add (num 1) (num 1)))
(test (parse '(- 1 1)) (sub (num 1) (num 1)))
(test (parse '(+ 1 (+ 1 1))) (add (num 1) (add (num 1) (num 1))))

; with and app
(test (parse '(with (x 1) x)) (with 'x (num 1) (id 'x)))
(test (parse '(f x y)) (app 'f (list (id 'x) (id 'y))))
(test (interp (parse '{x})(list (parse-defn '{deffun {x} 1})) empty) 1)
(test(interp (parse '{- {x} {x}})(list (parse-defn '{deffun {x} 1})) empty)0)

; Conditionals test
(test (interp-expr (parse '{if0 0 1 2}) '()) 1)
(test (interp-expr (parse '{if0 0 0 3}) '()) 0)
(test (interp-expr (parse '{if0 3 4 9}) '()) 9)

; error test cases
(test/exn (interp-expr (parse '{f 1 1 1 x})(list (parse-defn '{deffun {f a b c} a})))"free variable")
(test/exn (interp-expr (parse '{f x})(list (parse-defn '{deffun {f a b c} b})))"free variable")
(test/exn (interp (id 'x) '() '()) "free variable")
(test/exn (interp (parse '(f 0)) '() '()) "undefined function: f")
(test/exn (interp (parse '{f 1})(list (parse-defn '{deffun {f} {+ 1 77}})) empty)"wrong arity")
(test/exn (interp (parse '{f 999})(list (parse-defn '{deffun {f x y} {+ x y}})) empty)"wrong arity")
(test/exn (interp-expr (parse '{f x})(list (parse-defn '{deffun {f x y z} y})))"free variable")
(test/exn (interp-expr (parse '{f x})(list (parse-defn '{deffun {fxn x y z} z})))"undefined function")
(test/exn (parse-defn '{deffun {f x x} x}) "bad syntax")
(test/exn (parse-defn '(deffun (f x x) (+ 1 x))) "bad syntax")
(test/exn (parse-defn '(deffun (f x x y) (+ x 1))) "bad syntax")

;shadow fuction test case
(test (interp-expr (parse '{+ {f 1} {f 2}})(flatten (cons library-defn (list (parse-defn
                                                                              '{deffun {f x} {if0 {neg? {- x 3}}
                                                                                                  {with {x {+ x 1}} {f x}}
                                                                                                  x}}))))) 6)




; extra tests
(test/exn (lookup-fundef 'p '()) "undefined function: p")
(test/exn (lookup-fundef  'q (list (fundef 'f (list 'a) (id 'b))))"undefined function: q")



