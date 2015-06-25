#lang plai

; Joseph lee
; EECS 321 Programming Languages
; Homework 5

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



(print-only-errors)




;FAE
;provided from HW5
(define-type FAE
  [num (n number?)]
  [add (lhs FAE?) (rhs FAE?)]
  [sub (lhs FAE?) (rhs FAE?)]
  [id (name symbol?)]
  [if0 (test FAE?) (then FAE?) (else FAE?)]
  [fun (param symbol?) (body FAE?)]
  [app (fun FAE?) (arg FAE?)])


;FAE val
;Obtained from lecture 7 slides
(define-type FAE-Val
  [numV (n number?)]
  [closureV (param symbol?)
            (body FAE?)
            (ds DefrdSub?)])


;FAE_pair
(define-type FAE_Pair 
  [fpair (name symbol?)(val FAE-Val?)])

(define DefrdSub? (listof FAE_Pair?))


;dfs options
(define-type id-key 
  [none] 
  [symF (sym (lambda (x) true))])

;;;;;;;;;;;;
;Parser
;;;;;;;;;;;;

;Parser
(define (parse sexpr)
  (cond
    [(number? sexpr) (num sexpr)]
    [(symbol? sexpr) (id sexpr)]
    [(pair? sexpr)
     (case (car sexpr)
       [(+) (add (parse (cadr sexpr)) (parse (caddr sexpr)))]
       [(-) (sub (parse (cadr sexpr)) (parse (caddr sexpr)))]
       [(with) (app 
                (fun (car (cadr sexpr)) (parse (caddr sexpr))) 
                (parse (cadr (cadr sexpr))))]
       [(if0) (if0 (parse (cadr sexpr))
                   (parse (caddr sexpr))
                   (parse (cadddr sexpr)))]
       [(fun) (define (f-help args body) 
                (cond [(equal? 0 (length args)) (error "bad syntax")]
                      [(equal? 1 (length args)) (fun (car args) (parse body))]
                      [else (fun (car args) (f-help (cdr args) body))]))
              (f-help (cadr sexpr) (caddr sexpr))]
       [else   (define (f-help sexpr) 
                 (cond[(equal? 1 (length sexpr))(parse (car sexpr))]
                      [else (app (f-help (drop-right sexpr 1)) (parse (last sexpr)))]
                      )
                 )
               (cond[ (equal? 1 (length sexpr)) 
                   (error "appliction without arguments")]
                   [else (f-help sexpr)])]
       )]
    [else (error "unexpected token")]))


; lookup 
(define (lookup name ds)
  (fpair-val (index-lookup
              (λ (fx) (symbol=? (fpair-name fx) name)) ds 
              (error-push name "free identifier: "))))

;pushes error message through lookup
(define (error-push name str)
  (string-append str (symbol->string name)))
  

; find-id : symbol list -> list-of-symbols
; returns specified symbols as list
(define (find-id s1 lst)
  (cond [(empty? lst) (none)]
        [(s1 (car lst)) (symF (car lst))]
        [else (find-id s1 (cdr lst))]))

; index-lookup
; checks the symbol of interest to see if contained
; in id-key, otherwise prints an error message
; provided from hw4
(define (index-lookup s lst error-string)
  (type-case id-key (find-id s lst) 
    [none () (error error-string)]
    [symF (sym) sym]))





;;;;;;;;;;;;;;;;;
; Interpretor
;;;;;;;;;;;;;;;;;





;interp-expr
; takes one argument and acts as wrapper
(define (interp-expr expr) 
  (-> any/c FAE?)
  (type-case FAE-Val (interp expr empty)
    [numV (n) n]
    [closureV (sx bx ds) 'procedure]))

;interp 
(define/contract (interp expr ds)
  (-> FAE? DefrdSub? FAE-Val?)
  (type-case FAE expr
    [num (n) (numV n)]
    [add (lhs rhs) (op+ (interp lhs ds) (interp rhs ds))]
    [sub (lhs rhs) (op- (interp lhs ds) (interp rhs ds))]
    [id (name) (lookup name ds)]
    [if0 (x1 x2 x3)
         (local [(define (bool-op  n) (if (numV? n) (numV-n n) 1))]
         (cond [(equal? 0 (bool-op (interp x1 ds))) (interp x2 ds) ]
               [else (interp x3 ds)]))]
    [fun (id body) (closureV id body ds)]
    [app (f-expr a-expr) 
         (let ([f (interp f-expr ds)][a (interp a-expr ds)])
           (type-case FAE-Val f
             [numV (n) (error "application expected procedure")]
             [closureV (id body dcs)
                       (interp body (cons (fpair id a) dcs))]))
         ]))


; num operations
; based from lecture notes 7&8
(define (op+ l r) (a-op + l r "numeric operation expected number"))
(define (op- l r) (a-op - l r "numeric operation expected number"))

(define (a-op op l r str)
  (cond[(and (numV? l) (numV? r)) (numV (op (numV-n l)(numV-n r)))]
       [else (error str)]))
       



;;;;;;;;;;;;;;;;;;;;;;
; FAE Level Functions
;;;;;;;;;;;;;;;;;;;;;;

;recursive helper function
(define mk-rec0 '{fun {body}
                    {with {fX {fun {fX}
                                   {with {gx {fun {y}
                                                  {{fX fX} y}}}
                                         {body gx}}}}
                          {fX fX}}})

(define mk-rec1 '{fun {natf}
                      {fun {n XX F}
                           {if0 n
                                XX
                                {F {natf {- n 1} XX F}}}}})
;n-to-f
;modified from lecture slides 7-8
(define n-to-f `{fun {Nat} 
                     {with {mk-rec ,mk-rec0}
                           {with {n-to-f {mk-rec
                                          ,mk-rec1}}
                                 {fun {f} 
                                      {fun {x} {n-to-f Nat x f}}}}}})



(test (interp-expr (num 10)) 10)
(test (interp-expr (fun 'x (id 'x))) 'procedure)
;add 1 helper function
(define add1 '{fun {x}{+ 1 x}})

  
(define f-to-n `{fun {FX}
                     {{FX ,add1}
                      0}})

(define plus `{fun {FX1 FX2}
                   {fun {ifop} 
                        {fun {x}
                             {{FX2 ifop} {{FX1 ifop} x}}}}})
(define times `{fun {FX1 FX2}
                    {fun {x} {FX1 {FX2 x}}}})



;parse basics
(test (parse 1) (num 1))
(test (parse 'x) (id 'x))
(test (parse '(+ 1 1)) (add (num 1) (num 1)))
(test (parse '(if0 1 2 3)) (if0 (num 1) (num 2) (num 3)))

;interp-exr tests
(test (interp-expr (parse 0)) 0)
(test (interp-expr (parse (- 50 50))) 0)
(test (interp-expr (parse '((fun (x) (fun (y) (+ x y))) 5))) 'procedure)
(test (interp-expr (parse '(fun (x) (+ x 60)))) 'procedure)
(test (interp-expr (parse '(if0 0 2 3))) 2)

(test/exn (interp-expr (parse `{+ {fun {x} x}
                                  {9 2}}))
          "application expected procedure")

(test (interp-expr (parse '((fun (x x) x) 1 8))) 8)




;Part 4 tests

(define hw-test0 `{fun {f} {fun {x} x}})
(define hw-test1 `{fun {f} {fun {x} x}})
(define hw-test2 `{fun {f} {fun {x} {f {f {f x}}}}})
(define hw-test3 `{,n-to-f 9})
(define hw-test4 `{,f-to-n 9})
(define hw-test5  `{plus {n-to-f 0} {n-to-f 0}})
(define hw-test6 `{,n-to-f 0})

(test (interp-expr (parse `{,f-to-n ,hw-test0}))0)
(test (interp-expr (parse `{,f-to-n ,hw-test2}))3)

(test (interp-expr (parse `{,f-to-n ,hw-test3}))
      9)

(test (interp-expr (parse `{,f-to-n {,times {,plus ,hw-test0 ,hw-test3} ,hw-test0}}))
      0)

(test/exn (interp-expr (parse `{+ {,n-to-f 9} {,n-to-f 9}}))
          "numeric operation expected number")

(test/exn (interp-expr (parse `{with {f {fun {y} x}}
                                     {with {x 8}
                                           {f 4}}}))
          "free identifier")

(test (interp-expr (parse `{,f-to-n {,times {,plus ,hw-test1 ,hw-test2} ,hw-test6}})) 0)

(test (interp-expr (app (app (app (parse n-to-f)
                                  (num 2))
                             (fun 'f (add (id 'f) (num 1))))
                        (num 1)))
      3)



(test (interp-expr (app (app (app (parse n-to-f)
                             (num 100))
                        (fun 'f (num 0)))
                   (num 0)))
      0)








