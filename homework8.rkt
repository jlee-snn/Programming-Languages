#lang plai-typed


;Joseph Lee;
;EECS 321
;HW 8 Types

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


(print-only-errors #t)

;;given def
;TFAE
(define-type TFAE
  [num (n : number)]
  [bool (b : boolean)]
  [add (l : TFAE) (r : TFAE)]
  [sub (l : TFAE) (r : TFAE)]
  [eql (l : TFAE) (r : TFAE)]
  [id (name : symbol)]
  [ifthenelse (tst : TFAE) (thn : TFAE) (els : TFAE)]
  [fun (arg : symbol) (typ : Type) (body : TFAE)]
  [app (rator : TFAE) (rand : TFAE)]
  [consl (fst : TFAE) (rst : TFAE)]
  [firstl (lst : TFAE)]
  [restl (lst : TFAE)]
  [nil (typ : Type)]
  [mtl? (lst : TFAE)])

;given in assignment
(define-type Type 
  [numT]
  [boolT]
  [arrowT (dom : Type) (codom : Type)]
  [listT (typ : Type)])

; ds
; deferred sub method
(define-type DefrdSub
  [mtSub]
  [aBind (name : symbol)
         (typ : Type)
         (rest : DefrdSub)])

;derived from Textbook
(define type-error-check
  (lambda (t1 t2)
    (when (not(equal? t1 t2))
      (error 'type-error-check "type-error"))))

; checks typs of arguments of mth operations
(define op-type-check
  (lambda (t1 t2 realtype)
    (begin
      (type-error-check t1 realtype)
      (type-error-check t2 realtype)
      realtype)))
;check for equavalent types
(define eq-check
  (lambda (t1 t2)
    (op-type-check t1 t2 t1)))

;env or deferred sub
(define dfrd-lookup 
  (lambda (name ds)
    (type-case DefrdSub ds
      [mtSub () (error 'dfrd-lookup "type-error")]
      [aBind (sym typ rst) (cond[(equal? sym name) typ]
                                [else (dfrd-lookup name rst)])])))


;type check for app case
(define type-app-check
  (lambda (t1 t2)
    (type-case Type t1
      [arrowT (from-typ to-typ) (cond[(equal? from-typ t2) to-typ]
                                     [else (error 'type-app-check "type-error")])]
      [else (error 'type-app-check "type-error")])))

;type check ase for cons
(define is-cons?
  (lambda (t1 t2)
    (type-case Type t2
      [listT (of-typ) (cond[ (equal? of-typ t1) t2]
                         [else  (error 'is-cons? "type-error")])]
      [else (error 'is-cons? "type-error")])))

;list check, first
(define list-first
  (lambda (typ)
    (type-case Type typ
      [listT (lst-typ) lst-typ]
      [else (error 'list-first "type-error")])))

;list check rest
(define list-rest
  (lambda (typ)
    (type-case Type typ
      [listT (lst-typ) typ]
      [else (error 'list-first "type-error")])))

; acts as wrapper for type-check

(define type-check-expr : (TFAE -> Type)
  (lambda (tfae)
    (type-check tfae (mtSub))))

;;type-check-expr : TFAE -> Typ
;; with contract 
(define type-check : (TFAE DefrdSub -> Type)
  (lambda (fae ds)
    (type-case TFAE fae
      [num (n) (numT)]
      [bool (b) (boolT)]
      [add (l r) (op-type-check (type-check l ds)
                                (type-check r ds)
                                (numT))]
      [sub (l r) (op-type-check (type-check l ds)
                                (type-check r ds)
                                (numT))]
      [eql (l r) (begin
                   (op-type-check (type-check l ds)
                                  (type-check r ds)
                                  (numT))
                   (boolT))]
      [id (name) (dfrd-lookup name ds)]
      [ifthenelse (prd thn els) (conditional-case prd thn els ds)]
      [fun (param typ body) (arrowT typ (type-check body (aBind param typ ds)))]
      [app (rator rand)(app-case rator rand ds)]
      [consl (hd tl) (consl-case hd tl ds)]
      [firstl (lst) (list-first (type-check lst ds))]
      [restl (lst) (list-rest (type-check lst ds))]
      [nil (t) (listT t)]
      [mtl? (lst) (begin  (list-rest (type-check lst ds)) (boolT))])))

(define (consl-case h t ds)
  (let ([hd (type-check h ds)]
        [tl (type-check t ds)])
                       (is-cons? hd tl)))


(define (app-case rat ran ds)
  (let ([rat-typ (type-check rat ds)]
                              [ran-typ (type-check ran ds)])
                          (type-app-check rat-typ ran-typ)))

(define (conditional-case p t e ds)
  (begin
    (type-error-check (type-check p ds) (boolT))
    (eq-check (type-check t ds)
              (type-check e ds))))


;Test cases




(test (type-error-check (boolT) (boolT))
      (void))

(test/exn (is-cons? (boolT) (numT))
          "type-error")

(test (type-check (num 1) (mtSub))
      (numT))
(test (type-check-expr (restl (consl (num 0) (consl (num 0) (nil (numT)))))) (listT (numT)))

(test/exn (type-check (app (num 1) (num 7)) (mtSub))
            "type-error")

(test/exn (type-check (add (fun 'x (numT) (num 4))
                              (num 0))
                         (mtSub))
            "type-error")
  
(test (type-check-expr (num 12))
      (numT))

(test/exn (type-check-expr (ifthenelse (bool true) 
 			   (consl (bool true) (nil (numT))) 
 			   (consl (num 7) (nil (numT)))))
 	  "type-error")


(test (type-check (fun 'x (listT (numT)) (restl (id 'x)))
                       (aBind 'z (boolT) (aBind 'x (listT (boolT)) (mtSub))))
      (arrowT (listT (numT)) (listT (numT))))

(test/exn (type-check (mtl? (consl (id 'x) (id 'y)))
                           (aBind 'f (numT) (aBind 'y (listT (numT)) (mtSub))))"type-error")


(test (type-check (app (id 'x) (id 'y))
                       (aBind 'z (numT) (aBind 'y (numT) (aBind 'x (arrowT (numT) (boolT)) (mtSub)))))
      (boolT))

(test (type-check (fun 'y (listT (numT)) (restl (consl (id 'a) (id 'b))))
                       (aBind 'a (numT) (aBind 'b (listT (numT)) (mtSub))))
      (arrowT (listT (numT)) (listT (numT))))

(test (type-check-expr (restl (consl (num 1) (consl (num 9) (nil (numT))))))(listT(numT)))
(test/exn (type-check-expr (restl (consl (bool true) (consl (num 9) (nil (numT)))))) "type-error")

