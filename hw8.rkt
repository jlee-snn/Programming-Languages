#lang plai-typed

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

(print-only-errors true)

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

(define-type Type 
  [numT]
  [boolT]
  [arrowT (dom : Type) (codom : Type)]
  [listT (typ : Type)])

(define-type TypeEnv
  [mtEnv]
  [aBind (sym : symbol)
         (typ : Type)
         (rst : TypeEnv)])

(define verify-type : (Type Type -> void)
  (lambda (typ1 typ2)
    (unless (equal? typ1 typ2)
      (error 'verify-type "type-error"))))


(test (verify-type (numT) (numT))
      (void))
(test/exn (verify-type (numT) (boolT))
          "type-error")


(define verify-two : (Type Type Type -> Type)
  (lambda (typ1 typ2 typshould)
    (begin
      (verify-type typ1 typshould)
      (verify-type typ2 typshould)
      typshould)))

(test (verify-two (numT) (numT) (numT))
      (numT))
(test/exn (verify-two (boolT) (numT) (numT))
          "type-error")

(define verify-two-same : (Type Type -> Type)
  (lambda (typ1 typ2)
    (verify-two typ1 typ2 typ1)))

(test (verify-two-same (numT) (numT))
      (numT))
(test (verify-two-same (listT (boolT)) (listT (boolT)))
      (listT (boolT)))
(test/exn (verify-two-same (listT (boolT)) (listT (numT)))
          "type-error")

(define lookup : (symbol TypeEnv -> Type)
  (lambda (name env)
    (type-case TypeEnv env
      [mtEnv () (error 'lookup "type-error")]
      [aBind (sym typ rst) (if (equal? sym name)
                               typ
                               (lookup name rst))])))
(test (lookup 'x  (aBind 'z (arrowT (boolT) (boolT)) (aBind 'y (numT) (aBind 'x (numT) (mtEnv)))))
      (numT))
(test/exn (lookup 'x (mtEnv))
          "type-error")

(define verify-app : (Type Type -> Type)
  (lambda (typ1 typ2)
    (type-case Type typ1
      [arrowT (from-typ to-typ) (if (equal? from-typ typ2)
                                    to-typ
                                    (error 'verify-app "type-error: app case"))]
      [else (error 'verify-app "type-error: app case")])))
(test (verify-app (arrowT (numT) (boolT))
                  (numT))
      (boolT))
(test/exn (verify-app (arrowT (numT) (boolT))
                      (boolT))
          "type-error")
(test/exn (verify-app (boolT)
                      (boolT))
          "type-error")

(define verify-cons : (Type Type -> Type)
  (lambda (typ1 typ2)
    (type-case Type typ2
      [listT (of-typ) (if (equal? of-typ typ1)
                          typ2
                          (error 'verify-cons "type-error: cons case"))]
      [else (error 'verify-cons "type-error: cons case")])))
(test (verify-cons (numT) (listT (numT)))
      (listT (numT)))
(test/exn (verify-cons (numT) (numT))
          "type-error")
(test/exn (verify-cons (numT) (listT (boolT)))
          "type-error")

(define list-holds : (Type -> Type)
  (lambda (typ)
    (type-case Type typ
      [listT (lst-typ) lst-typ]
      [else (error 'list-holds "type-error: should be a list")])))
(test (list-holds (listT (boolT)))
      (boolT))
(test/exn (list-holds (boolT))
          "type-error")

(define is-list : (Type -> Type)
  (lambda (typ)
    (type-case Type typ
      [listT (lst-typ) typ]
      [else (error 'list-holds "type-error: should be a list")])))
(test (is-list (listT (boolT)))
      (listT (boolT)))
(test/exn (is-list (boolT))
          "type-error")
      
;;type-check-expr : TFAE -> Type
(define type-check : (TFAE TypeEnv -> Type)
  (lambda (fae env)
    (type-case TFAE fae
      [num (n) (numT)]
      [bool (b) (boolT)]
      [add (l r) (verify-two (type-check l env)
                             (type-check r env)
                             (numT))]
      [sub (l r) (verify-two (type-check l env)
                             (type-check r env)
                             (numT))]
      [eql (l r) (begin
                   (verify-two (type-check l env)
                               (type-check r env)
                               (numT))
                   (boolT))]
      [id (name) (lookup name env)]
      [ifthenelse (cnd ifb elb) (begin
                                  (verify-type (type-check cnd env) (boolT))
                                  (verify-two-same (type-check ifb env)
                                                   (type-check elb env)))]
      [fun (arg typ body) (arrowT typ (type-check body (aBind arg typ env)))]
      [app (rator rand) (let ([rator-typ (type-check rator env)]
                              [rand-typ (type-check rand env)])
                          (verify-app rator-typ rand-typ))]
      [consl (hd tl) (let ([hd-typ (type-check hd env)]
                           [tl-typ (type-check tl env)])
                       (verify-cons hd-typ tl-typ))]
      [firstl (lst) (list-holds (type-check lst env))]
      [restl (lst) (is-list (type-check lst env))]
      [nil (typ) (listT typ)]
      [mtl? (lst) (begin
                    (is-list (type-check lst env))    
                    (boolT))])))

(define type-check-expr : (TFAE -> Type)
  (lambda (fae)
    (type-check fae (mtEnv))))
(test (type-check-expr (num 0))
      (numT))

(test (type-check (num 0) (mtEnv))
      (numT))
(test/exn (type-check (id 'x) (mtEnv))
          "type-error")
(test (type-check (bool false) (mtEnv))
      (boolT))
(test (type-check (id 'x) (aBind 'x (boolT) (mtEnv)))
      (boolT))
(test (type-check (id 'x) (aBind 'y (numT) (aBind 'x (boolT) (mtEnv))))
      (boolT))
(test (type-check (id 'x) (aBind 'y (numT) (aBind 'x (arrowT (numT) (numT)) (mtEnv))))
      (arrowT (numT) (numT)))
(test (type-check (id 'x) (aBind 'y (numT) (aBind 'x (listT (boolT)) (mtEnv))))
      (listT (boolT)))
(test/exn (type-check (add (id 'x) (id 'y)) 
                           (aBind 'y (numT) (aBind 'x (listT (boolT)) (mtEnv))))
          "type-error")
(test/exn (type-check (add (id 'x) (id 'y)) 
                           (aBind 'y (numT) (aBind 'x (listT (numT)) (mtEnv))))
          "type-error")
(test (type-check (add (id 'x) (id 'y)) 
                       (aBind 'y (numT) (aBind 'x (numT) (mtEnv))))
      (numT))
(test (type-check (sub (id 'x) (id 'y)) 
                       (aBind 'y (numT) (aBind 'x (numT) (mtEnv))))
      (numT))
(test/exn (type-check (add (id 'x) (id 'y)) 
                           (aBind 'y (numT) (aBind 'x (arrowT (numT) (boolT)) (mtEnv))))
          "type-error")
(test/exn (type-check (eql (id 'x) (id 'y))
                           (aBind 'y (numT) (aBind 'x (arrowT (numT) (boolT)) (mtEnv))))
          "type-error")
(test (type-check (eql (id 'x) (id 'y))
                       (aBind 'y (numT) (aBind 'x (numT) (mtEnv))))
      (boolT))
(test/exn (type-check (ifthenelse (id 'x) (id 'y) (id 'z))
                           (aBind 'z (numT) (aBind 'y (numT) (aBind 'x (numT) (mtEnv)))))
          "type-error")
(test/exn (type-check (ifthenelse (id 'z) (id 'y) (id 'x))
                           (aBind 'z (arrowT (boolT) (boolT)) (aBind 'y (numT) (aBind 'x (numT) (mtEnv)))))
          "type-error")
(test/exn (type-check (ifthenelse (id 'z) (id 'y) (id 'x))
                           (aBind 'z (boolT) (aBind 'y (numT) (aBind 'x (boolT) (mtEnv)))))
          "type-error")
(test/exn (type-check (ifthenelse (id 'z) (id 'y) (id 'x))
                           (aBind 'z (boolT) 
                                  (aBind 'y (listT (numT)) 
                                         (aBind 'x (listT (boolT)) (mtEnv)))))
          "type-error")
(test (type-check (ifthenelse (id 'z) (id 'y) (id 'x))
                       (aBind 'z (boolT) (aBind 'y (numT) (aBind 'x (numT) (mtEnv)))))
      (numT))
(test (type-check (ifthenelse (id 'z) (id 'y) (id 'x))
                       (aBind 'z (boolT) (aBind 'y (listT (boolT)) (aBind 'x (listT (boolT)) (mtEnv)))))
      (listT (boolT)))
(test (type-check (fun 'a (listT (numT)) (firstl (id 'a)))
                       (aBind 'z (boolT) (aBind 'y (listT (boolT)) (aBind 'x (listT (boolT)) (mtEnv)))))
      (arrowT (listT (numT)) (numT)))
(test (type-check (fun 'a (listT (numT)) (restl (id 'a)))
                       (aBind 'z (boolT) (aBind 'y (listT (boolT)) (aBind 'x (listT (boolT)) (mtEnv)))))
      (arrowT (listT (numT)) (listT (numT))))
(test (type-check (fun 'a (listT (numT)) (nil (boolT)))
                       (aBind 'z (boolT) (aBind 'y (listT (boolT)) (aBind 'x (listT (boolT)) (mtEnv)))))
      (arrowT (listT (numT)) (listT (boolT))))
(test (type-check (mtl? (nil (boolT)))
                       (aBind 'z (boolT) (aBind 'y (listT (boolT)) (aBind 'x (listT (boolT)) (mtEnv)))))
      (boolT))
(test (type-check (mtl? (consl (id 'x) (id 'y)))
                       (aBind 'z (boolT) (aBind 'y (listT (boolT)) (aBind 'x (boolT) (mtEnv)))))
      (boolT))
(test/exn (type-check (mtl? (consl (id 'x) (id 'y)))
                           (aBind 'z (boolT) (aBind 'y (listT (boolT)) (aBind 'x (listT (numT)) (mtEnv)))))
          "type-error")
(test/exn (type-check (mtl? (consl (id 'x) (id 'y)))
                           (aBind 'z (boolT) (aBind 'y (listT (boolT)) (aBind 'x (listT (boolT)) (mtEnv)))))
          "type-error")
(test/exn (type-check (mtl? (consl (id 'y) (id 'z)))
                           (aBind 'z (boolT) (aBind 'y (listT (boolT)) (aBind 'x (listT (boolT)) (mtEnv)))))
          "type-error")
(test/exn (type-check (mtl? (consl (id 'y) (id 'z)))
                           (aBind 'z (boolT) (aBind 'y (boolT) (aBind 'x (listT (boolT)) (mtEnv)))))
          "type-error")
(test (type-check (app (id 'x) (id 'y))
                       (aBind 'z (boolT) (aBind 'y (numT) (aBind 'x (arrowT (numT) (boolT)) (mtEnv)))))
      (boolT))
(test/exn (type-check (app (id 'x) (id 'z))
                           (aBind 'z (boolT) (aBind 'y (listT (numT)) (aBind 'x (arrowT (numT) (boolT)) (mtEnv)))))
          "type-error")
(test (type-check (fun 'a (listT (numT)) (firstl (consl (id 'z) (id 'a))))
                       (aBind 'z (numT) (aBind 'y (listT (boolT)) (aBind 'x (listT (boolT)) (mtEnv)))))
      (arrowT (listT (numT)) (numT)))
(test/exn (type-check (fun 'a (listT (numT)) (firstl (consl (id 'z) (id 'a))))
                       (aBind 'z (boolT) (aBind 'y (listT (boolT)) (aBind 'x (listT (boolT)) (mtEnv)))))
          "type-error")
(test (type-check (fun 'a (listT (numT)) (restl (consl (id 'z) (id 'a))))
                       (aBind 'z (numT) (aBind 'y (listT (boolT)) (aBind 'x (listT (boolT)) (mtEnv)))))
      (arrowT (listT (numT)) (listT (numT))))
(test/exn (type-check (fun 'a (listT (numT)) (restl (consl (id 'z) (id 'a))))
                       (aBind 'z (boolT) (aBind 'y (listT (boolT)) (aBind 'x (listT (boolT)) (mtEnv)))))
          "type-error")
