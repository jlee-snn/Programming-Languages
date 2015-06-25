#lang plai
(print-only-errors #t)


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




;   <RRFAE> = <number>
;          | {+ <RRFAE> <RRFAE>}
;          | {- <RRFAE> <RRFAE>}
;          | {fun {<id>} <RRFAE>}
;          | {<RRFAE> <RRFAE>}             ;; function application
;          | <id>
;          | {with {<id> <RRFAE>} <RRFAE>} ;; shorthand for fun & app
;          | {struct {<id> <RRFAE>} ...}  ;; all fields must be distinct
;          | {get <RRFAE> <id>}
;          | {set <RRFAE> <id> <RRFAE>}
;          | {seqn <RRFAE> <RRFAE>}




(define-type RFAE
  [num (n number?)]
  [add (lhs RFAE?) (rhs RFAE?)]
  [sub (lhs RFAE?) (rhs RFAE?)]
  [id (name symbol?)]
  [fun (param symbol?) (body RFAE?)]
  [app (fun RFAE?) (arg RFAE?)]
  [setter (r RFAE?) (id symbol?)]
  [getter (g RFAE?) (id symbol?)]
  [structX (t RFAE?) (id symbol?)]
  [seqn-x (fst RFAE?) (snd RFAE?)])






