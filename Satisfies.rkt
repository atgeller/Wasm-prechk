#lang racket

(require redex "IndexTypes.rkt" "solver.rkt")

(provide test-satisfaction)

(define debug #t)

(define (ask-z3 vars constraints1 constraints2)
  (when debug
    (displayln vars)
    (displayln constraints1)
    (displayln constraints2))
  
  (solve (append (map (lambda (x) `(declare-const ,x (_ BitVec 32))) vars)
                 `((define-fun satisfies () Bool
                     (=>
                      (and ,@constraints1)
                      (and ,@constraints2)))
                   (assert (not satisfies))))))

(define (redex_op->z3_op expr)
  (match expr
    [`(add ,x ,y) `(bvadd ,x ,y)]
    [`(sub ,x ,y) `(bvsub ,x ,y)]
    [`(mul ,x ,y) `(bvmul ,x ,y)]
    [`(div ,x ,y) `(bvdiv ,x ,y)]
    [`(rem ,x ,y) `(bvrem ,x ,y)]
    [`(and ,x ,y) `(bvand ,x ,y)]
    [`(or ,x ,y)  `(bvor ,x ,y)]
    [`(xor ,x ,y) `(bvxor ,x ,y)]
    [`(eq ,x ,y)  `(= ,x ,y)]
    [`(ne ,x ,y)  `(not (= ,x ,y))]
    [`(lt ,x ,y)  `(bvult ,x ,y)]
    [`(gt ,x ,y)  `(bvugt ,x ,y)]
    [`(le ,x ,y)  `(bvule ,x ,y)]
    [`(ge ,x ,y)  `(bvuge ,x ,y)]
    [`(eqz ,x)    `(= ,x (_ bv0 32))]))

(define (parse-index x vars)
  (match x
    [(? symbol?) (values x (cons x vars))]
    [(? number?) (values (string->symbol (format "(_ bv~a 32)" x)) vars)]
    [`(,u_op ,x)
     #:when (redex-match? WASMIndexTypes unop u_op)
     (let-values ([(index vars*) (parse-index x vars)])
       (values (redex_op->z3_op `(,u_op ,index)) vars*))]
    [`(,b_op ,x ,y)
     #:when (redex-match? WASMIndexTypes binop b_op)
     (let*-values ([(index1 vars1) (parse-index x vars)]
                   [(index2 vars2) (parse-index y vars1)])
       (values (redex_op->z3_op `(,b_op ,index1 ,index2)) vars2))]))

(define (parse-proposition P vars)
  (match P
    [`(,t_op ,x)
     #:when (redex-match? WASMIndexTypes testop t_op)
     (let-values ([(index vars*) (parse-index x vars)])
       (values (redex_op->z3_op `(,t_op ,index)) vars*))]
    [`(,r_op ,x ,y)
     #:when (redex-match? WASMIndexTypes relop r_op)
     (let*-values ([(index1 vars1) (parse-index x vars)]
                   [(index2 vars2) (parse-index y vars1)])
       (values (redex_op->z3_op `(,r_op ,index1 ,index2)) vars2))]
    [`(not ,P*)
     (let-values ([(prop vars*) (parse-proposition P* vars)])
       (values `(not ,prop) vars*))]
    [`(and ,P1 ,P2)
     (let*-values ([(prop1 vars1) (parse-proposition P1 vars)]
                   [(prop2 vars2) (parse-proposition P2 vars1)])
       (values `(and ,prop1 ,prop2) vars2))]
    [`(or ,P1 ,P2)
     (let*-values ([(prop1 vars1) (parse-proposition P1 vars)]
                   [(prop2 vars2) (parse-proposition P2 vars1)])
       (values `(or ,prop1 ,prop2) vars2))]
    [`(if ,P ,x ,y)
     (let*-values ([(prop vars1) (parse-proposition P vars)]
                   [(index1 vars2) (parse-index x vars1)]
                   [(index2 vars3) (parse-index y vars2)])
       (values `(ite ,prop ,index1 index2) vars3))]))

(define (make-proposition P)
  (parse-proposition P null))

(define (extract-constraints phi vars)
  (match phi
    [`empty (values null vars)]
    [`(,phi* ,P)
     (let*-values ([(new-constraint new-vars) (make-proposition P)]
                   [(rest-constraints rest-vars)
                    (extract-constraints phi* (append new-vars vars))])
       (values (cons new-constraint rest-constraints) rest-vars))]))

(define (context-to-constraints phi_1 phi_2)
  (let*-values ([(consts1 vars1) (extract-constraints phi_1 null)]
                [(consts2 vars2) (extract-constraints phi_2 vars1)])
    (values (remove-duplicates vars2) consts1 consts2)))

(define (test-satisfaction phi_1 phi_2)
  (let-values ([(vars constraints1 constraints2) (context-to-constraints phi_1 phi_2)])
    (not (ask-z3 vars constraints1 constraints2))))