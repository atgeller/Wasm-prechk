#lang racket

(require redex "IndexTypes.rkt" "Solver.rkt")

(provide test-satisfaction extract-constraints parse-index index-var->z3-bitvec parse-defs)

(define debug #t)

(define (index-var->z3-bitvec var)
  (match-let ([(cons name type) var])
    `(declare-const ,name (_ BitVec ,(match type ['i32 32] ['i64 64])))))

(define (ask-z3 vars constraints1 constraints2)
  (when debug
    (displayln vars)
    (displayln constraints1)
    (displayln constraints2))
  
  (solve (append (map index-var->z3-bitvec vars)
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

(define (parse-index x)
  (match x
    [(? symbol?) x]
    [`(,type ,n) #:when (and (redex-match? WASMIndexTypes t type)
                             (number? n))
                 (string->symbol (format "(_ bv~a ~a)" n (match type
                                                           ['i32 32]
                                                           ['i64 64])))]
    [`(,u_op ,x)
     #:when (redex-match? WASMIndexTypes unop u_op)
     (let ([index (parse-index x)])
       (redex_op->z3_op `(,u_op ,index)))]
    [`(,b_op ,x ,y)
     #:when (redex-match? WASMIndexTypes binop b_op)
     (let ([index1 (parse-index x)]
           [index2 (parse-index y)])
       (redex_op->z3_op `(,b_op ,index1 ,index2)))]
    [`(,t_op ,x)
     #:when (redex-match? WASMIndexTypes testop t_op)
     (let ([index (parse-index x)])
       `(ite ,(redex_op->z3_op `(,t_op ,index)) (_ bv1 32) (_ bv0 32)))]
    [`(,r_op ,x ,y)
     #:when (redex-match? WASMIndexTypes relop r_op)
     (let ([index1 (parse-index x)]
           [index2 (parse-index y)])
       `(ite ,(redex_op->z3_op `(,r_op ,index1 ,index2)) (_ bv1 32) (_ bv0 32)))]))

(define (parse-proposition P)
  (match P
    [`(= ,x ,y)
     (let ([index1 (parse-index x)]
           [index2 (parse-index y)])
       `(= ,index1 ,index2))]
    [`(not ,P*)
     (let ([prop (parse-proposition P*)])
       `(not ,prop))]
    [`(and ,P1 ,P2)
     (let ([prop1 (parse-proposition P1)]
           [prop2 (parse-proposition P2)])
       `(and ,prop1 ,prop2))]
    [`(or ,P1 ,P2)
     (let ([prop1 (parse-proposition P1)]
           [prop2 (parse-proposition P2)])
       `(or ,prop1 ,prop2))]
    [`(if ,P? ,P1 ,P2)
     (let ([cond (parse-proposition P?)]
           [true (parse-proposition P1)]
           [false (parse-proposition P2)])
       `(ite ,cond ,true ,false))]
    [`⊥
     `false]))

(define (parse-defs gamma)
  (match gamma
    [`empty null]
    [`(,gamma* (,t ,a)) (cons (cons a t) (parse-defs gamma*))]))

(define (extract-constraints phi)
  (match phi
    [`empty null]
    [`(,phi* ,P) (cons (parse-proposition P) (extract-constraints phi*))]))

(define (context-to-constraints gamma phi_1 phi_2)
  (let* ([vars (parse-defs gamma)]
         [consts1 (extract-constraints phi_1)]
         [consts2 (extract-constraints phi_2)])
    (values vars consts1 consts2)))

(define (test-satisfaction gamma phi_1 phi_2)
  (let-values ([(vars constraints1 constraints2) (context-to-constraints gamma phi_1 phi_2)])
    (or (null? constraints2)
        (and (not (null? constraints1))
             (not (ask-z3 vars constraints1 constraints2))))))