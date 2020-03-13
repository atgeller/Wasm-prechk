#lang racket

(require redex
         "SubTyping.rkt"
         "Satisfies.rkt"
         "Solver.rkt")

(provide check-table-call)

(define (construct-z3-table call-type table typelist)
  (let ([unique-typelist (remove-duplicates typelist)])
    (for/hash ([type unique-typelist])
      (displayln type)
      (displayln call-type)
      (values type (if (judgment-holds (<: ,call-type ,type))
                       'true
                       'false)))))

(define (check-table-call type index table typelist phi)
  (let*-values ([(typemap) (construct-z3-table type table typelist)]
                [(constraints vars) (extract-constraints phi null)]
                [(index-def) (parse-index index)])
    (let ([query (append (map index-var->z3-bitvec (remove-duplicates vars))
                         `((declare-const table (Array (_ BitVec 32) Bool))
                           (define-fun satisfies () Bool
                             (select table ,index-def))
                           (assert (not satisfies)))
                         (map (lambda (x) `(assert ,x)) constraints)
                         (for/list ([i (in-range 0 (length typelist))])
                           `(assert (= (select table ,(string->symbol (format "(_ bv~a 32)" i))) ,(hash-ref typemap (list-ref typelist i))))))])
      (not (solve query)))))