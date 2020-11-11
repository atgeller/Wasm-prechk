#lang racket

(require redex
         "SubTyping.rkt"
         "Satisfies.rkt"
         "Solver.rkt"
         "IndexTypes.rkt")

(provide valid-table-call)

(define (construct-z3-table call-type typelist)
  (let ([unique-typelist (remove-duplicates typelist)])
    (for/hash ([type unique-typelist])
      (displayln type)
      (displayln call-type)
      (values type (if (judgment-holds (<: ,type ,call-type))
                       'true
                       'false)))))

(define (check-table-call type index typelist gamma phi)
  (displayln "Hello world")
  (let* ([typemap (construct-z3-table type typelist)]
         [vars (parse-defs gamma)]
         [constraints (extract-constraints phi)]
         [index-def (parse-index index)])
    (let ([query (append (map index-var->z3-bitvec vars)
                         `((declare-const table (Array (_ BitVec 32) Bool))
                           (define-fun satisfies () Bool
                             (select table ,index-def))
                           (assert (not satisfies)))
                         (map (lambda (x) `(assert ,x)) constraints)
                         (for/list ([i (in-range 0 (length typelist))])
                           `(assert (= (select table ,(string->symbol (format "(_ bv~a 32)" i))) ,(hash-ref typemap (list-ref typelist i))))))])
      (not (solve query)))))

(define-metafunction WASMIndexTypes
  valid-table-call : tfi a (tfi ...) Γ φ -> boolean
  [(valid-table-call tfi a (tfi_2 ...) Γ φ)
   ,(check-table-call (term tfi) (term a) (term (tfi_2 ...)) (term Γ) (term φ))])
