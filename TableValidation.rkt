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
      (displayln (equal? type call-type))
      (values type (if (equal? type call-type)
                       'true
                       'false)))))

(define (check-table-call type index typelist gamma phi)
  (displayln "Hello world")
  (let* ([typemap (construct-z3-table type typelist)]
         [vars (parse-defs gamma)]
         [constraints (extract-constraints gamma phi)]
         [index-def (parse-index gamma index)])
    (let ([query (append (map index-var->z3-const vars)
                         `((declare-const table (Array (_ BitVec 32) Bool))
                           (define-fun satisfies () Bool
                             (select table ,index-def))
                           (assert (not satisfies)))
                         (map (lambda (x) `(assert ,x)) constraints)
                         (for/list ([i (in-range 0 (length typelist))])
                           `(assert (= (select table ,(integer->z3-bitvec i 32)) ,(hash-ref typemap (list-ref typelist i))))))])
      (not (solve query)))))

(define-metafunction WASMIndexTypes
  valid-table-call : tfi ivar (tfi ...) Γ φ -> boolean
  [(valid-table-call tfi ivar (tfi_2 ...) Γ φ)
   ,(check-table-call (term tfi) (term ivar) (term (tfi_2 ...)) (term Γ) (term φ))])
