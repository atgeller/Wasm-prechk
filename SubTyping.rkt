#lang racket

(require redex
         "IndexTypes.rkt"
         "Satisfies.rkt")

(provide satisfies <:)

;; Ensures index type context φ_1 satisfies φ_2
(define-metafunction WASMIndexTypes
  satisfies : φ_1 φ_2 -> boolean
  [(satisfies φ φ) #t]
  [(satisfies φ empty) #t]
  [(satisfies φ_1 φ_2) ,(test-satisfaction (term φ_1) (term φ_2))])

(define-judgment-form WASMIndexTypes
  #:contract (<: tfi tfi)
  #:mode (<: I I)
  
  [(side-condition (satisfies φ_1 φ_2))
   (side-condition (satisfies φ_3 φ_4))
   ------------------------------
   (<: (((ti_1 ...) locals_1 φ_1)
        -> ((ti_2 ...) locals_2 φ_4))
       (((ti_1 ...) locals_1 φ_2)
        -> ((ti_2 ...) locals_2 φ_3)))])