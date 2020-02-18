#lang racket

(require redex
         "IndexTypes.rkt"
         "Satisfies.rkt")

(provide satisfies <:)

;; TODO: this will need to actually work
(define-metafunction WASMIndexTypes
  simplify : φ -> φ
  [(simplify empty) empty]
  [(simplify (φ (a γ))) ((simplify φ) (a γ))]
  [(simplify (φ P)) ((simplify φ) P)])

;; TODO: this will need to actually work
;; Ensures index type context φ_1 satisfies φ_2
(define-metafunction WASMIndexTypes
  satisfies : φ_1 φ_2 -> boolean
  [(satisfies φ φ) #t]
  [(satisfies φ empty) #t]
  [(satisfies φ_1 φ_2) ,(test-satisfaction (term φ_1) (term φ_2))])

(define-judgment-form WASMIndexTypes
  #:contract (<: tfi tfi)
  #:mode (<: I I)
  
  [(where #t (satisfies φ_1 φ_2))
   (where #t (satisfies φ_3 φ_4))
   ------------------------------
   (<: (((ti_1 ...) φ_1) -> ((ti_2 ...) φ_4))
       (((ti_1 ...) φ_2) -> ((ti_2 ...) φ_3)))])