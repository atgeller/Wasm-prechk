#lang racket

(require redex
         "IndexTypes.rkt"
         "Satisfies.rkt")

(provide satisfies <:)

;; Ensures index type context φ_1 satisfies φ_2
(define-metafunction WASMIndexTypes
  satisfies : Γ φ_1 φ_2 -> boolean
  [(satisfies empty φ_1 φ_2) #t]
  [(satisfies Γ φ φ) #t]
  [(satisfies Γ φ empty) #t]
  [(satisfies Γ φ_1 φ_2) ,(test-satisfaction (term Γ) (term φ_1) (term φ_2))])

(define-judgment-form WASMIndexTypes
  #:contract (<: tfi tfi)
  #:mode (<: I I)
  
  [(side-condition (satisfies Γ_1 φ_1 φ_2))
   (side-condition (satisfies Γ_2 φ_3 φ_4))
   --------------------------------------
   (<: (((ti_1 ...) locals_1 Γ_1 φ_2)
        -> ((ti_2 ...) locals_2 Γ_2 φ_3))
       (((ti_1 ...) locals_1 Γ_1 φ_1)
        -> ((ti_2 ...) locals_2 Γ_2 φ_4)))]

  ;; This allows us to add fresh "scratch variables"
  ;; Among other things, this makes it easy to account for "deleted" intermediate state in the type safety proof
  [(where #f (in a Γ_2))
   -------------------
   (<: (((ti_1 ...) locals_1 Γ_1 φ_1)
        -> ((ti_2 ...) locals_2 Γ_2 φ_2))
       (((ti_1 ...) locals_1 Γ_1 φ_1)
        -> ((ti_2 ...) locals_2 (Γ_2 (t a)) (φ_2 (= a c)))))])