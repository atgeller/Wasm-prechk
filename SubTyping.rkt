#lang racket

(require redex
         "IndexTypes.rkt"
         "Satisfies.rkt"
         "Utilities.rkt")

(provide satisfies <: label-types)

;; Ensures index type context φ_1 satisfies φ_2
(define-metafunction WASMIndexTypes
  satisfies : Γ φ_1 φ_2 -> boolean
  [(satisfies empty φ_1 φ_2) #t]
  [(satisfies Γ φ φ) #t]
  [(satisfies Γ φ empty) #t]
  [(satisfies Γ φ_1 φ_2) ,(test-satisfaction (term Γ) (term φ_1) (term φ_2))])

(define-metafunction WASMIndexTypes
  contains-all : any (any ...) -> boolean
  [(contains-all any ()) #t]
  [(contains-all any (any_1 any_2 ...)) (contains-all any (any_2 ...)) (where #t (in any_1 any))]
  [(contains-all any (any_1 any_2 ...)) #f (where #f (in any_1 any))])

(define-judgment-form WASMIndexTypes
  #:contract (<: tfi tfi)
  #:mode (<: I I)
  
  [(side-condition (satisfies Γ_2 φ_1 φ_2))
   (side-condition (satisfies Γ_4 φ_3 φ_4))
   (side-condition (superset Γ_2 Γ_1))
   (side-condition (superset Γ_4 Γ_3))
   (where (ti ...) locals_2)
   (side-condition (contains-all (ti_1 ... ti ...) Γ_3))
   -----------------------------------------------------
   (<: (((ti_1 ...) locals_1 Γ_2 φ_2)
        -> ((ti_2 ...) locals_2 Γ_3 φ_3))
       (((ti_1 ...) locals_1 Γ_1 φ_1)
        -> ((ti_2 ...) locals_2 Γ_4 φ_4)))])

(define-judgment-form WASMIndexTypes
  #:contract (label-types (ticond ...) (j ...) ticond)
  #:mode (label-types I I I)

  [(label-types (ticond ...) () ticond_3)]

  [(where ((ti_1 ...) locals_1 _ φ_2) (reverse-get (ticond ...) j))
   (side-condition (satisfies Γ_1 φ_1 φ_2))
   (label-types (ticond ...) (j_2 ...) ((ti_1 ...) locals_1 Γ_1 φ_1))
   ------------------------------------------------------------------
   (label-types (ticond ...) (j j_2 ...) ((ti_1 ...) locals_1 Γ_1 φ_1))])
