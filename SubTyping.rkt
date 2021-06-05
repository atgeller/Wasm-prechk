#lang racket

(require redex
         "IndexTypes.rkt"
         "Satisfies.rkt"
         "Utilities.rkt"
         ;"WASM-Redex/Validation/Utilities.rkt"
         )

(provide satisfies <: label-types contains-all substitute-ivars)

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
  
  [(side-condition (satisfies Γ_2 φ_1 φ_2))
   (side-condition (satisfies Γ_4 φ_3 φ_4))
   (side-condition (superset Γ_2 Γ_1))
   (side-condition (superset Γ_4 Γ_3))
   (where (ti ...) locals_2)
   (side-condition (contains-all Γ_3 (ti_1 ... ti ...)))
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

(define-metafunction WASMIndexTypes
  substitute-ivars : (ti ...) locals (ti ...) locals φ -> φ
  [(substitute-ivars () () () () φ) φ]
  [(substitute-ivars () ((t ivar) ti ...) () ((t ivar_pat) ti_pat ...) φ)
   (substitute-ivars () (ti ...) () (ti_pat ...) (substitute φ ivar_pat ivar))]
  [(substitute-ivars ((t ivar) ti ...) locals ((t ivar_pat) ti_pat ...) locals_pat φ)
   (substitute-ivars (ti ...) locals (ti_pat ...) locals_pat (substitute φ ivar_pat ivar))])
