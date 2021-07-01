#lang racket

(require redex
         "IndexTypes.rkt"
         "Satisfies.rkt"
         "Utilities.rkt"
         ;"WASM-Redex/Validation/Utilities.rkt"
         )

(provide satisfies satisfies-all all-satisfies <: contains-all substitute-ivars)

;; Ensures index type context φ_1 satisfies φ_2
(define-metafunction WASMIndexTypes
  satisfies : Γ φ φ -> boolean
  [(satisfies empty φ_1 φ_2) #t]
  [(satisfies Γ φ φ) #t]
  [(satisfies Γ φ empty) #t]
  [(satisfies Γ φ_1 φ_2) ,(test-satisfaction (term Γ) (term φ_1) (term φ_2))])

(define-metafunction WASMIndexTypes
  satisfies-all : Γ φ (φ ...) -> boolean
  [(satisfies-all Γ φ_1 ()) #t]
  [(satisfies-all Γ φ_1 (φ φ_2 ...))
   (satisfies-all Γ φ_1 (φ_2 ...))
   (side-condition (term (satisfies Γ φ_1 φ)))
   or
   #f])

(define-metafunction WASMIndexTypes
  all-satisfies : (Γ ...) (φ ...) φ -> boolean
  [(all-satisfies Γ () φ_2) #t]
  [(all-satisfies Γ (φ φ_1 ...) φ_2)
   (all-satisfies Γ (φ_1 ...) φ_2)
   (side-condition (term (satisfies Γ φ φ_2)))
   or
   #f])

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

(define-metafunction WASMIndexTypes
  substitute-ivars-xy : (ivar ivar) ... x -> x
  [(substitute-ivars-xy (ivar_1 ivar_2) ... ivar) ivar (where (ivar_!_ ...) (ivar_2 ... ivar))]
  [(substitute-ivars-xy (ivar_1 ivar_2) ... (ivar_new ivar) (ivar_3 ivar_4) ... ivar) ivar_new]
  [(substitute-ivars-xy (ivar_1 ivar_2) ... (t c)) (t c)]
  [(substitute-ivars-xy (ivar_1 ivar_2) ... ((t binop) x y))
   ((t binop) (substitute-ivars-xy (ivar_1 ivar_2) ... x)
              (substitute-ivars-xy (ivar_1 ivar_2) ... y))]
  [(substitute-ivars-xy (ivar_1 ivar_2) ... ((t testop) x))
   ((t testop) (substitute-ivars-xy (ivar_1 ivar_2) ... x))]
  [(substitute-ivars-xy (ivar_1 ivar_2) ... ((t relop) x y))
   ((t relop) (substitute-ivars-xy (ivar_1 ivar_2) ... x)
              (substitute-ivars-xy (ivar_1 ivar_2) ... y))]
  [(substitute-ivars-xy (ivar_1 ivar_2) ... ((t cvtop t) x))
   ((t cvtop t) (substitute-ivars-xy (ivar_1 ivar_2) ... x))]
  [(substitute-ivars-xy (ivar_1 ivar_2) ... ((t cvtop t sx) x))
   ((t cvtop t sx) (substitute-ivars-xy (ivar_1 ivar_2) ... x))])

(define-metafunction WASMIndexTypes
  substitute-ivars-P : (ivar ivar) ... P -> P
  [(substitute-ivars-P (ivar_1 ivar_2) ... (= x y))
   (= (substitute-ivars-xy (ivar_1 ivar_2) ... x)
      (substitute-ivars-xy (ivar_1 ivar_2) ... y))]
  [(substitute-ivars-P (ivar_1 ivar_2) ... (if P_p P_t P_e))
   (if (substitute-ivars-P (ivar_1 ivar_2) ... P_p)
       (substitute-ivars-P (ivar_1 ivar_2) ... P_t)
       (substitute-ivars-P (ivar_1 ivar_2) ... P_e))]
  [(substitute-ivars-P (ivar_1 ivar_2) ... (not P))
   (not (substitute-ivars-P (ivar_1 ivar_2) ... P))]
  [(substitute-ivars-P (ivar_1 ivar_2) ... (and P_1 P_2))
   (and (substitute-ivars-P (ivar_1 ivar_2) ... P_1)
        (substitute-ivars-P (ivar_1 ivar_2) ... P_2))]
  [(substitute-ivars-P (ivar_1 ivar_2) ... (or P_1 P_2))
   (or (substitute-ivars-P (ivar_1 ivar_2) ... P_1)
       (substitute-ivars-P (ivar_1 ivar_2) ... P_2))]
  [(substitute-ivars-P (ivar_1 ivar_2) ... ⊥) ⊥])

(define-metafunction WASMIndexTypes
  substitute-ivars : (ivar ivar) ... φ -> φ
  [(substitute-ivars (ivar_1 ivar_2) ... empty) empty]
  [(substitute-ivars (ivar_1 ivar_2) ... (φ P))
   ((substitute-ivars (ivar_1 ivar_2) ... φ) (substitute-ivars-P (ivar_1 ivar_2) ... P))])
