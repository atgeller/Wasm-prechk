#lang racket

(require redex "Satisfies.rkt" "IndexTypes.rkt")

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
  #:contract (⊢ C (e ...) tfi)
  
  [-------------------------------------------------------
   (⊢ C ((t const c)) ((() φ) -> (((t a)) (φ (eq a c)))))]

  [(where/error #t (satisfies φ (empty (ne a_2 0))))
   -------------------------------------------------
   (⊢ C ((t div/unsafe)) ((((t a_1) (t a_2)) φ) -> (((t a_3)) (φ (eq a_3 (div a_1 a_2))))))]
  
  [(where (binop_!_1 binop_!_1) (binop div/unsafe))
   ------------------------------------------------
   (⊢ C ((t binop)) ((((t a_1) (t a_2)) φ) -> (((t a_3)) (φ (eq a_3 (binop a_1 a_2))))))]

  [---------------------------------------------------------------------------------------
   (⊢ C ((t testop)) ((((t a)) φ) -> (((t a_2)) (φ (and (and (testop a) (eq a_2 1))
                                                        (and (not (testop a)) (eq a_2 0)))))))]

  [-----------------------------------------------------------------------------------------------------
   (⊢ C ((t relop)) ((((t a_1) (t a_2)) φ) -> (((t a_3)) (φ (and (and (relop a_1 a_2) (eq a_3 1))
                                                                 (and (not (relop a_1 a_2)) (eq a_3 0)))))))]

  [(label-types (ticond ...) (j) ((ti ...) φ))
   ;(where #t (satisfies (φ (not (eqz a))) φ_2))
   (where #t (satisfies φ_1 φ))
   ----------------------------
   (⊢ (_ _ _ _ _ (label (ticond  ...)) _) ((br-if j)) (((ti ... (t a)) φ_1) -> ((ti ...) (φ_1 (eqz a)))))]

  [(label-types (ticond ...) (j) ((ti ...) φ))
   (where #t (satisfies φ_1 φ))
   ----------------------------
   (⊢ (_ _ _ _ _ (label (ticond  ...)) _) ((br j)) (((ti_1 ... ti ...) φ_1) -> ((ti_2...) φ_2)))]

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  
  [----------------------------
   (⊢ C () ((() φ) -> (() φ)))]
  
  [(⊢ C (e_1 ...) (ticond_1 -> ((ti_2 ...) φ_2)))
   (⊢ C (e_2) (((ti_2 ...) φ_3) -> ticond_3))
   (where #t (satisfies φ_2 φ_3))
   ------------------------------
   (⊢ C (e_1 ... e_2) (ticond_1 -> ticond_3))]

  [(⊢ C (e ...) (((ti_1 ...) φ_1) -> ((ti_2 ...) φ_2)))
   ----------------------------------------------------
   (⊢ C (e ...) (((ti ... ti_1 ...) φ_1) -> ((ti ... ti_2 ...) φ_2)))]

  ;; Precondition strengthening, postconditioning weakening
  ;; TODO: is this right? is this needed?
  [(⊢ C (e ...) (((ti_1 ...) φ_1) -> ((ti_2 ...) φ_3)))
   (where #t (satisfies φ_1 φ_2))
   (where #t (satisfies φ_3 φ_4))
   ------------------------------
   (⊢ C (e ...) (((ti_1 ...) φ_2) -> ((ti_2 ...) φ_4)))]
  )