#lang racket

(require redex "Satisfies.rkt" "IndexTypes.rkt" "SubTyping.rkt" "TableValidation.rkt")

(provide ⊢)

(define-metafunction WASMIndexTypes
  valid-table-call : tfi a (i ...) (tfi ...) φ -> boolean
  [(valid-table-call tfi a (i ...) (tfi_2 ...) φ)
   ,(check-table-call (term tfi) (term a) (term (i ...)) (term (tfi_2 ...)) (term φ))])

(define-judgment-form WASMIndexTypes
  #:contract (⊢ C (e ...) tfi)
  
  [-------------------------------------------------------------------
   (⊢ C ((t const c)) ((() φ) -> (((t a)) ((φ (t a)) (eq a (t c))))))]

  [(where/error #t (satisfies φ (empty (ne a_2 (i32 0)))))
   -------------------------------------------------------
   (⊢ C ((t div/unsafe)) ((((t a_1) (t a_2)) φ) -> (((t a_3)) ((φ (t a_3)) (eq a_3 (div a_1 a_2))))))]
  
  [(where (binop_!_1 binop_!_1) (binop div/unsafe))
   ------------------------------------------------
   (⊢ C ((t binop)) ((((t a_1) (t a_2)) φ) -> (((t a_3)) ((φ (t a_3)) (eq a_3 (binop a_1 a_2))))))]

  [------------------------------------------------------------------------------------------
   (⊢ C ((t testop)) ((((t a)) φ) -> (((t a_2)) ((φ (t a_2)) (and (and (testop a) (eq a_2 1))
                                                                    (and (not (testop a)) (eq a_2 0)))))))]

  [--------------------------------------------------------------------------------------------------------
   (⊢ C ((t relop)) ((((t a_1) (t a_2)) φ) -> (((t a_3)) ((φ (t a_3)) (and (and (relop a_1 a_2) (eq a_3 1))
                                                                             (and (not (relop a_1 a_2)) (eq a_3 0)))))))]

  [--------------------------
   (⊢ C ((unreachable)) tfi)]

  [---------------------------------
   (⊢ C ((nop)) ((() φ) -> (() φ)))]

  [----------------------------------------------------
   (⊢ C ((drop)) (((ti ... (t a)) φ) -> ((ti ...) φ)))]

  [---------------------------------------------------------------------------------------------------------
   (⊢ C ((select)) ((((t a_1) (t a_2) (i32 c)) φ) -> (((t a_3)) ((φ (t a_3)) (and (and (eqz c) (eq a_3 a_1))
                                                                                    (and (not (eqz c)) (eq a_3 a_2)))))))]

  [(where (ticond_1 -> ticond_2) tfi)
   (where C_2 (in-label C_1 ticond_2))
   (⊢ C_2 (e ...) tfi)
   --------------------
   (⊢ C_1 ((block tfi (e ...))) tfi)]

  [(where (ticond_1 -> ticond_2) tfi)
   (where C_2 (in-label C_1 ticond_1))
   (⊢ C_2 (e ...) tfi)
   --------------------
   (⊢ C_1 ((loop tfi (e ...))) tfi)]

  [(where (((ti_1 ...) φ_2) -> ((ti_2 ...) φ_5)) tfi)
   (where C_2 (in-label C_1 ((ti_2 ...) φ_2)))
   (where #t (satisfies φ_1 φ_2))
   (⊢ C_2 (e_1 ...) (((ti_1 ...) (φ_2 (neq a (i32 0)))) -> ((ti_2 ...) φ_3)))
   (⊢ C_2 (e_2 ...) (((ti_1 ...) (φ_2 (eqz a))) -> ((ti_2 ...) φ_4)))
   (where #t (satisfies φ_3 φ_5))
   (where #t (satisfies φ_4 φ_5))
   ------------------------------
   (⊢ C_1 ((if tfi (e_1 ...) (e_2 ...))) (((ti_1 ... (i32 a)) φ_1) -> ((ti_2 ...) φ_5)))]

  [(label-types (ticond ...) (j) ((ti ...) φ))
   (where #t (satisfies φ_1 φ))
   ----------------------------
   (⊢ (_ _ _ _ _ (label (ticond  ...)) _) ((br j)) (((ti_1 ... ti ...) φ_1) -> ((ti_2 ...) φ_2)))]

  [(label-types (ticond ...) (j) ((ti ...) φ))
   (where #t (satisfies φ_1 φ))
   ----------------------------
   (⊢ (_ _ _ _ _ (label (ticond  ...)) _) ((br-if j)) (((ti ... (t a)) φ_1) -> ((ti ...) (φ_1 (eqz a)))))]

  ;; TODO: fix label-types :)
  #;[(label-types (ticond ...) (j ...) ((ti_3 ...) φ))
   (where #t (satisfies φ_1 φ))
   ----------------------------
   (⊢ ((_ _ _ _ (label (ticond ...)) _ _)) ((br-table (j ...))) (((ti_1 ... ti_3 ... (i32 a)) φ_1) -> ((ti_2 ...) φ_2)))]
  
  [(where #t (satisfies φ_1 φ))
   ----------------------------
   (⊢ (_ _ _ _ _ _ (return ((ti ...) φ))) ((return)) (((ti_1 ... ti ...) φ_1) -> ((ti_2 ...) φ_2)))]

  [(where tfi_2 (do-get (tfi ...) j))
   ----------------------------------
   (⊢ ((func (tfi ...)) _ _ _ _ _ _) ((call j)) tfi_2)]

  [(where (((ti_1 ...) φ_2) -> ((ti_2 ...) φ_3)) tfi)
   (where #t (satisfies (ti_1 ...) φ_1 φ_2))
   -----------------------------------------
   (⊢ (_ _ (table j _) _ _ _ _) ((call-indirect tfi)) (((ti_1 ... (i32 a)) φ_1) -> ((ti_2 ...) φ_3)))]
  
  [(where (((ti_1 ...) φ_2) -> ((ti_2 ...) φ_3)) tfi_2)
   (where #t (satisfies φ_1 φ_2))
   (where #t (valid-table-call tfi_2 a (i ...) (tfi ...) φ_1))
   -----------------------------------------------------------
   (⊢ ((func (tfi ...)) _ (table (j (i ...))) _ _ _ _) ((call-indirect/unsafe tfi_2)) (((ti_1 ... (i32 a)) φ_1) -> ((ti_2 ...) φ_3)))]

  [(where (t a) (do-get (ti ...) j))
   ---------------------------------
   (⊢ (_ _ _ _ (local (ti ...)) _ _) ((get-local j)) ((() φ) -> ((t b) (φ (eq a b)))))]

  [(where (t a) (do-get (ti ...) j))
   ---------------------------------
   (⊢ (_ _ _ _ (local (ti ...)) _ _) ((set-local j)) (((t b) φ) -> (() (φ (eq a b)))))]

  [(where (t _) (do-get (ti ...) j))
   ------------------------------
   (⊢ (_ _ _ _ (local (ti ...)) _ _) ((tee-local j)) (((t b) φ) -> ((t b) (φ (eq a b)))))]

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

  ;; Subtyping
  [(⊢ C (e ...) tfi_2)
   (<: tfi_1 tfi_2)
   ---------------
   (⊢ C (e ...) tfi_1)])
