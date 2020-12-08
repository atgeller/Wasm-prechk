#lang racket

(require redex
         "IndexTypes.rkt"
         "SubTyping.rkt"
         "TableValidation.rkt"
         "Utilities.rkt"
         "WASM-Redex/Utilities.rkt"
         "WASM-Redex/Bits.rkt")

(provide ⊢)

;; TODO: fresh metafunction

(define-judgment-form WASMIndexTypes
  #:contract (⊢ C (e ...) tfi)

  [(where #f (in a Γ)) ;; a fresh
   ---
   "Const"
   (⊢ C ((t const c)) ((() locals Γ φ) -> (((t a)) locals (Γ (t a)) (φ (= a (t c))))))]

  [(side-condition (satisfies Γ φ (empty (not (= a_2 (t 0))))))
   (where #f (in a_3 Γ)) ;; a_3 fresh
   ---------------------------------------------------------- "Div-Prechk"
   (⊢ C ((t (div/unsafe sx))) ((((t a_1) (t a_2)) locals Γ φ)
                               -> (((t a_3)) locals (Γ (t a_3)) (φ (= a_3 ((div sx) a_1 a_2))))))]

  [(side-condition (satisfies Γ φ (empty (not (= a_2 (t 0))))))
   (where #f (in a_3 Γ)) ;; a_3 fresh
   ---------------------------------------------------------- "Rem-Prechk"
   (⊢ C ((t (rem/unsafe sx))) ((((t a_1) (t a_2)) locals Γ φ)
                               -> (((t a_3)) locals (Γ (t a_3)) (φ (= a_3 ((rem sx) a_1 a_2))))))]

  [(where (binop_!_1 binop_!_1 binop_!_1) (binop (div/unsafe signed) (div/unsafe unsigned)))
   (where (binop_!_1 binop_!_1 binop_!_1) (binop (rem/unsafe signed) (rem/unsafe unsigned)))
   (where #f (in a_3 Γ)) ;; a_3 fresh
   ------------------------------------------------ "Binop"
   (⊢ C ((t binop)) ((((t a_1) (t a_2)) locals Γ φ)
                       -> (((t a_3)) locals (Γ (t a_3)) (φ (= a_3 (binop a_1 a_2))))))]

  [(where #f (in a_2 Γ)) ;; a_2 fresh
   --------
   "Testop"
   (⊢ C ((t testop)) ((((t a)) locals Γ φ)
                        -> (((t a_2)) locals (Γ (t a_2)) (φ (= a_2 (testop a))))))]

  [(where #f (in a_3 Γ)) ;; a_3 fresh
   -------
   "Relop"
   (⊢ C ((t relop)) ((((t a_1) (t a_2)) locals Γ φ)
                       -> (((t a_3)) locals (Γ (t a_3)) (φ (= a_3 (relop a_1 a_2))))))]

  [---
   "Unreachable"
   (⊢ C ((unreachable)) tfi)]

  [---
   "Nop"
   (⊢ C ((nop)) ((() locals Γ φ) -> (() locals Γ φ)))]

  [---
   "Drop"
   (⊢ C ((drop)) (((ti ... (t a)) locals Γ φ) -> ((ti ...) locals Γ φ)))]

  [(where #f (in a_3 Γ)) ;; a_3 fresh
   ---
   "Select"
   (⊢ C ((select)) ((((t a_1) (t a_2) (i32 a)) locals Γ φ)
                    -> (((t a_3)) locals (Γ (t a))
                                  (φ (if (= a (i32 0))
                                         (= a_3 a_2)
                                         (= a_3 a_1))))))]
  
  [(where C_2 (in-label C_1 ((ti_2 ...) locals_2 Γ_3 φ_3)))
   (⊢ C_2 (e ...) (((ti_1 ...) locals_1 Γ_2 φ_2) -> ((ti_2 ...) locals_2 Γ_4 φ_4)))
   (side-condition (satisfies Γ_1 φ_1 φ_2)) ;; Strengthen precondition outside
   (side-condition (satisfies Γ_2 φ_4 φ_3)) ;; Weaken postcondition inside
   (side-condition (equiv-gamma Γ_2 (build-gamma (merge (ti_1 ...) locals_1)))) ;; Γ_2 = ti_1 ... locals_1
   (side-condition (subset (build-gamma (domain-φ φ_2)) Γ_2)) ;; domain(φ_2) subset of Γ_2
   (where Γ_5 (union Γ_1 Γ_3))
   (where φ_5 (union φ_1 φ_3))
   --------------------------- "Block"
   (⊢ C_1 ((block (((ti_1 ...) locals_1 Γ_2 φ_2) -> ((ti_2 ...) locals_2 Γ_3 φ_3)) (e ...)))
      (((ti_1 ...) locals_1 Γ_1 φ_1) -> ((ti_2 ...) locals_2 Γ_5 φ_5)))]

  [(where C_2 (in-label C_1 ((ti_1 ...) locals_1 Γ_2 φ_2)))
   (⊢ C_2 (e ...) (((ti_1 ...) locals_1 Γ_2 φ_2) -> ((ti_2 ...) locals_2 Γ_4 φ_4)))
   (side-condition (satisfies Γ_1 φ_1 φ_2)) ;; Strengthen precondition outside
   (side-condition (satisfies Γ_2 φ_4 φ_3)) ;; Weaken postcondition inside
   (side-condition (equiv-gamma Γ_2 (build-gamma (merge (ti_1 ...) locals_1)))) ;; Γ_2 = ti_1 ... locals_1
   (side-condition (subset (build-gamma (domain-φ φ_2)) Γ_2)) ;; domain(φ_2) subset of Γ_2
   (where Γ_5 (union Γ_1 Γ_3))
   (where φ_5 (union φ_1 φ_3))
   --------------------------- "Loop"
   (⊢ C_1 ((loop (((ti_1 ...) locals_1 Γ_2 φ_2) -> ((ti_2 ...) locals_2 Γ_3 φ_3)) (e ...)))
      (((ti_1 ...) locals_1 Γ_1 φ_1) -> ((ti_2 ...) locals_2 Γ_5 φ_5)))]

  [(where C_2 (in-label C_1 ((ti_2 ...) locals_2 Γ_3 φ_3)))
   (⊢ C_2 (e_1 ...) (((ti_1 ...) locals_1 Γ_2 φ_2)
                     -> ((ti_2 ...) locals_2 Γ_4 φ_4)))
   (⊢ C_2 (e_2 ...) (((ti_1 ...) locals_1 Γ_2 φ_2)
                     -> ((ti_2 ...) locals_2 Γ_4 φ_4)))
   (side-condition (satisfies Γ_1 φ_1 φ_2)) ;; Strengthen precondition outside
   (side-condition (satisfies Γ_2 φ_4 φ_3)) ;; Weaken postcondition inside
   (side-condition (equiv-gamma Γ_2 (build-gamma (merge (ti_1 ...) locals_1)))) ;; Γ_2 = ti_1 ... locals_1
   (side-condition (subset (build-gamma (domain-φ φ_2)) Γ_2)) ;; domain(φ_2) subset of Γ_2
   (where Γ_5 (union Γ_1 Γ_3))
   (where φ_5 (union φ_1 φ_3))
   --------------------------------------------------------------------- "If"
   (⊢ C_1 ((if (((ti_1 ...) locals_1 Γ_2 φ_2) -> ((ti_2 ...) locals_2 Γ_3 φ_3)) (e_1 ...) (e_2 ...)))
      (((ti_1 ...) locals_1 Γ_1 φ_1) -> ((ti_2 ...) locals_2 Γ_5 φ_5)))]

  [(label-types (ticond ...) (j) ((ti ...) locals Γ_1 φ_1))
   -------------------------------------------------------- "Br"
   (⊢ (_ _ _ _ _ (label (ticond  ...)) _)
      ((br j))
      (((ti_1 ... ti ...) locals Γ_1 φ_1)
       -> ((ti_2 ...) locals Γ_2 φ_2)))]

  [(label-types (ticond ...) (j) ((ti ...) locals Γ_1 (φ_1 (not (= a (i32 0))))))
   ------------------------------------------------------------------------------ "Br-If"
   (⊢ (_ _ _ _ _ (label (ticond  ...)) _)
      ((br-if j))
      (((ti ... (i32 a)) locals Γ_1 φ_1)
       -> ((ti ...) locals Γ_1 (φ_1 (= a (i32 0))))))]

  [(label-types (ticond ...) (j ...) ((ti_3 ...) locals Γ_1 φ_1))
   -------------------------------------------------------------- "Br-Table"
   (⊢ ((_ _ _ _ (label (ticond ...)) _ _))
      ((br-table (j ...)))
      (((ti_1 ... ti_3 ... (i32 a)) locals Γ_1 φ_1)
       -> ((ti_2 ...) locals Γ_1 φ_2)))]

  [(side-condition (satisfies Γ_1 φ_1 φ)) ;; Strengthen precondition
   -------------------------------------- "Return"
   (⊢ (_ _ _ _ _ _ (return ((ti ...) _ _ φ)))
      ((return))
      (((ti_1 ... ti ...) locals Γ_1 φ_1) -> ticond))]

  ;; Only works if Function is internal
  ;; Justin - Actually, I think this works fine, functions imported from other contexts have to
  ;;          have a type declaration in the context that they're called from.
  ;; Adam - This is the same as in the thesis
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  [(where (((ti_1 ...) _ Γ_2 φ_2) -> ((ti_2 ...) _ Γ_3 φ_3)) (do-get (tfi ...) j))
   (side-condition (satisfies Γ_1 φ_1 φ_2)) ;; Strengthen precondition
   (where φ_4 (union φ_1 φ_3))
   (where Γ_4 (union Γ_1 Γ_3))
   --------------------------- "Call"
   (⊢ ((func (tfi ...)) _ _ _ _ _ _) ((call j))
      (((ti_1 ...) locals Γ_1 φ_1)
       -> ((ti_2 ...) locals Γ_4 φ_4)))]
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  [(side-condition (satisfies Γ_1 φ_1 φ_2)) ;; Strengthen precondition
   (where φ_4 (union φ_1 φ_3))
   (where Γ_4 (union Γ_1 Γ_3))
   --------------------------- "Call-Indirect"
   (⊢ (_ _ (table j _) _ _ _ _)
      ((call-indirect (((ti_1 ...) _ Γ_2 φ_2) -> ((ti_2 ...) _ Γ_3 φ_3))))
      (((ti_1 ... (i32 a)) locals_1 Γ_1 φ_1)
       -> ((ti_2 ...) locals_1 Γ_4 φ_4)))]
  
  [(side-condition (satisfies Γ_1 φ_1 φ_2)) ;; Strengthen precondition
   (where φ_4 (union φ_1 φ_3))
   (where Γ_4 (union Γ_1 Γ_3))
   (side-condition (valid-table-call (((ti_1 ...) () Γ_2 φ_2) -> ((ti_2 ...) () Γ_3 φ_3))
                                     a (tfi ...) Γ_1 φ_1))
   ------------------------------------------------------- "Call-Indirect-Prechk"
   (⊢ (_ _ (table (j (tfi ...))) _ _ _ _)
      ((call-indirect/unsafe (((ti_1 ...) _ Γ_2 φ_2) -> ((ti_2 ...) _ Γ_3 φ_3))))
      (((ti_1 ... (i32 a)) locals_1 Γ_1 φ_1)
       -> ((ti_2 ...) locals_1 Γ_4 φ_4)))]

  [(where t_2 (do-get (t ...) j))
   (where (t_2 a) (do-get locals j))
   (where #f (in a_2 Γ)) ;; a_2 fresh
   --------------------------------- "Get-Local"
   (⊢ (_ _ _ _ (local (t ...)) _ _)
      ((get-local j))
      ((() locals Γ φ)
       -> (((t_2 a_2)) locals (Γ (t_2 a_2)) (φ (= a_2 a)))))]

  [(where t_2 (do-get (t ...) j))
   (where locals_2 (do-set locals_1 j (t_2 a)))
   -------------------------------------------- "Set-Local"
   (⊢ (_ _ _ _ (local (t ...)) _ _)
      ((set-local j))
      ((((t_2 a)) locals_1 Γ φ)
       -> (() locals_2 Γ φ)))]

  [(where t_2 (do-get (t ...) j))
   (where locals_2 (do-set locals_1 j (t_2 a)))
   (where #f (in a_2 Γ)) ;; a_2 fresh
   ---------------------------------- "Tee-Local"
   (⊢ (_ _ _ _ (local (t ...)) _ _)
      ((tee-local j))
      ((((t_2 a)) locals_1 Γ φ)
       -> (((t_2 a_2)) locals_2 (Γ (t_2 a_2)) (φ (= a_2 a)))))]

  [(where tg_2 (do-get (tg ...) j))
   (where t_2 (erase-mut tg_2))
   (where #f (in a Γ)) ;; a_2 fresh
   ------------------- "Get-Global"
   (⊢ (_ (global (tg ...)) _ _ _ _ _ _)
      ((get-global j))
      ((() locals Γ φ)
       -> (((t_2 a)) locals (Γ (t_2 a)) φ)))]

  [(where (#t t_2) (do-get (tg ...) j))
   ------------------------------------ "Set-Global"
   (⊢ (_ (global (tg ...)) _ _ _ _ _ _)
      ((set-global j))
      ((((t_2 a)) locals Γ φ)
       -> (() locals Γ φ)))]

  [(where (_ _ _ (memory j) _ _ _) C)
   (side-condition ,(< (expt 2 (term j_1))
                       (type-width (term t))))
   (side-condition (satisfies Γ φ_1 (empty
                                     (and (= (i32 1) (le (add (add a (i32 j_2)) (i32 ,(/ (type-width (term t)) 8))) (i32 j)))
                                          (= (i32 1) (ge (add a (i32 j_2)) (i32 0)))))))
   (where #f (in a_2 Γ)) ;; a_2 fresh
   ----------------------------------------------------------------------- "Load-Prechk-1"
   (⊢ C ((t load/unsafe j_1 j_2)) ((((i32 a)) locals Γ φ_1)
                                     -> (((t a_2)) locals (Γ (t a_2)) φ_1)))]

  [(where (_ _ _ (memory j) _ _ _) C)
   (side-condition ,(< (expt 2 (term j_1))
                       (type-width (term t) (term tp))))
   (side-condition (satisfies Γ φ_1 (empty
                                     (and (= (i32 1) (le (add (add a (i32 j_2)) (i32 ,(/ (type-width (term t) (term tp)) 8))) (i32 j)))
                                          (= (i32 1) (ge (add a (i32 j_2)) (i32 0)))))))
   (where #f (in a_2 Γ)) ;; a_2 fresh
   ----------------------------------------------------------------------- "Load-Prechk-2"
   (⊢ C ((t load/unsafe (tp sz) j_1 j_2)) ((((i32 a)) locals Γ φ_1)
                                             -> (((t a_2)) locals (Γ (t a_2)) φ_1)))]

  [(where (_ _ _ (memory j) _ _ _) C)
   (side-condition ,(< (expt 2 (term j_1))
                       (type-width (term t))))
   (side-condition (satisfies Γ φ_1 (empty
                                     (and (= (i32 1) (le (add (add a (i32 j_2)) (i32 ,(/ (type-width (term t)) 8))) (i32 j)))
                                          (= (i32 1) (ge (add a (i32 j_2)) (i32 0)))))))
   ------------------------------------------------------------------------- "Store-Prechk-1"
   (⊢ C ((t store/unsafe j_1 j_2)) ((((i32 a) (t a_1)) locals Γ φ_1)
                                      -> (() locals Γ φ_1)))]

  ;; TODO: no floats yet so not included in side-condition
  [(where (_ _ _ (memory j) _ _ _) C)
   (side-condition ,(< (expt 2 (term j_1))
                       (type-width (term t) (term tp))))
   (side-condition (satisfies Γ φ_1 (empty
                                     (and (= (i32 1) (le (add (add a (i32 j_2)) (i32 ,(/ (type-width (term t) (term tp)) 8))) (i32 j)))
                                          (= (i32 1) (ge (add a (i32 j_2)) (i32 0)))))))
   ------------------------------------------------------------------------------ "Store-Prechk-2"
   (⊢ C ((t store/unsafe (tp) j_1 j_2)) ((((i32 a) (t a_1)) locals Γ φ_1)
                                           -> (() locals Γ φ_1)))]

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  [------------------------------------------ "Empty"
   (⊢ C () ((() locals Γ φ) -> (() locals Γ φ)))]

  [(⊢ C (e_1 ...) (ticond_1 -> ticond_2))
   (⊢ C (e_2) (ticond_2 -> ticond_3))
   -------------------------------------------- "Composition"
   (⊢ C (e_1 ... e_2) (ticond_1 -> ticond_3))]

  ;; Stack polymorphism
  [(⊢ C (e ...) (((ti_1 ...) locals Γ_1 φ_1)
                   -> ((ti_2 ...) locals Γ_2 φ_2)))
   ------------------------------------------------------ "Stack-Poly"
   (⊢ C (e ...) (((ti ... ti_1 ...) locals Γ_1 φ_1)
                   -> ((ti ... ti_2 ...) locals Γ_2 φ_2)))])
