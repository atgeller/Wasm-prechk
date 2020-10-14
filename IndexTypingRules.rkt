#lang racket

(require redex
         "IndexTypes.rkt"
         "SubTyping.rkt"
         "TableValidation.rkt"
         "Utilities.rkt"
         "WASM-Redex/Utilities.rkt"
         "WASM-Redex/Bits.rkt")

(provide ⊢)

(define-judgment-form WASMIndexTypes
  #:contract (⊢ C (e ...) tfi)

  [;; a fresh
   ----------
   "Const"
   (⊢ C ((t const c)) ((() locals φ)
                         -> (((t a)) locals ((φ (t a)) (= a (t c))))))]

  [(side-condition (satisfies φ (empty (not (= a_2 (i32 0))))))
   ;; a_3 fresh
   ------------------------------------------------------- "Div-Prechk"
   (⊢ C ((t div/unsafe)) ((((t a_1) (t a_2)) locals φ)
                            -> (((t a_3)) locals ((φ (t a_3)) (= a_3 (div a_1 a_2))))))]

  [(where (binop_!_1 binop_!_1) (binop div/unsafe))
   ;; a_3 fresh
   ------------------------------------------------ "Binop"
   (⊢ C ((t binop)) ((((t a_1) (t a_2)) locals φ)
                       -> (((t a_3)) locals ((φ (t a_3)) (= a_3 (binop a_1 a_2))))))]

  [;; a_2 fresh
   ------------
   "Testop"
   (⊢ C ((t testop)) ((((t a)) locals φ)
                        -> (((t a_2)) locals
                                    ((φ (t a_2)) (= a_2 (testop a))))))]

  [;; a_3 fresh
   ------------
   "Relop"
   (⊢ C ((t relop)) ((((t a_1) (t a_2)) locals φ)
                       -> (((t a_3)) locals
                                     ((φ (t a_3)) (= a_3 (relop a_1 a_2))))))]

  [---
   "Unreachable"
   (⊢ C ((unreachable)) tfi)]

  [---
   "Nop"
   (⊢ C ((nop)) ((() locals φ) -> (() locals φ)))]

  [---
   "Drop"
   (⊢ C ((drop)) (((ti ... (t a)) locals φ) -> ((ti ...) locals φ)))]

  [---
   "Select"
   (⊢ C ((select)) ((((t a_1) (t a_2) (i32 a)) locals φ)
                    -> (((t a_3)) locals
                                  ((φ (t a_3)) (if (= a (i32 0))
                                                   (eq a_3 a_2)
                                                   (eq a_3 a_1))))))]
  
  [(where C_2 (in-label C_1 ticond_2))
   (⊢ C_2 (e ...) (ticond_1 -> ticond_2))
   -------------------------------------- "Block"
   (⊢ C_1 ((block (ticond_1 -> ticond_2) (e ...))) (ticond_1 -> ticond_2))]

  [(where C_2 (in-label C_1 ticond_1))
   (⊢ C_2 (e ...) (ticond_1 -> ticond_2))
   -------------------------------------- "Loop"
   (⊢ C_1 ((loop (ticond_1 -> ticond_2) (e ...))) (ticond_1 -> ticond_2))]

  [(where C_2 (in-label C_1 ticond_2))
   (⊢ C_2 (e_1 ...) (((ti_1 ...) locals_1 (φ_1 (not (= a (i32 0))))) -> ticond_2))
   (⊢ C_2 (e_2 ...) (((ti_1 ...) locals_1 (φ_1 (= a (i32 0)))) -> ticond_2))
   ------------------------------------------------------------------------- "If"
   (⊢ C_1 ((if (((ti_1 ...) locals_1 φ_1) -> ticond_2) (e_1 ...) (e_2 ...)))
      (((ti_1 ... (i32 a)) locals_1 φ_1) -> ticond_2))]

  [(label-types (ticond ...) (j) ((ti ...) φ_1))
   --------------------------------------------- "Br"
   (⊢ (_ _ _ _ _ (label (ticond  ...)) _)
      ((br j))
      (((ti_1 ... ti ...) locals φ_1)
       -> ((ti_2 ...) locals φ_2)))]

  [(label-types (ticond ...) (j) ((ti ...) φ_1))
   --------------------------------------------- "Br-If"
   (⊢ (_ _ _ _ _ (label (ticond  ...)) _)
      ((br-if j))
      (((ti ... (i32 a)) locals φ_1)
       -> ((ti ...) locals (φ_1 (= a (i32 0))))))]

  [(label-types (ticond ...) (j ...) ((ti_3 ...) φ_1))
   --------------------------------------------------- "Br-Tabel"
   (⊢ ((_ _ _ _ (label (ticond ...)) _ _))
      ((br-table (j ...)))
      (((ti_1 ... ti_3 ... (i32 a)) locals φ_1)
       -> ((ti_2 ...) locals φ_2)))]

  [(side-condition (satisfies φ_1 φ))
   ---------------------------------- "Return"
   (⊢ (_ _ _ _ _ _ (return ((ti ...) _ φ)))
      ((return))
      (((ti_1 ... ti ...) locals φ_1)
       -> ticond))]

  ;; Only works if Function is internal
  ;; Justin - Actually, I think this works fine, functions imported from other contexts have to
  ;;          have a type declaration in the context that they're called from.
  ;; Adam - This is the same as in the thesis
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  [(where (((ti_1 ...) _ φ_1) -> ((ti_2 ...) _ φ_2)) (do-get (tfi ...) j))
   (where φ_3 (extend φ_1 φ_2))
   ---------------------------- "Call"
   (⊢ ((func (tfi ...)) _ _ _ _ _ _) ((call j))
      (((ti_1 ...) locals φ_1)
       -> ((ti_2 ...) locals φ_3)))]
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  [(where (((ti_1 ...) _ φ_1)
           -> ((ti_2 ...) _ φ_2)) tfi)
   (where φ_3 (extend φ_1 φ_2))
   ---------------------------- "Call-Indirect"
   (⊢ (_ _ (table j _) _ _ _ _)
      ((call-indirect tfi))
      (((ti_1 ... (i32 a)) locals_1 φ_1)
       -> ((ti_2 ...) locals_1 φ_3)))]
  
  [(where (((ti_1 ...) _ φ_1) -> ((ti_2 ...) _ φ_2)) tfi_2)
   (where φ_3 (extend φ_1 φ_2))
   (side-condition (valid-table-call tfi_2 a (tfi ...) φ_1))
   --------------------------------------------------------- "Call-Indirect-Prechk"
   (⊢ (_ _ (table (j (tfi ...))) _ _ _ _)
      ((call-indirect/unsafe tfi_2))
      (((ti_1 ... (i32 a)) locals_1 φ_1)
       -> ((ti_2 ...) locals_1 φ_3)))]

  [(where t_2 (do-get (t ...) j))
   (where (t_2 a) (do-get locals j))
   ;; a_2 fresh
   --------------------------------- "Get-Local"
   (⊢ (_ _ _ _ (local (t ...)) _ _)
      ((get-local j))
      ((() locals φ)
       -> (((t_2 a_2)) locals ((φ (t_2 a_2)) (= a_2 a)))))]

  [(where t_2 (do-get (t ...) j))
   (where locals_2 (do-set locals_1 j (t_2 a)))
   -------------------------------------------- "Set-Local"
   (⊢ (_ _ _ _ (local (t ...)) _ _)
      ((set-local j))
      ((((t_2 a)) locals_1 φ)
       -> (() locals_2 φ)))]

  [(where t_2 (do-get (t ...) j))
   (where locals_2 (do-set locals_1 j (t_2 a)))
   ;; a_2 fresh
   -------------------------------------------- "Tee-Local"
   (⊢ (_ _ _ _ (local (t ...)) _ _)
      ((tee-local j))
      ((((t_2 a)) locals_1 φ)
       -> (((t_2 a_2)) locals_2 ((φ (t_2 a_2)) (= a_2 a)))))]

  [(where tg_2 (do-get (tg ...) j))
   (where t_2 (erase-mut tg_2))
   ---------------------------- "Get-Global"
   (⊢ (_ (global (tg ...)) _ _ _ _ _ _)
      ((get-global j))
      ((() locals φ)
       -> (((t_2 a_2)) locals (φ (t_2 a_2)))))]

  [(where (#t t_2) (do-get (tg ...) j))
   ------------------------------------------------ "Set-Global"
   (⊢ (_ (global (tg ...)) _ _ _ _ _ _)
      ((set-global j))
      ((((t_2 a)) locals φ)
       -> (() locals (φ (t_2 a_2)))))]

  [(where (_ _ _ (memory j) _ _ _) C)
   (side-condition ,(< (expt 2 (term j_1))
                       (type-width (term t))))
   (side-condition (satisfies φ_1 ((empty (i32 a))
                                   (and (= (i32 1) (le (add (add a (i32 j_2)) (i32 ,(/ (type-width (term t)) 8))) (i32 j)))
                                        (= (i32 1) (ge (add a (i32 j_2)) (i32 0)))))))
   ;; a_2 fresh
   ----------------------------------------------------------------------- "Load-Prechk-1"
   (⊢ C ((t load/unsafe j_1 j_2)) ((((i32 a)) locals φ_1)
                                     -> (((t a_2)) locals (φ_1 (t a_2)))))]

  [(where (_ _ _ (memory j) _ _ _) C)
   (side-condition ,(< (expt 2 (term j_1))
                       (type-width (term t) (term tp))))
   (side-condition (satisfies φ_1 ((empty (i32 a))
                                   (and (= (i32 1) (le (add (add a (i32 j_2)) (i32 ,(/ (type-width (term t) (term tp)) 8))) (i32 j)))
                                        (= (i32 1) (ge (add a (i32 j_2)) (i32 0)))))))
   ;; a_2 fresh
   ----------------------------------------------------------------------- "Load-Prechk-2"
   (⊢ C ((t load/unsafe (tp sz) j_1 j_2)) ((((i32 a)) locals φ_1)
                                             -> (((t a_2)) locals (φ_1 (t a_2)))))]

  [(where (_ _ _ (memory j) _ _ _) C)
   (side-condition ,(< (expt 2 (term j_1))
                       (type-width (term t))))
   (side-condition (satisfies φ_1 ((empty (i32 a))
                                   (and (= (i32 1) (le (add (add a (i32 j_2)) (i32 ,(/ (type-width (term t)) 8))) (i32 j)))
                                        (= (i32 1) (ge (add a (i32 j_2)) (i32 0)))))))
   ------------------------------------------------------------------------- "Store-Prechk-1"
   (⊢ C ((t store/unsafe j_1 j_2)) ((((i32 a) (t a_1)) locals φ_1)
                                      -> (() locals φ_1)))]

  ;; TODO: no floats yet so not included in side-condition
  [(where (_ _ _ (memory j) _ _ _) C)
   (side-condition ,(< (expt 2 (term j_1))
                       (type-width (term t) (term tp))))
   (side-condition (satisfies φ_1 ((empty (i32 a))
                                   (and (= (i32 1) (le (add (add a (i32 j_2)) (i32 ,(/ (type-width (term t) (term tp)) 8))) (i32 j)))
                                        (= (i32 1) (ge (add a (i32 j_2)) (i32 0)))))))
   ------------------------------------------------------------------------------ "Store-Prechk-2"
   (⊢ C ((t store/unsafe (tp) j_1 j_2)) ((((i32 a) (t a_1)) locals φ_1)
                                           -> (() locals φ_1)))]

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  [------------------------------------------ "Empty"
   (⊢ C () ((() locals φ) -> (() locals φ)))]

  [(⊢ C (e_1 ...) (ticond_1 -> ticond_2))
   (⊢ C (e_2) (ticond_2 -> ticond_3))
   -------------------------------------------- "Composition"
   (⊢ C (e_1 ... e_2) (ticond_1 -> ticond_3))]

  ;; Stack polymorphism
  [(⊢ C (e ...) (((ti_1 ...) locals φ_1)
                   -> ((ti_2 ...) locals φ_2)))
   ------------------------------------------------------ "Stack-Poly"
   (⊢ C (e ...) (((ti ... ti_1 ...) locals φ_1)
                   -> ((ti ... ti_2 ...) locals φ_2)))]

  ;; Subtyping
  [(⊢ C (e ...) tfi_2)
   (<: tfi_1 tfi_2)
   ---------------- "Subtyping"
   (⊢ C (e ...) tfi_1)])
