#lang racket

(require redex
         "IndexTypes.rkt"
         "SubTyping.rkt"
         "TableValidation.rkt"
         "Utilities.rkt"
         "WASM-Redex/Utilities.rkt")

(provide ⊢)

;; TODO: fresh metafunction

(define-judgment-form WASMIndexTypes
  #:contract (⊢ C (e ...) tfi)

  [(where #f (in ivar Γ)) ;; ivar fresh
   ---
   "Const"
   (⊢ C ((t const c)) ((() locals Γ φ) -> (((t ivar)) locals (Γ (t ivar)) (φ (= ivar (t c))))))]

  [(side-condition (satisfies Γ φ (empty (not (= ivar_2 (t 0))))))
   (where #f (in ivar_3 Γ)) ;; ivar_3 fresh
   ---------------------------------------------------------- "Div-S-Prechk"
   (⊢ C ((t div-s/unsafe)) ((((t ivar_1) (t ivar_2)) locals Γ φ)
                            -> (((t ivar_3)) locals (Γ (t ivar_3)) (φ (= ivar_3 (div-s ivar_1 ivar_2))))))]

  [(side-condition (satisfies Γ φ (empty (not (= ivar_2 (t 0))))))
   (where #f (in ivar_3 Γ)) ;; ivar_3 fresh
   ---------------------------------------------------------- "Div-U-Prechk"
   (⊢ C ((t div-u/unsafe)) ((((t ivar_1) (t ivar_2)) locals Γ φ)
                            -> (((t ivar_3)) locals (Γ (t ivar_3)) (φ (= ivar_3 (div-u ivar_1 ivar_2))))))]

  [(side-condition (satisfies Γ φ (empty (not (= ivar_2 (t 0))))))
   (where #f (in ivar_3 Γ)) ;; ivar_3 fresh
   ---------------------------------------------------------- "Rem-S-Prechk"
   (⊢ C ((t rem-s/unsafe)) ((((t ivar_1) (t ivar_2)) locals Γ φ)
                            -> (((t ivar_3)) locals (Γ (t ivar_3)) (φ (= ivar_3 (rem-s ivar_1 ivar_2))))))]

  [(side-condition (satisfies Γ φ (empty (not (= ivar_2 (t 0))))))
   (where #f (in ivar_3 Γ)) ;; ivar_3 fresh
   ---------------------------------------------------------- "Rem-U-Prechk"
   (⊢ C ((t rem-u/unsafe)) ((((t ivar_1) (t ivar_2)) locals Γ φ)
                            -> (((t ivar_3)) locals (Γ (t ivar_3)) (φ (= ivar_3 (rem-u ivar_1 ivar_2))))))]

  [(where (binop_!_1 binop_!_1 binop_!_1) (binop div-s/unsafe div-u/unsafe))
   (where (binop_!_1 binop_!_1 binop_!_1) (binop rem-s/unsafe rem-u/unsafe))
   (where #f (in ivar_3 Γ)) ;; ivar_3 fresh
   ------------------------------------------------ "Binop"
   (⊢ C ((t binop)) ((((t ivar_1) (t ivar_2)) locals Γ φ)
                     -> (((t ivar_3)) locals (Γ (t ivar_3)) (φ (= ivar_3 (binop ivar_1 ivar_2))))))]

  [(where #f (in ivar_2 Γ)) ;; ivar_2 fresh
   --------
   "Testop"
   (⊢ C ((t testop)) ((((t ivar)) locals Γ φ)
                      -> (((t ivar_2)) locals (Γ (t ivar_2)) (φ (= ivar_2 (testop ivar))))))]

  [(where #f (in ivar_3 Γ)) ;; ivar_3 fresh
   -------
   "Relop"
   (⊢ C ((t relop)) ((((t ivar_1) (t ivar_2)) locals Γ φ)
                     -> (((t ivar_3)) locals (Γ (t ivar_3)) (φ (= ivar_3 (relop ivar_1 ivar_2))))))]

  [---
   "Unreachable"
   (⊢ C (unreachable) tfi)]

  [---
   "Nop"
   (⊢ C (nop) ((() locals Γ φ) -> (() locals Γ φ)))]

  [---
   "Drop"
   (⊢ C (drop) (((ti ... (t ivar)) locals Γ φ) -> ((ti ...) locals Γ φ)))]

  [(where #f (in ivar_3 Γ)) ;; ivar_3 fresh
   ---
   "Select"
   (⊢ C (select) ((((t ivar_1) (t ivar_2) (i32 ivar)) locals Γ φ)
                  -> (((t ivar_3)) locals (Γ (t ivar))
                                   (φ (if (= ivar (i32 0))
                                          (= ivar_3 ivar_2)
                                          (= ivar_3 ivar_1))))))]
  
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

  [(label-types (ticond ...) (j) ((ti ...) locals Γ_1 (φ_1 (not (= ivar (i32 0))))))
   ------------------------------------------------------------------------------ "Br-If"
   (⊢ (_ _ _ _ _ (label (ticond  ...)) _)
      ((br-if j))
      (((ti ... (i32 ivar)) locals Γ_1 φ_1)
       -> ((ti ...) locals Γ_1 (φ_1 (= ivar (i32 0))))))]

  [(label-types (ticond ...) (j ...) ((ti_3 ...) locals Γ_1 φ_1))
   -------------------------------------------------------------- "Br-Table"
   (⊢ ((_ _ _ _ (label (ticond ...)) _ _))
      ((br-table (j ...)))
      (((ti_1 ... ti_3 ... (i32 ivar)) locals Γ_1 φ_1)
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
      (((ti_1 ... (i32 ivar)) locals_1 Γ_1 φ_1)
       -> ((ti_2 ...) locals_1 Γ_4 φ_4)))]
  
  [(side-condition (satisfies Γ_1 φ_1 φ_2)) ;; Strengthen precondition
   (where φ_4 (union φ_1 φ_3))
   (where Γ_4 (union Γ_1 Γ_3))
   (side-condition (valid-table-call (((ti_1 ...) () Γ_2 φ_2) -> ((ti_2 ...) () Γ_3 φ_3))
                                     ivar (tfi ...) Γ_1 φ_1))
   ------------------------------------------------------- "Call-Indirect-Prechk"
   (⊢ (_ _ (table (j (tfi ...))) _ _ _ _)
      ((call-indirect/unsafe (((ti_1 ...) _ Γ_2 φ_2) -> ((ti_2 ...) _ Γ_3 φ_3))))
      (((ti_1 ... (i32 ivar)) locals_1 Γ_1 φ_1)
       -> ((ti_2 ...) locals_1 Γ_4 φ_4)))]

  [(where t_2 (do-get (t ...) j))
   (where (t_2 ivar) (do-get locals j))
   (where #f (in ivar_2 Γ)) ;; ivar_2 fresh
   --------------------------------- "Get-Local"
   (⊢ (_ _ _ _ (local (t ...)) _ _)
      ((get-local j))
      ((() locals Γ φ)
       -> (((t_2 ivar_2)) locals (Γ (t_2 ivar_2)) (φ (= ivar_2 ivar)))))]

  [(where t_2 (do-get (t ...) j))
   (where locals_2 (do-set locals_1 j (t_2 ivar)))
   -------------------------------------------- "Set-Local"
   (⊢ (_ _ _ _ (local (t ...)) _ _)
      ((set-local j))
      ((((t_2 ivar)) locals_1 Γ φ)
       -> (() locals_2 Γ φ)))]

  [(where t_2 (do-get (t ...) j))
   (where locals_2 (do-set locals_1 j (t_2 ivar)))
   (where #f (in ivar_2 Γ)) ;; ivar_2 fresh
   ---------------------------------- "Tee-Local"
   (⊢ (_ _ _ _ (local (t ...)) _ _)
      ((tee-local j))
      ((((t_2 ivar)) locals_1 Γ φ)
       -> (((t_2 ivar_2)) locals_2 (Γ (t_2 ivar_2)) (φ (= ivar_2 ivar)))))]

  [(where tg_2 (do-get (tg ...) j))
   (where t_2 (erase-mut tg_2))
   (where #f (in ivar Γ)) ;; ivar fresh
   ------------------- "Get-Global"
   (⊢ (_ (global (tg ...)) _ _ _ _ _ _)
      ((get-global j))
      ((() locals Γ φ)
       -> (((t_2 ivar)) locals (Γ (t_2 ivar)) φ)))]

  [(where (#t t_2) (do-get (tg ...) j))
   ------------------------------------ "Set-Global"
   (⊢ (_ (global (tg ...)) _ _ _ _ _ _)
      ((set-global j))
      ((((t_2 ivar)) locals Γ φ)
       -> (() locals Γ φ)))]

  [(where (_ _ _ (memory n) _ _ _) C)
   (side-condition ,(<= (expt 2 (term a)) (/ (term (bit-width t)) 8)))
   (side-condition (satisfies Γ φ_1 (empty
                                     (and (= (i32 1) (le-u (add (add ivar (i32 o)) (i32 ,(/ (term (bit-width t)) 8))) (i32 n)))
                                          (= (i32 1) (ge-u (add ivar (i32 o)) (i32 0)))))))
   (where #f (in ivar_2 Γ)) ;; ivar_2 fresh
   ----------------------------------------------------------------------- "Load-Prechk"
   (⊢ C ((t load/unsafe a o)) ((((i32 ivar)) locals Γ φ_1)
                                     -> (((t ivar_2)) locals (Γ (t ivar_2)) φ_1)))]

  [(where (_ _ _ (memory n) _ _ _) C)
   (side-condition ,(<= (expt 2 (term a)) (/ (term (packed-bit-width tp)) 8)))
   (side-condition ,(< (term (packed-bit-width tp)) (term (bit-width t))))
   (side-condition (satisfies Γ φ_1 (empty
                                     (and (= (i32 1) (le-u (add (add ivar (i32 o)) (i32 ,(/ (term (packed-bit-width tp)) 8))) (i32 n)))
                                          (= (i32 1) (ge-u (add ivar (i32 o)) (i32 0)))))))
   (where inn t)
   (where #f (in ivar_2 Γ)) ;; ivar_2 fresh
   ----------------------------------------------------------------------- "Load-Packed-Prechk"
   (⊢ C ((t load/unsafe (tp sz) a o)) ((((i32 ivar)) locals Γ φ_1)
                                           -> (((t ivar_2)) locals (Γ (t ivar_2)) φ_1)))]

  [(where (_ _ _ (memory n) _ _ _) C)
   (side-condition ,(<= (expt 2 (term a)) (/ (term (bit-width t)) 8)))
   (side-condition (satisfies Γ φ_1 (empty
                                     (and (= (i32 1) (le-u (add (add ivar (i32 o)) (i32 ,(/ (term (bit-width t)) 8))) (i32 n)))
                                          (= (i32 1) (ge-u (add ivar (i32 o)) (i32 0)))))))
   ------------------------------------------------------------------------- "Store-Prechk"
   (⊢ C ((t store/unsafe a o)) ((((i32 ivar) (t ivar_1)) locals Γ φ_1)
                                    -> (() locals Γ φ_1)))]

  [(where (_ _ _ (memory n) _ _ _) C)
   (side-condition ,(<= (expt 2 (term a)) (/ (term (packed-bit-width tp)) 8)))
   (side-condition ,(< (term (packed-bit-width tp)) (term (bit-width t))))
   (side-condition (satisfies Γ φ_1 (empty
                                     (and (= (i32 1) (le-u (add (add ivar (i32 o)) (i32 ,(/ (term (packed-bit-width tp)) 8))) (i32 n)))
                                          (= (i32 1) (ge-u (add ivar (i32 o)) (i32 0)))))))
   (where inn t)
   ------------------------------------------------------------------------------ "Store-Packed-Prechk"
   (⊢ C ((t store/unsafe tp a o)) ((((i32 ivar) (t ivar_1)) locals Γ φ_1)
                                   -> (() locals Γ φ_1)))]
  
  [(where n (context-memory C))
   (side-condition ,(<= (expt 2 (term a)) (/ (term (bit-width t)) 8)))
   ------------------------------------------------------------- "Load"
   (⊢ C ((t load a o)) ((i32) -> (t)))]

  [(where n (context-memory C))
   (side-condition ,(<= (expt 2 (term a)) (/ (term (packed-bit-width tp)) 8)))
   (side-condition ,(< (term (packed-bit-width tp)) (term (bit-width t))))
   (where inn t)
   ----------------------------------------------------------------------- "Load-Packed"
   (⊢ C ((t load (tp sx) a o)) ((i32) -> (t)))]

  [(where n (context-memory C))
   (side-condition ,(<= (expt 2 (term a)) (/ (term (bit-width t)) 8)))
   ------------------------------------------------------------- "Store"
   (⊢ C ((t store a o)) ((i32 t) -> ()))]

  [(where n (context-memory C))
   (side-condition ,(<= (expt 2 (term a)) (/ (term (packed-bit-width tp)) 8)))
   (side-condition ,(< (term (packed-bit-width tp)) (term (bit-width t))))
   (where inn t)
   ----------------------------------------------------------------------- "Store-Packed"
   (⊢ C ((t store tp a o)) ((i32 t) -> ()))]

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
