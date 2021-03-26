#lang racket

(require redex
         "IndexTypes.rkt"
         "SubTyping.rkt"
         "IndexTypingRules.rkt"
         "IndexModuleTyping.rkt"
         "Utilities.rkt"
         "WASM-Redex/Utilities.rkt")

(define-extended-language WASMPrechkWithAdmin WASMIndexTypes
  (v ::= (t const c))
  (cl ::= (i f))
  (e ::= .... trap (call cl)
     (label n (e ...) (e ...)) (local n (i (v ...)) (e ...)))

  (S ::= ((C ...) (table ((j (tfi ...)) ...)) (memory (j ...))))

  (inst ::= ((cl ...) (v ...) (table (j tfi ...) ...) (memory j ...)))
  (tabinst ::= (cl ...))
  (meminst ::= bstr)

  (bstr ::= (side-condition any_1 (bytes? (term any_1))))
  
  (s ::= ((inst ...) (tabinst ...) (meminst ...))))

(define-judgment-form WASMPrechkWithAdmin
  #:contract (⊢-cl S cl tfi)

  [(where ((C ...) _ _) S)
   (where C_2 (do-get (C ...) i))
   (⊢-module-func C_2 f (_ tfi))
   -----------------------------
   (⊢-cl S (i f) tfi)])

(define-judgment-form WASMPrechkWithAdmin
  #:contract (⊢-cl-list S (cl ...) (tfi ...))

  [--------------------
   (⊢-cl-list S () ())]

  [(⊢-cl-list S (cl ...) (tfi ...))
   (⊢-cl S cl_2 tfi_2)
   -------------------
   (⊢-cl-list S (cl_2 cl ...) (tfi_2 tfi ...))])

(define-judgment-form WASMPrechkWithAdmin
  #:contract (⊢-inst S inst C)

  [(⊢-cl-list S (cl ...) (tfi ...))
   (where ((C ...) (tab ((j_1 (tfi_1 ...)) ...)) (mem (j_2 ...))) S)
   (where (j_3 (tfi_3 ...)) (do-get ((j_1 (tfi_1 ...)) ...) j))
   (where j_4 (do-get (j_2 ...) i))
   --------------------------------
   (⊢-inst S ((cl ...) ((t const c) ...) (table j) (memory i))
           ((func (tfi ...)) (glob ((_ t) ...)) (table (j_3 (tfi_3 ...))) (memory j_4) _ _ _))]

  [(⊢-cl-list S (cl ...) (tfi ...))
   (where (_ (tab ((j_1 (tfi_1 ...)) ...)) _) S)
   (where (j_3 (tfi_3 ...)) (do-get ((j_1 (tfi_1 ...)) ...) j))
   --------------------------------------------------------
   (⊢-inst S ((cl ...) ((t const c) ...) (table j) (memory))
           ((func (tfi ...)) (glob ((_ t) ...)) (table (j_3 (tfi_3 ...))) (memory) _ _ _))]

  [(⊢-cl-list S (cl ...) (tfi ...))
   (where (_ _ (mem (j_2 ...))) S)
   (where j_4 (do-get (j_2 ...) i))
   --------------------------------
   (⊢-inst S ((cl ...) ((t const c) ...) (table) (memory i))
           ((func (tfi ...)) (glob ((_ t) ...)) (table) (memory j_4) _ _ _))]

  [(⊢-cl-list S (cl ...) (tfi ...))
   --------------------------------
   (⊢-inst S ((cl ...) ((t const c) ...) (table) (memory))
           ((func (tfi ...)) (glob ((_ t) ...)) (table) (memory) _ _ _))])

(define-judgment-form WASMPrechkWithAdmin
  #:contract (⊢-inst-list S (inst ...) (C ...))

  [----------------------
   (⊢-inst-list S () ())]

  [(⊢-inst-list S (inst ...) (C ...))
   (⊢-inst S inst_2 C_2)
   -------------------
   (⊢-inst-list S (inst ... inst_2) (C ... C_2))])

(define-metafunction WASMIndexTypes
  check-memory-sizes : (meminst ...) (j ...) -> boolean
  [(check-memory-sizes ((bits any) ...) (j ...))
   ,(and (= (length (term (any ...))) (length (term (j ...))))
         (andmap (lambda (mem j)
                   (<= j (memory-size mem)))
                 (term (any ...))
                 (term (j ...))))])

(define-judgment-form WASMPrechkWithAdmin
  #:contract (⊢-store s S)

  [(where ((C ...) (tab ((i (i_2 ...)) ...)) (mem (j ...))) S)
   (⊢-inst-list S (inst ...) (C ...))
   (where (cl_2 ...) ,(apply append (term ((cl ...) ...))))
   (⊢-cl-list S (cl_2 ...) (tfi ...))
   ;(valid-indices (cl ...) (i_2 ...) i) ...
   (side-condition (check-memory-sizes (meminst ...) (j ...)))
   -----------------------------------------------------------
   (⊢-store ((inst ...) ((cl ...) ...) (meminst ...)) S)])

(define-judgment-form WASMPrechkWithAdmin
  #:contract (⊢-exec s i (v ...) (e ...) ticond)

  [(⊢-store s S)
   (⊢-top S i (v ...) (e ...) ticond)
   -----------------------------------
   (⊢-exec s i (v ...) (e ...) ticond)])

(define-judgment-form WASMPrechkWithAdmin
  #:contract (⊢-top S k (v ...) (e ...) ticond)

  [(where ((inst (C ...)) _ _) S)
   (where ((func (tfi_1 ...)) (global (tg ...)) (table (j_1 (tfi_2 ...)) ...) (memory j_2 ...) _ (label (ticond_1  ...)) _) (do-get (C ...) i))
   (⊢-admin S ((func (tfi_1 ...)) (global (tg ...)) (table (j_1 (tfi_2 ...)) ...) (memory j_2 ...) (local (t ...)) (label (ticond_1  ...)) (return))
      (e ...) ((() ((t a) ...) Γ_1 φ_1) -> ((ti ...) locals Γ φ)))
   (where Γ_1 (build-gamma ((t a) ...)))
   (where φ_1 (build-phi (t ...) (a ...) (c ...)))
   --------------------------------------------------------------------------------------------------------------------------------------------
   (⊢-top S i ((t const c) ...) (e ...) ((ti ...) locals Γ φ))])

(define-judgment-form WASMPrechkWithAdmin
  #:contract (⊢-return S i (v ...) (e ...) ticond)

  [(where ((inst (C ...)) _ _) S)
   (where ((func (tfi_1 ...)) (global (tg ...)) (table (j_1 (tfi_2 ...)) ...) (memory j_2 ...) _ (label (ticond_1  ...)) _) (do-get (C ...) i))
   (⊢-admin S ((func (tfi_1 ...)) (global (tg ...)) (table (j_1 (tfi_2 ...)) ...) (memory j_2 ...) (local (t ...)) (label (ticond_1  ...)) (return ticond))
      (e ...) ((() ((t a) ...) Γ_1 φ_1) -> ((ti ...) locals Γ φ)))
   (where Γ_1 (build-gamma ((t a) ...)))
   (where φ_1 (build-phi (t ...) (a ...) (c ...)))
   --------------------------------------------------------------------------------------------------------------------------------------------------
   (⊢-return S i ((t const c) ...) (e ...) ((ti ...) locals Γ φ))])

(define-judgment-form WASMIndexTypes
  #:contract (⊢-admin S C (e ...) tfi)

  [(side-condition (satisfies Γ φ (empty (not (= a_2 (i32 0))))))
   (where #f (in a_3 Γ)) ;; a_3 fresh
   ------------------------------------------------------- "Div-Prechk"
   (⊢-admin S C ((t div/unsafe)) ((((t a_1) (t a_2)) locals Γ φ)
                                  -> (((t a_3)) locals (Γ (t a_3)) (φ (= a_3 (div a_1 a_2))))))]

  [(where (binop_!_1 binop_!_1) (binop div/unsafe))
   (where #f (in a_3 Γ)) ;; a_3 fresh
   ------------------------------------------------ "Binop"
   (⊢-admin S C ((t binop)) ((((t a_1) (t a_2)) locals Γ φ)
                             -> (((t a_3)) locals (Γ (t a_3)) (φ (= a_3 (binop a_1 a_2))))))]

  [(where #f (in a_2 Γ)) ;; a_2 fresh
   --------
   "Testop"
   (⊢-admin S C ((t testop)) ((((t a)) locals Γ φ)
                              -> (((t a_2)) locals (Γ (t a_2)) (φ (= a_2 (testop a))))))]

  [(where #f (in a_3 Γ)) ;; a_3 fresh
   -------
   "Relop"
   (⊢-admin S C ((t relop)) ((((t a_1) (t a_2)) locals Γ φ)
                             -> (((t a_3)) locals (Γ (t a_3)) (φ (= a_3 (relop a_1 a_2))))))]

  [---
   "Unreachable"
   (⊢-admin S C ((unreachable)) tfi)]

  [---
   "Nop"
   (⊢-admin S C ((nop)) ((() locals Γ φ) -> (() locals Γ φ)))]

  [---
   "Drop"
   (⊢-admin S C ((drop)) (((ti ... (t a)) locals Γ φ) -> ((ti ...) locals Γ φ)))]

  [(where #f (in a_3 Γ)) ;; a_3 fresh
   ---
   "Select"
   (⊢-admin S C ((select)) ((((t a_1) (t a_2) (i32 a)) locals Γ φ)
                            -> (((t a_3)) locals (Γ (t a))
                                          (φ (if (= a (i32 0))
                                                 (= a_3 a_2)
                                                 (= a_3 a_1))))))]
  
  [(where C_2 (in-label C_1 ((ti_2 ...) locals_2 Γ_3 φ_3)))
   (⊢-admin S C_2 (e ...) (((ti_1 ...) locals_1 Γ_2 φ_2) -> ((ti_2 ...) locals_2 Γ_4 φ_4)))
   (side-condition (satisfies Γ_1 φ_1 φ_2)) ;; Strengthen precondition outside
   (side-condition (satisfies Γ_2 φ_4 φ_3)) ;; Weaken postcondition inside
   (side-condition (equiv-gammas Γ_2 (build-gamma (merge (ti_1 ...) locals_1)))) ;; Γ_2 = ti_1 ... locals_1
   (side-condition ,(subset? (term (domain-φ φ_2)) (term (domain-Γ Γ_2)))) ;; domain(φ_2) subset of Γ_2
   (where Γ_5 (union Γ_1 Γ_3))
   (where φ_5 (union φ_1 φ_3))
   --------------------------- "Block"
   (⊢-admin S C_1 ((block (((ti_1 ...) locals_1 Γ_2 φ_2) -> ((ti_2 ...) locals_2 Γ_3 φ_3)) (e ...)))
            (((ti_1 ...) locals_1 Γ_1 φ_1) -> ((ti_2 ...) locals_2 Γ_5 φ_5)))]

  [(where C_2 (in-label C_1 ((ti_1 ...) locals_1 Γ_2 φ_2)))
   (⊢-admin S C_2 (e ...) (((ti_1 ...) locals_1 Γ_2 φ_2) -> ((ti_2 ...) locals_2 Γ_4 φ_4)))
   (side-condition (satisfies Γ_1 φ_1 φ_2)) ;; Strengthen precondition outside
   (side-condition (satisfies Γ_2 φ_4 φ_3)) ;; Weaken postcondition inside
   (side-condition (equiv-gammas Γ_2 (build-gamma (merge (ti_1 ...) locals_1)))) ;; Γ_2 = ti_1 ... locals_1
   (side-condition ,(subset? (term (domain-φ φ_2)) (term (domain-Γ Γ_2)))) ;; domain(φ_2) subset of Γ_2
   (where Γ_5 (union Γ_1 Γ_3))
   (where φ_5 (union φ_1 φ_3))
   --------------------------- "Loop"
   (⊢-admin S C_1 ((loop (((ti_1 ...) locals_1 Γ_2 φ_2) -> ((ti_2 ...) locals_2 Γ_3 φ_3)) (e ...)))
            (((ti_1 ...) locals_1 Γ_1 φ_1) -> ((ti_2 ...) locals_2 Γ_5 φ_5)))]

  [(where C_2 (in-label C_1 ((ti_2 ...) locals_2 Γ_3 φ_3)))
   (⊢-admin S C_2 (e_1 ...) (((ti_1 ...) locals_1 Γ_2 φ_2)
                             -> ((ti_2 ...) locals_2 Γ_4 φ_4)))
   (⊢-admin S C_2 (e_2 ...) (((ti_1 ...) locals_1 Γ_2 φ_2)
                             -> ((ti_2 ...) locals_2 Γ_4 φ_4)))
   (side-condition (satisfies Γ_1 φ_1 φ_2)) ;; Strengthen precondition outside
   (side-condition (satisfies Γ_2 φ_4 φ_3)) ;; Weaken postcondition inside
   (side-condition (equiv-gammas Γ_2 (build-gamma (merge (ti_1 ...) locals_1)))) ;; Γ_2 = ti_1 ... locals_1
   (side-condition ,(subset? (term (domain-φ φ_2)) (term (domain-Γ Γ_2)))) ;; domain(φ_2) subset of Γ_2
   (where Γ_5 (union Γ_1 Γ_3))
   (where φ_5 (union φ_1 φ_3))
   --------------------------------------------------------------------- "If"
   (⊢-admin S C_1 ((if (((ti_1 ...) locals_1 Γ_2 φ_2) -> ((ti_2 ...) locals_2 Γ_3 φ_3)) (e_1 ...) (e_2 ...)))
            (((ti_1 ...) locals_1 Γ_1 φ_1) -> ((ti_2 ...) locals_2 Γ_5 φ_5)))]

  [(label-types (ticond ...) (j) ((ti ...) locals Γ_1 φ_1))
   -------------------------------------------------------- "Br"
   (⊢-admin S (_ _ _ _ _ (label (ticond  ...)) _)
            ((br j))
            (((ti_1 ... ti ...) locals Γ_1 φ_1)
             -> ((ti_2 ...) locals Γ_2 φ_2)))]

  [(label-types (ticond ...) (j) ((ti ...) locals Γ_1 (φ_1 (not (= a (i32 0))))))
   ------------------------------------------------------------------------------ "Br-If"
   (⊢-admin S (_ _ _ _ _ (label (ticond  ...)) _)
            ((br-if j))
            (((ti ... (i32 a)) locals Γ_1 φ_1)
             -> ((ti ...) locals Γ_1 (φ_1 (= a (i32 0))))))]

  [(label-types (ticond ...) (j ...) ((ti_3 ...) locals Γ_1 φ_1))
   -------------------------------------------------------------- "Br-Table"
   (⊢-admin S ((_ _ _ _ (label (ticond ...)) _ _))
            ((br-table (j ...)))
            (((ti_1 ... ti_3 ... (i32 a)) locals Γ_1 φ_1)
             -> ((ti_2 ...) locals Γ_1 φ_2)))]

  [(side-condition (satisfies Γ_1 φ_1 φ)) ;; Strengthen precondition
   -------------------------------------- "Return"
   (⊢-admin S (_ _ _ _ _ _ (return ((ti ...) _ _ φ)))
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
   (⊢-admin S ((func (tfi ...)) _ _ _ _ _ _) ((call j))
            (((ti_1 ...) locals Γ_1 φ_1)
             -> ((ti_2 ...) locals Γ_4 φ_4)))]
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  [(side-condition (satisfies Γ_1 φ_1 φ_2)) ;; Strengthen precondition
   (where φ_4 (union φ_1 φ_3))
   (where Γ_4 (union Γ_1 Γ_3))
   --------------------------- "Call-Indirect"
   (⊢-admin S (_ _ (table j _) _ _ _ _)
            ((call-indirect (((ti_1 ...) _ Γ_2 φ_2) -> ((ti_2 ...) _ Γ_3 φ_3))))
            (((ti_1 ... (i32 a)) locals_1 Γ_1 φ_1)
             -> ((ti_2 ...) locals_1 Γ_4 φ_4)))]
  
  [(side-condition (satisfies Γ_1 φ_1 φ_2)) ;; Strengthen precondition
   (where φ_4 (union φ_1 φ_3))
   (where Γ_4 (union Γ_1 Γ_3))
   (side-condition (valid-table-call (((ti_1 ...) () Γ_2 φ_2) -> ((ti_2 ...) () Γ_3 φ_3))
                                     a (tfi ...) Γ_1 φ_1))
   ------------------------------------------------------- "Call-Indirect-Prechk"
   (⊢-admin S (_ _ (table (j (tfi ...))) _ _ _ _)
            ((call-indirect/unsafe (((ti_1 ...) _ Γ_2 φ_2) -> ((ti_2 ...) _ Γ_3 φ_3))))
            (((ti_1 ... (i32 a)) locals_1 Γ_1 φ_1)
             -> ((ti_2 ...) locals_1 Γ_4 φ_4)))]

  [(where t_2 (do-get (t ...) j))
   (where (t_2 a) (do-get locals j))
   (where #f (in a_2 Γ)) ;; a_2 fresh
   --------------------------------- "Get-Local"
   (⊢-admin S (_ _ _ _ (local (t ...)) _ _)
            ((get-local j))
            ((() locals Γ φ)
             -> (((t_2 a_2)) locals (Γ (t_2 a_2)) (φ (= a_2 a)))))]

  [(where t_2 (do-get (t ...) j))
   (where locals_2 (do-set locals_1 j (t_2 a)))
   -------------------------------------------- "Set-Local"
   (⊢-admin S (_ _ _ _ (local (t ...)) _ _)
            ((set-local j))
            ((((t_2 a)) locals_1 Γ φ)
             -> (() locals_2 Γ φ)))]

  [(where t_2 (do-get (t ...) j))
   (where locals_2 (do-set locals_1 j (t_2 a)))
   (where #f (in a_2 Γ)) ;; a_2 fresh
   ---------------------------------- "Tee-Local"
   (⊢-admin S (_ _ _ _ (local (t ...)) _ _)
            ((tee-local j))
            ((((t_2 a)) locals_1 Γ φ)
             -> (((t_2 a_2)) locals_2 (Γ (t_2 a_2)) (φ (= a_2 a)))))]

  [(where tg_2 (do-get (tg ...) j))
   (where t_2 (erase-mut tg_2))
   (where #f (in a Γ)) ;; a_2 fresh
   ------------------- "Get-Global"
   (⊢-admin S (_ (global (tg ...)) _ _ _ _ _ _)
            ((get-global j))
            ((() locals Γ φ)
             -> (((t_2 a)) locals (Γ (t_2 a)) φ)))]

  [(where (#t t_2) (do-get (tg ...) j))
   ------------------------------------ "Set-Global"
   (⊢-admin S (_ (global (tg ...)) _ _ _ _ _ _)
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
   (⊢-admin S C ((t load/unsafe j_1 j_2)) ((((i32 a)) locals Γ φ_1)
                                           -> (((t a_2)) locals (Γ (t a_2)) φ_1)))]

  [(where (_ _ _ (memory j) _ _ _) C)
   (side-condition ,(< (expt 2 (term j_1))
                       (type-width (term t) (term tp))))
   (side-condition (satisfies Γ φ_1 (empty
                                     (and (= (i32 1) (le (add (add a (i32 j_2)) (i32 ,(/ (type-width (term t) (term tp)) 8))) (i32 j)))
                                          (= (i32 1) (ge (add a (i32 j_2)) (i32 0)))))))
   (where #f (in a_2 Γ)) ;; a_2 fresh
   ----------------------------------------------------------------------- "Load-Prechk-2"
   (⊢-admin S C ((t load/unsafe (tp sz) j_1 j_2)) ((((i32 a)) locals Γ φ_1)
                                                   -> (((t a_2)) locals (Γ (t a_2)) φ_1)))]

  [(where (_ _ _ (memory j) _ _ _) C)
   (side-condition ,(< (expt 2 (term j_1))
                       (type-width (term t))))
   (side-condition (satisfies Γ φ_1 (empty
                                     (and (= (i32 1) (le (add (add a (i32 j_2)) (i32 ,(/ (type-width (term t)) 8))) (i32 j)))
                                          (= (i32 1) (ge (add a (i32 j_2)) (i32 0)))))))
   ------------------------------------------------------------------------- "Store-Prechk-1"
   (⊢-admin S C ((t store/unsafe j_1 j_2)) ((((i32 a) (t a_1)) locals Γ φ_1)
                                            -> (() locals Γ φ_1)))]

  ;; TODO: no floats yet so not included in side-condition
  [(where (_ _ _ (memory j) _ _ _) C)
   (side-condition ,(< (expt 2 (term j_1))
                       (type-width (term t) (term tp))))
   (side-condition (satisfies Γ φ_1 (empty
                                     (and (= (i32 1) (le (add (add a (i32 j_2)) (i32 ,(/ (type-width (term t) (term tp)) 8))) (i32 j)))
                                          (= (i32 1) (ge (add a (i32 j_2)) (i32 0)))))))
   ------------------------------------------------------------------------------ "Store-Prechk-2"
   (⊢-admin S C ((t store/unsafe (tp) j_1 j_2)) ((((i32 a) (t a_1)) locals Γ φ_1)
                                                 -> (() locals Γ φ_1)))]

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  [------------------------------------------ "Empty"
   (⊢-admin S C () ((() locals Γ φ) -> (() locals Γ φ)))]

  [(⊢-admin S C (e_1 ...) (ticond_1 -> ticond_2))
   (⊢-admin S C (e_2) (ticond_2 -> ticond_3))
   -------------------------------------------- "Composition"
   (⊢-admin S C (e_1 ... e_2) (ticond_1 -> ticond_3))]

  ;; Stack polymorphism
  [(⊢-admin S C (e ...) (((ti_1 ...) locals Γ_1 φ_1)
                         -> ((ti_2 ...) locals Γ_2 φ_2)))
   ------------------------------------------------------ "Stack-Poly"
   (⊢-admin S C (e ...) (((ti ... ti_1 ...) locals Γ_1 φ_1)
                         -> ((ti ... ti_2 ...) locals Γ_2 φ_2)))]

  ;; Admin instructions
  [-------------------------- "Trap"
   (⊢-admin S C ((trap)) tfi)]

  [(where n ,(length (term (ti_2 ...))))
   (⊢-admin S C (e_0 ...) (((ti_3 ...) locals_3 Γ_3 φ_3) -> ((ti_2 ...) locals_2 Γ_2 φ_2)))
   (where C_2 (in-label C_1 ((ti_3 ...) locals_3 Γ_3 φ_3)))
   (⊢-admin S C_2 (e ...) ((() locals_1 Γ_1 φ_1) -> ((ti_2 ...) locals_2 Γ_2 φ_2)))
   --------------------------------------------------------------------- "Label"
   (⊢-admin S C_1 ((label n (e_0 ...) (e ...))) ((() locals_1 Γ_1 φ_1) -> ((ti_2 ...) locals_2 Γ_2 φ_2)))]

  [(⊢-cl S cl (((ti_1 ...) _ Γ_2 φ_2) -> ((ti_2 ...) _ Γ_3 φ_3)))
   (side-condition (satisfies Γ_1 φ_1 φ_2))
   (where Γ_4 (union Γ_1 Γ_3))
   (where φ_4 (union φ_1 φ_3))
   ---------------------------------------- "Call-Cl"
   (⊢-admin S C ((call cl)) (((ti_1 ...) locals Γ_1 φ_1) -> ((ti_2 ...) locals Γ_4 φ_4)))]

  [(where n ,(length (term (ti ...))))
   (⊢-return S i (v ...) (e ...) ((ti ...) _ Γ_2 φ_2))
   (where Γ_3 (union Γ_1 Γ_2))
   (where φ_3 (union φ_1 φ_2))
   ---------------------------------------------------------------------------------------- "Local"
   (⊢-admin S C ((local n (i (v ...)) (e ...))) ((() locals Γ_1 φ_1) -> ((ti ...) locals Γ_3 φ_3)))])
