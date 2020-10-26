#lang racket

(require redex
         "IndexTypes.rkt"
         "SubTyping.rkt"
         "IndexTypingRules.rkt"
         "IndexModuleTyping.rkt"
         "Utilities.rkt"
         "WASM-Redex/Utilities.rkt"
         "WASM-Redex/Bits.rkt")

(define-extended-language WASMPrechkWithAdmin WASMIndexTypes
  (v ::= (t const c))
  (cl ::= (i f))
  (e ::= .... (trap) (call cl)
     (label n (e ...) (e ...)) (local n (i (v ...)) (e ...)))

  (S ::= ((C ...) (table ((j (tfi ...)) ...)) (memory (j ...))))

  (inst ::= ((cl ...) (v ...) (table (j (tfi ...))) (memory j))
        ((cl ...) (v ...) (table (j (tfi ...))) (memory))
        ((cl ...) (v ...) (table) (memory j))
        ((cl ...) (v ...) (table) (memory)))
  (tabinst ::= (cl ...))
  (meminst ::= (bits any))
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
      (e ...) ((() locals_1 φ_1) -> ticond))
   --------------------------------------------------------------------------------------------------------------------------------------------
   (⊢-top S i ((t const c) ...) (e ...) ticond)])

(define-judgment-form WASMPrechkWithAdmin
  #:contract (⊢-return S i (v ...) (e ...) (locals φ) ticond)

  [(where ((inst (C ...)) _ _) S)
   (where ((func (tfi_1 ...)) (global (tg ...)) (table (j_1 (tfi_2 ...)) ...) (memory j_2 ...) _ (label (ticond_1  ...)) _) (do-get (C ...) i))
   (⊢-admin S ((func (tfi_1 ...)) (global (tg ...)) (table (j_1 (tfi_2 ...)) ...) (memory j_2 ...) (local (t ...)) (label (ticond_1  ...)) (return ticond))
      (e ...) ((() locals_1 φ_1) -> ticond))
   --------------------------------------------------------------------------------------------------------------------------------------------------
   (⊢-return S i ((t const c) ...) (e ...) (locals_1 φ_1) ticond)])

(define-judgment-form WASMPrechkWithAdmin
  #:contract (⊢-admin S C (e ...) tfi)

  [;; a fresh
   (⊢-admin S C ((t const c)) ((() locals φ)
                         -> (((t a)) locals ((φ (t a)) (eq a (t c))))))]

  [(side-condition (satisfies φ (empty (ne a_2 (i32 0)))))
   ;; a_3 fresh
   -------------------------------------------------------
   (⊢-admin S C ((t div/unsafe)) ((((t a_1) (t a_2)) locals φ)
                            -> (((t a_3)) locals ((φ (t a_3)) (eq a_3 (div a_1 a_2))))))]

  [(where (binop_!_1 binop_!_1) (binop div/unsafe))
   ;; a_3 fresh
   ------------------------------------------------
   (⊢-admin S C ((t binop)) ((((t a_1) (t a_2)) locals φ)
                       -> (((t a_3)) locals ((φ (t a_3)) (eq a_3 (binop a_1 a_2))))))]

  [;; a_2 fresh
   (⊢-admin S C ((t testop)) ((((t a)) locals φ)
                        -> (((t a_2)) locals
                                    ((φ (t a_2)) (and (and (testop a) (eq a_2 1))
                                                      (and (not (testop a)) (eq a_2 0)))))))]

  [;; a_3 fresh
   (⊢-admin S C ((t relop)) ((((t a_1) (t a_2)) locals φ)
                       -> (((t a_3)) locals
                                     ((φ (t a_3)) (and (and (relop a_1 a_2) (eq a_3 1))
                                                       (and (not (relop a_1 a_2)) (eq a_3 0)))))))]

  [(⊢-admin S C ((unreachable)) tfi)]

  [(⊢-admin S C ((nop)) ((() locals φ) -> (() locals φ)))]

  [(⊢-admin S C ((drop)) (((ti ... (t a)) locals φ) -> ((ti ...) locals φ)))]

  [(⊢-admin S C ((select)) ((((t a_1) (t a_2) (i32 c)) locals φ)
                      -> (((t a_3)) locals
                                    ((φ (t a_3)) (and (and (eqz c) (eq a_3 a_1))
                                                      (and (not (eqz c)) (eq a_3 a_2)))))))]

  [(where (ticond_1 -> ticond_2) tfi)
   (where C_2 (in-label C_1 ticond_2))
   (⊢-admin S C_2 (e ...) tfi)
   -----------------------------------
   (⊢-admin S C_1 ((block tfi (e ...))) tfi)]

  [(where (ticond_1 -> ticond_2) tfi)
   (where C_2 (in-label C_1 ticond_1))
   (⊢-admin S C_2 (e ...) tfi)
   ----------------------------------
   (⊢-admin S C_1 ((loop tfi (e ...))) tfi)]

  [(where (((ti_1 ...) locals_1 φ_1)
           -> ticond_2) tfi)
   (where C_2 (in-label C_1 ticond_2))
   (⊢-admin S C_2 (e_1 ...) (((ti_1 ...) locals_1 (φ_1 (neq a (i32 0)))) -> ticond_2))
   (⊢-admin S C_2 (e_2 ...) (((ti_1 ...) locals_1 (φ_1 (eqz a))) -> ticond_2))
   ------------------------------------
   (⊢-admin S C_1 ((if tfi (e_1 ...) (e_2 ...)))
      (((ti_1 ... (i32 a)) locals_1 φ_1) -> ticond_2))]

  [(label-types (ticond ...) (j) ((ti ...) φ_1))
   ---------------------------------------------
   (⊢-admin S (_ _ _ _ _ (label (ticond  ...)) _)
      ((br j))
      (((ti_1 ... ti ...) locals φ_1)
       -> ((ti_2 ...) locals φ_2)))]

  ;; TODO: Should be (i32 a) not (t a)
  [(label-types (ticond ...) (j) ((ti ...) φ_1))
   ---------------------------------------------
   (⊢-admin S (_ _ _ _ _ (label (ticond  ...)) _)
      ((br-if j))
      (((ti ... (t a)) locals φ_1)
       -> ((ti ...) locals (φ_1 (eqz a)))))]

  ;; TODO: fix label-types :)
  ;; TODONE: Hopefully
  [(label-types (ticond ...) (j ...) ((ti_3 ...) φ_1))
   ----------------------------------------
   (⊢-admin S ((_ _ _ _ (label (ticond ...)) _ _))
      ((br-table (j ...)))
      (((ti_1 ... ti_3 ... (i32 a)) locals φ_1)
       -> ((ti_2 ...) locals φ_2)))]

  [(side-condition (satisfies φ_1 φ))
   --------------------------------------------------
   (⊢-admin S (_ _ _ _ _ _ (return ((ti ...) _ φ)))
      ((return))
      (((ti_1 ... ti ...) locals φ_1)
       -> ticond))]

  ;; Only works if Function is internal
  ;; Justin - Actually, I think this works fine, functions imported from other contexts have to
  ;;          have a type declaration in the context that they're called from.
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  [(where (((ti_1 ...) _ φ_1) -> ((ti_2 ...) _ φ_2)) (do-get (tfi ...) j))
   (where φ_3 (extend φ φ_2))
   (side-condition (satisfies φ φ_1))
   ----------------------------------------------
   (⊢-admin S ((func (tfi ...)) _ _ _ _ _ _) ((call j))
      (((ti_1 ...) locals φ)
       -> ((ti_2 ...) locals φ_3)))]
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  [(where (((ti_1 ...) _ φ_2)
           -> ((ti_2 ...) _ φ_3)) tfi)
   (side-condition (satisfies φ_1 φ_2))
   ------------------------------------
   (⊢-admin S (_ _ (table j _) _ _ _ _)
      ((call-indirect tfi))
      (((ti_1 ... (i32 a)) locals_1 φ_1)
       -> ((ti_2 ...) locals_1 φ_3)))]

  [(where (((ti_1 ...) _ φ_2) -> ((ti_2 ...) _  φ_3)) tfi_2)
   (side-condition (satisfies φ_1 φ_2))
   (side-condition (valid-table-call tfi_2 a (tfi ...) φ_1))
   ---------------------------------------------------------
   (⊢-admin S (_ _ (table (j (tfi ...))) _ _ _ _)
      ((call-indirect/unsafe tfi_2))
      (((ti_1 ... (i32 a)) locals_1 φ_1)
       -> ((ti_2 ...) locals_1  φ_3)))]

  [(where t_2 (do-get (t ...) j))
   (where (t_2 a) (do-get locals j))
   ;; a_2 fresh
   ---------------------------------
   (⊢-admin S (_ _ _ _ (local (t ...)) _ _)
      ((get-local j))
      ((() locals φ)
       -> (((t_2 a_2)) locals ((φ (t_2 a_2)) (eq a_2 a)))))]

  [(where t_2 (do-get (t ...) j))
   (where locals_2 (do-set locals_1 j (t_2 a_2)))
   ;; a_2 fresh
   ----------------------------------------------
   (⊢-admin S (_ _ _ _ (local (t ...)) _ _)
      ((set-local j))
      ((((t_2 a)) locals_1 φ)
       -> (() locals_2 ((φ (t_2 a_2)) (eq a_2 a)))))]

  [(where t_2 (do-get (t ...) j))
   (where locals_2 (do-set locals_1 j (t_2 a_2)))
   ;; a_2 fresh
   ----------------------------------------------
   (⊢-admin S (_ _ _ _ (local (t ...)) _ _)
      ((tee-local j))
      ((((t_2 a)) locals_1 φ)
       -> (((t_2 a)) locals_2 ((φ (t_2 a_2)) (eq a_2 a)))))]

  ;; TODO: if not mut, lookup value?
  [(where tg_2 (do-get (tg ...) j))
   (where t_2 (erase-mut tg_2))
   --------------------------------------
   (⊢-admin S (_ (global (tg ...)) _ _ _ _ _ _)
      ((get-global j))
      ((() locals φ)
       -> (((t_2 a_2)) locals ((φ (t_2 a_2)) (eq a_2 a)))))]

  [(where (mut t_2) (do-get (tg ...) j))
   --------------------------------------
   (⊢-admin S (_ (global (tg ...)) _ _ _ _ _ _)
      ((set-global j))
      ((((t_2 a)) locals φ)
       -> (() locals  ((φ (t_2 a_2)) (eq a_2 a)))))]

  [(where (_ _ _ (memory j) _ _ _) C)
   (side-condition ,(< (expt 2 (term j_1))
                       (type-width (term t))))
   (side-condition (satisfies φ_1 ((empty (i32 a))
                                   (and (le (add (add a (i32 j_2)) (i32 ,(/ (type-width (term t)) 8))) (i32 j))
                                        (ge (add a (i32 j_2)) (i32 0))))))
   ;; a_2 fresh
   -----------------------------------------------------------------------
   (⊢-admin S C ((t load/unsafe j_1 j_2)) ((((i32 a)) locals φ_1)
                                     -> (((t a_2)) locals (φ_1 (t a_2)))))]

  [(where (_ _ _ (memory j) _ _ _) C)
   (side-condition ,(< (expt 2 (term j_1))
                       (type-width (term t) (term tp))))
   (side-condition (satisfies φ_1 ((empty (i32 a))
                                   (and (le (add (add a (i32 j_2)) (i32 ,(/ (type-width (term t) (term tp)) 8))) (i32 j))
                                        (ge (add a (i32 j_2)) (i32 0))))))
   ;; a_2 fresh
   -----------------------------------------------------------------------
   (⊢-admin S C ((t load/unsafe (tp sz) j_1 j_2)) ((((i32 a)) locals φ_1)
                                             -> (((t a_2)) locals (φ_1 (t a_2)))))]

  [(where (_ _ _ (memory j) _ _ _) C)
   (side-condition ,(< (expt 2 (term j_1))
                       (type-width (term t))))
   (side-condition (satisfies φ_1 ((empty (i32 a))
                                   (and (le (add (add a (i32 j_2)) (i32 ,(/ (type-width (term t)) 8))) (i32 j))
                                        (ge (add a (i32 j_2)) (i32 0))))))
   -------------------------------------------------------------------------
   (⊢-admin S C ((t store/unsafe j_1 j_2)) ((((i32 a) (t a_1)) locals φ_1)
                                      -> (() locals φ_1)))]

  ;; TODO: no floats yet so not included in side-condition
  [(where (_ _ _ (memory j) _ _ _) C)
   (side-condition ,(< (expt 2 (term j_1))
                       (type-width (term t) (term tp))))
   (side-condition (satisfies φ_1 ((empty (i32 a))
                                   (and (le (add (add a (i32 j_2)) (i32 ,(/ (type-width (term t) (term tp)) 8))) (i32 j))
                                        (ge (add a (i32 j_2)) (i32 0))))))
   ------------------------------------------------------------------------------
   (⊢-admin S C ((t store/unsafe (tp) j_1 j_2)) ((((i32 a) (t a_1)) locals φ_1)
                                           -> (() locals φ_1)))]

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  [-----------------------------------------------------------
   (⊢-admin S C () ((() locals φ) -> (() locals φ)))]

  [(⊢-admin S C (e_1 ...) (ticond_1 -> ((ti_2 ...) locals φ_2)))
   (⊢-admin S C (e_2) (((ti_2 ...) locals φ_3) -> ticond_3))
   (side-condition (satisfies φ_2 φ_3))
   --------------------------------------------
   (⊢-admin S C (e_1 ... e_2) (ticond_1 -> ticond_3))]

  [(⊢-admin S C (e ...) (((ti_1 ...) locals φ_1)
                   -> ((ti_2 ...) locals φ_2)))
   ------------------------------------------------------
   (⊢-admin S C (e ...) (((ti ... ti_1 ...) locals φ_1)
                   -> ((ti ... ti_2 ...) locals φ_2)))]

  [(⊢-admin S C (e ...) tfi_2)
   (<: tfi_1 tfi_2)
   ----------------
   (⊢-admin S C (e ...) tfi_1)]

  [---------------------
   (⊢-admin S C ((trap)) tfi)]

  [(where ((ti_2 ...) locals_2 φ_2) ticond_2)
   (where n ,(length (term (ti_2 ...))))
   (⊢-admin S C (e_0 ...) (ticond_1 -> ticond_2))
   (where ((func (tfi ...)) (glob (tg ...)) (table (j_1 (tfi_2 ...))) (memory j_2) (local (t_3 ...)) _ (return ticond_3)) C)
   (⊢-admin S ((func (tfi ...)) (glob (tg ...)) (table (j_1 (tfi_2 ...))) (memory j_2) (local (t_3 ...)) ticond_1 (return ticond_3))
      (e ...)
      ((() locals_1 φ_1) -> ticond_2))
   -----------------------------------------------------------------------------------
   (⊢-admin S C (label n (e_0 ...) (e ...)) ((() locals_1 φ_1) -> ticond_2))]

  [(⊢-cl S cl tfi)
   ------------------------
   (⊢-admin S C ((call cl)) tfi)]

  [(⊢-return S i (v ...) (e ...) (locals_1 φ_1) ((ti ...) _ φ_2))
   (where n ,(length (term (ti ...))))
   -------------------------------------------------------------------------------------
   (⊢-admin S C ((local n (i (v ...)) (e ...))) ((() locals φ_1) -> ((ti ...) locals φ_2)))])

(define-metafunction WASMPrechkWithAdmin
  add-values : φ_1 (t ...) (a ...) (c ...) -> φ_2
  [(add-values φ_1 () () ()) φ_1]
  [(add-values φ_1 (t t_1 ...) (a a_1 ...) (c c_1 ...))
   (((add-values φ_1 (t_1 ...) (a_1 ...) (c_1 ...)) (t a)) (eq a c))])
