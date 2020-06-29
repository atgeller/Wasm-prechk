#lang racket

(require redex
         "IndexTypes.rkt"
         "SubTyping.rkt"
         "IndexTypingRules.rkt"
         "IndexModuleTyping.rkt"
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
   (⊢-module-func S i C_2 f (_ tfi))
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
   (⊢ S i ((func (tfi_1 ...)) (global (tg ...)) (table (j_1 (tfi_2 ...)) ...) (memory j_2 ...) (local (t ...)) (label (ticond_1  ...)) (return))
      (e ...) ((() locals_1 globals_1 φ_1) -> ticond))
   --------------------------------------------------------------------------------------------------------------------------------------------
   (⊢-top S i ((t const c) ...) (e ...) ticond)])

(define-judgment-form WASMPrechkWithAdmin
  #:contract (⊢-return S i (v ...) (e ...) ticond)

  [(where ((inst (C ...)) _ _) S)
   (where ((func (tfi_1 ...)) (global (tg ...)) (table (j_1 (tfi_2 ...)) ...) (memory j_2 ...) _ (label (ticond_1  ...)) _) (do-get (C ...) i))
   (⊢ S i ((func (tfi_1 ...)) (global (tg ...)) (table (j_1 (tfi_2 ...)) ...) (memory j_2 ...) (local (t ...)) (label (ticond_1  ...)) (return ticond))
      (e ...) ((() locals_1 globals_1 φ_1) -> ticond))
   --------------------------------------------------------------------------------------------------------------------------------------------------
   (⊢-return S i ((t const c) ...) (e ...) ticond)])

(define-extended-judgment-form WASMPrechkWithAdmin ⊢
  #:contract (⊢- S i C (e ...) tfi)

  [---------------------
   (⊢- S i C ((trap)) tfi)]

  [(where ((ti_2 ...) locals_2 globals_2 φ_2) ticond_2)
   (where n ,(length (term (ti_2 ...))))
   (⊢ S i C (e_0 ...) (ticond_1 -> ticond_2))
   (where ((func (tfi ...)) (glob (tg ...)) (table (j_1 (tfi_2 ...))) (memory j_2) (local (t_3 ...)) _ (return ticond_3)) C)
   (⊢ S i ((func (tfi ...)) (glob (tg ...)) (table (j_1 (tfi_2 ...))) (memory j_2) (local (t_3 ...)) ticond_1 (return ticond_3))
      (e ...)
      ((() locals_1 globals_1 φ_1) -> ticond_2))
   -----------------------------------------------------------------------------------
   (⊢- S i C (label n (e_0 ...) (e ...)) ((() locals_1 globals_1 φ_1) -> ticond_2))]

  [(⊢-cl S cl tfi)
   ------------------------
   (⊢- S i C ((call cl)) tfi)]

  [(⊢-return S i (v ...) (e ...) ((ti ...) locals_2 globals_2 φ_2))
   (where n ,(length (term (ti ...))))
   ---------------------------------------------------------------------------------------------------------
   (⊢- S i C ((local n (i (v ...)) (e ...))) ((() locals_1 globals_1 φ_1) -> ((ti ...) locals_1 globals_2 φ_2)))]

  [(⊢-return S i_2 (v ...) (e ...) ((ti ...) locals_2 globals_2 φ_2))
   (where n ,(length (term (ti ...))))
   (side-condition ,(not (equal? (term i_1) (term i_2))))
   ;; a ... fresh
   -------------------------------------------------------------------------
   (⊢- S i_1 (_ (global ((_ t) ...)) _ _ _ _ _)
       ((local n (i_2 (v ...)) (e ...)))
       ((() locals_1 globals_1 φ_1) -> ((ti ...) locals_1 ((t a) ...) φ_2)))])
