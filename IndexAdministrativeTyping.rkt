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
     (label (e ...) (e ...)) (local (i (v ...)) (e ...)))
  
  (S ::= ((C ...) (tab ((j (tfi ...)) ...)) (mem (j ...))))

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
   (⊢-module-func S C_2 f (_ tfi))
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
   (⊢ S ((func (tfi_1 ...)) (global (tg ...)) (table (j_1 (tfi_2 ...)) ...) (memory j_2 ...) (local (t ...)) (label (ticond_1  ...)) (return))
      (e ...) ((() locals_1 globals_1 φ_1) -> ticond))
   --------------------------------------------------------------------------------------------------------------------------------------------
   (⊢-top S i ((t const c) ...) (e ...) ticond)])

(define-judgment-form WASMPrechkWithAdmin
  #:contract (⊢-return S i (v ...) (e ...) ticond)
  
  [(where ((inst (C ...)) _ _) S)
   (where ((func (tfi_1 ...)) (global (tg ...)) (table (j_1 (tfi_2 ...)) ...) (memory j_2 ...) _ (label (ticond_1  ...)) _) (do-get (C ...) i))
   (⊢ S ((func (tfi_1 ...)) (global (tg ...)) (table (j_1 (tfi_2 ...)) ...) (memory j_2 ...) (local (t ...)) (label (ticond_1  ...)) (return ticond))
      (e ...) ((() locals_1 globals_1 φ_1) -> ticond))
   --------------------------------------------------------------------------------------------------------------------------------------------------
   (⊢-return S i ((t const c) ...) (e ...) ticond)])

(define-extended-judgment-form WASMPrechkWithAdmin ⊢
  #:contract (⊢- S C (e ...) tfi)

  [---------------------
   (⊢- S C ((trap)) tfi)]

  [(⊢ S C (e_0 ...) (ticond_1 -> ticond_2))
   (where ((func (tfi ...)) (glob (tg ...)) (table (j_1 (tfi_2 ...))) (memory j_2) (local (t_3 ...)) _ (return ticond_3)) C)
   (⊢ S ((func (tfi ...)) (glob (tg ...)) (table (j_1 (tfi_2 ...))) (memory j_2) (local (t_3 ...)) ticond_1 (return ticond_3))
      (e ...)
      ((() locals_1 globals_1 φ_1) -> ticond_2))
   ---------------------------------------------------------------------------------------------------------------------------
   (⊢- S C ((label (e_0 ...) (e ...))) ((() locals_1 globals_1 φ_1) -> ticond_2))]

  [(⊢-cl S cl tfi)
   ------------------------
   (⊢- S C ((call cl)) tfi)]

  ;; TODO: This only works when j is the current instance index, need to thread instance number through typing rules
  ;;       to separate out the cases when they are different.
  [(⊢-return S j (v ...) (e ...) ((ti ...) locals_2 globals_2 φ_2))
   ---------------------------------------------------------------------------------------------------------
   (⊢- S C ((local (j (v ...)) (e ...))) ((() locals_1 globals_1 φ_1) -> ((ti ...) locals_1 globals_2 φ_2)))]

  #;[(⊢-return S j (v ...) (e ...) ((ti ...) locals_2 globals_2 φ_2))
   ;; replace globals_2 with (t_k a_k) where t_k is the type in C, and a_k are fresh
   ;; extend φ_2 with (t_k a_k) (eq a_k_c c), where k_c are the constant global variables
   ---------------------------------------------------------------------------------------------------------
   (⊢- S C ((local (j (v ...)) (e ...))) ((() locals_1 globals_1 φ_1) -> ((ti ...) locals_1 globals_2 φ_2)))])
