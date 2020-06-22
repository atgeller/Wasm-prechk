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
  #:contract (⊢-val v t)
  #:mode (⊢-val I I)

  [----------------------
   (⊢-val (t const c) t)])

;; Work-around because of oddities in Redex
(define-judgment-form WASMPrechkWithAdmin
  #:contract (⊢-infer-val-types (v ...) (t ...))
  #:mode (⊢-infer-val-types I O)

  [---------------------------
   (⊢-infer-val-types () ())]

  [(⊢-infer-val-types (v ...) (t ...))
   -----------------------------------
   (⊢-infer-val-types (v ... (t_1 const c)) (t ... t_1))])

(define-judgment-form WASMPrechkWithAdmin
  #:contract (⊢-cl S cl tfi)

  [(where C_2 (do-get (C ...) i))
   (⊢-module-func C_2 f (_ tfi))
   -----------------------------
   (⊢-cl ((C ...) _ _) (i f) tfi)])

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

  [(⊢-val v t) ...
   (⊢-cl-list S (cl ...) (tfi ...))
   (where ((C ...) (tab ((j_1 (tfi_1 ...)) ...)) (mem (j_2 ...))) S)
   (where (j_3 (tfi_3 ...)) (do-get ((j_1 (tfi_1 ...)) ...) j))
   (where j_4 (do-get (j_2 ...) i))
   --------------------------------
   (⊢-inst S ((cl ...) (v ...) (table j) (memory i))
           ((func (tfi ...)) (glob ((_ t) ...)) (table (j_3 (tfi_3 ...))) (memory j_4) _ _ _))]

  [(⊢-val v t) ...
   (⊢-cl-list S (cl ...) (tfi ...))
   (where (_ (tab ((j_1 (tfi_1 ...)) ...)) _) S)
   (where (j_3 (tfi_3 ...)) (do-get ((j_1 (tfi_1 ...)) ...) j))
   --------------------------------------------------------
   (⊢-inst S ((cl ...) (v ...) (table j) (memory))
           ((func (tfi ...)) (glob ((_ t) ...)) (table (j_3 (tfi_3 ...))) (memory) _ _ _))]

  [(⊢-val v t) ...
   (⊢-cl-list S (cl ...) (tfi ...))
   (where (_ _ (mem (j_2 ...))) S)
   (where j_4 (do-get (j_2 ...) i))
   --------------------------------
   (⊢-inst S ((cl ...) (v ...) (table) (memory i))
           ((func (tfi ...)) (glob ((_ t) ...)) (table) (memory j_4) _ _ _))]

  [(⊢-val v t) ...
   (⊢-cl-list S (cl ...) (tfi ...))
   --------------------------------
   (⊢-inst S ((cl ...) (v ...) (table) (memory))
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
   (valid-indices (cl ...) (i_2 ...) i) ...
   (side-condition (check-memory-sizes (meminst ...) (j ...)))
   -----------------------------------------------------------
   (⊢-store ((inst ...) ((cl ...) ...) (meminst ...)) S)])

;; TODO: Go back and add S to every prior rule (doesn't do anything except get passed around)
;; TODO: Redex doesn't understand that t is inferred from ⊢-val
(define-judgment-form WASMPrechkWithAdmin
  #:contract (⊢-code S ticond_1 i (v ...) (e ...) ticond_2)

  [(⊢-infer-val-types (v ...) (t ...))
   (where (() locals_1 globals_1 φ_1) ticond_1)
   (where ((C ...) _ _) S)
   (where ((func (tfi ...)) (glob (tg ...)) (table (j_1 (tfi_2 ...))) (memory j_2) _ _ _) (do-get (C ...) i))
   (where C_2 ((func (tfi ...)) (glob (tg ...)) (table (j_1 (tfi_2 ...))) (memory j_2) (local (t ...)) (label ()) (return ticond_2)))
   (⊢ C_2 (e ...) (ticond_1 -> ticond_2))
   ---------------------------------------------------------------------------------
   (⊢-code S ticond_1 i (v ...) (e ...) ticond_2)])

(define-judgment-form WASMPrechkWithAdmin
  #:contract (⊢-exec s ticond_1 i (v ...) (e ...) ticond_2)

  [(⊢-store s S)
   (where (() locals_1 globals_1 φ_1) ticond_1)
   (⊢-code S ticond_1 i (v ...) (e ...) ticond_2)
   ----------------------------------------------
   (⊢-exec s ticond_1 i (v ...) (e ...) ticond_2)])

(define-judgment-form WASMPrechkWithAdmin
  #:contract (⊢-trap S C (trap) tfi)

  [-------------------------
   (⊢-trap S C (trap) tfi)])

(define-judgment-form WASMPrechkWithAdmin
  #:contract (⊢-label S C (label (e ...) (e ...)) tfi)

  [(⊢ C (e_0 ...) (ticond_1 -> ticond_2))
   (where ((func (tfi ...)) (glob (tg ...)) (table (j_1 (tfi_2 ...))) (memory j_2) (local (t_3 ...)) _ (return ticond_3)) C)
   (⊢ ((func (tfi ...)) (glob (tg ...)) (table (j_1 (tfi_2 ...))) (memory j_2) (local (t_3 ...)) ticond_1 (return ticond_3))
      (e ...)
      ((() locals_1 globals_1 φ_1) -> ticond_2))
   -----------------------------------------------------------------------------------
   (⊢-label S C (label (e_0 ...) (e ...)) ((() locals_1 globals_1 φ_1) -> ticond_2))])

(define-judgment-form WASMPrechkWithAdmin
  #:contract (⊢-call-cl S C (call cl) tfi)

  [(⊢-cl S cl tfi)
   --------------
   (⊢-call-cl S C (call cl) tfi)])

(define-judgment-form WASMPrechkWithAdmin
  #:contract (⊢-local S C (local (i (v ...)) (e ...)) tfi)

  [(⊢code S () ticond_1 i (v ...) (e ...) ticond_2)
   ------------------------------------------------
   (⊢-local S C (local (i (v ...)) (e ...)) (ticond_1 -> ticond_2))])