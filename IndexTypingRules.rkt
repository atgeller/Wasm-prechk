#lang racket

(require redex
         "IndexTypes.rkt"
         "SubTyping.rkt"
         "TableValidation.rkt"
         "WASM-Redex/Utilities.rkt"
         "WASM-Redex/Bits.rkt")

(provide ⊢)

(define-judgment-form WASMIndexTypes
  #:contract (label-types (ticond ...) (j ...) ticond)
  #:mode (label-types I I I)

  [(where ticond_2 (reverse-get (ticond ...) j))
   (<: ticond_3 ticond_2)
   ---------------------------------------------
   (label-types (ticond ...) (j) ticond_3)]

  [(where ticond_2 (reverse-get (ticond ...) j))
   (side-condition (<: ticond_3 ticond_2))
   (label-types (ticond ...) (j_2 ...) ticond_3)
   ---------------------------------------------
   (label-types (ticond ...) (j j_2 ...) ticond_3)])

(define-metafunction WASMIndexTypes
  valid-table-call : tfi a (tfi ...) φ -> boolean
  [(valid-table-call tfi a (tfi_2 ...) φ)
   ,(check-table-call (term tfi) (term a) (term (tfi_2 ...)) (term φ))])

(define-metafunction WASMIndexTypes
  extend : φ_1 φ_2 -> φ
  [(extend φ_1 empty) φ_1]
  [(extend φ_1 (φ_2 P)) ((extend φ_1 φ_2) P)]
  [(extend φ_1 (φ_2 (t a))) ((extend φ_1 φ_2) (t a))])

(define-metafunction WASMIndexTypes
  reverse-get : (any ...) j -> any
  [(reverse-get (any ... any_1) j)
   (reverse-get (any ...) ,(sub1 (term j)))
   (side-condition (< 0 (term j)))]
  [(reverse-get (any ... any_1) 0) any_1])

(define-metafunction WASMIndexTypes
  in-label : C ticond -> C
  [(in-label ((func (tfi_1 ...)) (global (tg ...)) (table (j_1 (tfi_2 ...)) ...) (memory j_2 ...) (local (t ...)) (label (ticond_1 ...)) (return ticond_2)) ticond_3)
   ((func (tfi_1 ...)) (global (tg ...)) (table (j_1 (tfi_2 ...)) ...) (memory j_2 ...) (local (t ...)) (label (ticond_1 ... ticond_3)) (return ticond_2))]
  [(in-label ((func (tfi_1 ...)) (global (tg ...)) (table (j_1 (tfi_2 ...)) ...) (memory j_2 ...) (local (t ...)) (label (ticond_1 ...)) (return)) ticond_3)
   ((func (tfi_1 ...)) (global (tg ...)) (table (j_1 (tfi_2 ...)) ...) (memory j_2 ...) (local (t ...)) (label (ticond_1 ... ticond_3)) (return))])

(define-metafunction WASMIndexTypes
  erase-mut : tg -> t
  [(erase-mut (mut t)) t]
  [(erase-mut t) t])

(define-judgment-form WASMIndexTypes
  #:contract (⊢ S i C (e ...) tfi)

  [;; a fresh
   (⊢ S i C ((t const c)) ((() locals globals φ)
                           -> (((t a)) locals globals ((φ (t a)) (eq a (t c))))))]

  [(side-condition (satisfies φ (empty (ne a_2 (i32 0)))))
   ;; a_3 fresh
   -------------------------------------------------------
   (⊢ S i C ((t div/unsafe)) ((((t a_1) (t a_2)) locals globals φ)
                              -> (((t a_3)) locals globals ((φ (t a_3)) (eq a_3 (div a_1 a_2))))))]

  [(where (binop_!_1 binop_!_1) (binop div/unsafe))
   ;; a_3 fresh
   ------------------------------------------------
   (⊢ S i C ((t binop)) ((((t a_1) (t a_2)) locals globals φ)
                         -> (((t a_3)) locals globals ((φ (t a_3)) (eq a_3 (binop a_1 a_2))))))]

  [;; a_2 fresh
   (⊢ S i C ((t testop)) ((((t a)) locals globals φ)
                          -> (((t a_2)) locals globals
                                        ((φ (t a_2)) (and (and (testop a) (eq a_2 1))
                                                          (and (not (testop a)) (eq a_2 0)))))))]

  [;; a_3 fresh
   (⊢ S i C ((t relop)) ((((t a_1) (t a_2)) locals globals φ)
                         -> (((t a_3)) locals globals
                                       ((φ (t a_3)) (and (and (relop a_1 a_2) (eq a_3 1))
                                                         (and (not (relop a_1 a_2)) (eq a_3 0)))))))]

  [(⊢ S i C ((unreachable)) tfi)]

  [(⊢ S i C ((nop)) ((() locals globals φ) -> (() locals globals φ)))]

  [(⊢ S i C ((drop)) (((ti ... (t a)) locals globals φ) -> ((ti ...) locals globals φ)))]

  [(⊢ S i C ((select)) ((((t a_1) (t a_2) (i32 c)) locals globals φ)
                        -> (((t a_3)) locals globals
                                      ((φ (t a_3)) (and (and (eqz c) (eq a_3 a_1))
                                                        (and (not (eqz c)) (eq a_3 a_2)))))))]

  [(where (ticond_1 -> ticond_2) tfi)
   (where C_2 (in-label C_1 ticond_2))
   (⊢ S i C_2 (e ...) tfi)
   -----------------------------------
   (⊢ S i C_1 ((block tfi (e ...))) tfi)]

  [(where (ticond_1 -> ticond_2) tfi)
   (where C_2 (in-label C_1 ticond_1))
   (⊢ S i C_2 (e ...) tfi)
   ----------------------------------
   (⊢ S i C_1 ((loop tfi (e ...))) tfi)]

  [(where (((ti_1 ...) locals_1 globals_1 φ_1)
           -> ticond_2) tfi)
   (where C_2 (in-label C_1 ticond_2))
   (⊢ S i C_2 (e_1 ...) (((ti_1 ...) locals_1 globals_1 (φ_1 (neq a (i32 0)))) -> ticond_2))
   (⊢ S i C_2 (e_2 ...) (((ti_1 ...) locals_1 globals_1 (φ_1 (eqz a))) -> ticond_2))
   ------------------------------------
   (⊢ S i C_1 ((if tfi (e_1 ...) (e_2 ...)))
      (((ti_1 ... (i32 a)) locals_1 globals_1 φ_1) -> ticond_2))]

  [(label-types (ticond ...) (j) ((ti ...) φ_1))
   ---------------------------------------------
   (⊢ S i (_ _ _ _ _ (label (ticond  ...)) _)
      ((br j))
      (((ti_1 ... ti ...) locals globals φ_1)
       -> ((ti_2 ...) locals globals φ_2)))]

  ;; TODO: Should be (i32 a) not (t a)
  [(label-types (ticond ...) (j) ((ti ...) φ_1))
   ---------------------------------------------
   (⊢ S i (_ _ _ _ _ (label (ticond  ...)) _)
      ((br-if j))
      (((ti ... (t a)) locals globals φ_1)
       -> ((ti ...) locals globals (φ_1 (eqz a)))))]

  ;; TODO: fix label-types :)
  ;; TODONE: Hopefully
  [(label-types (ticond ...) (j ...) ((ti_3 ...) φ_1))
   ----------------------------------------
   (⊢ S i ((_ _ _ _ (label (ticond ...)) _ _))
      ((br-table (j ...)))
      (((ti_1 ... ti_3 ... (i32 a)) locals globals φ_1)
       -> ((ti_2 ...) locals globals φ_2)))]

  [(side-condition (satisfies φ_1 φ))
   --------------------------------------------------
   (⊢ S i (_ _ _ _ _ _ (return ((ti ...) _ globals φ)))
      ((return))
      (((ti_1 ... ti ...) locals globals φ_1)
       -> ticond))]

  ;; Only works if Function is internal
  ;; Justin - Actually, I think this works fine, functions imported from other contexts have to
  ;;          have a type declaration in the context that they're called from.
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  [(where (((ti_1 ...) _ globals_1 φ_1) -> ((ti_2 ...) _ globals_2 φ_2)) (do-get (tfi ...) j))
   (where φ_3 (extend φ φ_2))
   (side-condition (satisfies φ φ_1))
   ----------------------------------------------
   (⊢ S i ((func (tfi ...)) _ _ _ _ _ _)
      ((call j))
      (((ti_1 ...) locals globals_1 φ)
       -> ((ti_2 ...) locals globals_2 φ_3)))]
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  [(where (((ti_1 ...) _ globals_1 φ_2)
           -> ((ti_2 ...) _ globals_2 φ_3)) tfi)
   (side-condition (satisfies φ_1 φ_2))
   ------------------------------------
   (⊢ S i (_ _ (table j _) _ _ _ _)
      ((call-indirect tfi))
      (((ti_1 ... (i32 a)) locals_1 globals_1 φ_1)
       -> ((ti_2 ...) locals_1 globals_2 φ_3)))]
  
  [(where (((ti_1 ...) _ globals_1 φ_2) -> ((ti_2 ...) _ globals_2 φ_3)) tfi_2)
   (side-condition (satisfies φ_1 φ_2))
   (side-condition (valid-table-call tfi_2 a (tfi ...) φ_1))
   ---------------------------------------------------------
   (⊢ S i (_ _ (table (j (tfi ...))) _ _ _ _)
      ((call-indirect/unsafe tfi_2))
      (((ti_1 ... (i32 a)) locals_1 globals_1 φ_1)
       -> ((ti_2 ...) locals_1 globals_2 φ_3)))]

  [(where t_2 (do-get (t ...) j))
   (where (t_2 a) (do-get locals j))
   ;; a_2 fresh
   ---------------------------------
   (⊢ S i (_ _ _ _ (local (t ...)) _ _)
      ((get-local j))
      ((() locals globals φ)
       -> (((t_2 a_2)) locals globals ((φ (t_2 a_2)) (eq a_2 a)))))]

  [(where t_2 (do-get (t ...) j))
   (where locals_2 (do-set locals_1 j (t_2 a_2)))
   ;; a_2 fresh
   ----------------------------------------------
   (⊢ S i (_ _ _ _ (local (t ...)) _ _)
      ((set-local j))
      ((((t_2 a)) locals_1 globals φ)
       -> (() locals_2 globals ((φ (t_2 a_2)) (eq a_2 a)))))]

  [(where t_2 (do-get (t ...) j))
   (where locals_2 (do-set locals_1 j (t_2 a_2)))
   ;; a_2 fresh
   ----------------------------------------------
   (⊢ S i (_ _ _ _ (local (t ...)) _ _)
      ((tee-local j))
      ((((t_2 a)) locals_1 globals φ)
       -> (((t_2 a)) locals_2 globals ((φ (t_2 a_2)) (eq a_2 a)))))]

  ;; TODO: if not mut, lookup value?
  [(where (mut? t_2) (do-get (tg ...) j))
   (where (t_2 a) (do-get globals j))
   --------------------------------------
   (⊢ S i (_ (global (tg ...)) _ _ _ _ _ _)
      ((get-global j))
      ((() locals globals φ)
       -> (((t_2 a_2)) locals globals ((φ (t_2 a_2)) (eq a_2 a)))))]

  [(where (mut t_2) (do-get (tg ...) j))
   (where globals_2 (do-set globals_1 j (t_2 a_2)))
   ------------------------------------------------
   (⊢ S i (_ (global (tg ...)) _ _ _ _ _ _)
      ((set-global j))
      ((((t_2 a)) locals globals_1 φ)
       -> (() locals globals_2 ((φ (t_2 a_2)) (eq a_2 a)))))]

  [(where (_ _ _ (memory j) _ _ _) C)
   (side-condition ,(< (expt 2 (term j_1))
                       (type-width (term t))))
   (side-condition (satisfies φ_1 ((empty (i32 a))
                                   (and (le (add (add a (i32 j_2)) (i32 ,(/ (type-width (term t)) 8))) (i32 j))
                                        (ge (add a (i32 j_2)) (i32 0))))))
   ;; a_2 fresh
   -----------------------------------------------------------------------
   (⊢ S i C ((t load/unsafe j_1 j_2)) ((((i32 a)) locals globals φ_1)
                                       -> (((t a_2)) locals globals (φ_1 (t a_2)))))]

  [(where (_ _ _ (memory j) _ _ _) C)
   (side-condition ,(< (expt 2 (term j_1))
                       (type-width (term t) (term tp))))
   (side-condition (satisfies φ_1 ((empty (i32 a))
                                   (and (le (add (add a (i32 j_2)) (i32 ,(/ (type-width (term t) (term tp)) 8))) (i32 j))
                                        (ge (add a (i32 j_2)) (i32 0))))))
   ;; a_2 fresh
   -----------------------------------------------------------------------
   (⊢ S i C ((t load/unsafe (tp sz) j_1 j_2)) ((((i32 a)) locals globals φ_1)
                                               -> (((t a_2)) locals globals (φ_1 (t a_2)))))]

  [(where (_ _ _ (memory j) _ _ _) C)
   (side-condition ,(< (expt 2 (term j_1))
                       (type-width (term t))))
   (side-condition (satisfies φ_1 ((empty (i32 a))
                                   (and (le (add (add a (i32 j_2)) (i32 ,(/ (type-width (term t)) 8))) (i32 j))
                                        (ge (add a (i32 j_2)) (i32 0))))))
   -------------------------------------------------------------------------
   (⊢ S i C ((t store/unsafe j_1 j_2)) ((((i32 a) (t a_1)) locals globals φ_1)
                                        -> (() locals globals φ_1)))]

  ;; TODO: no floats yet so not included in side-condition
  [(where (_ _ _ (memory j) _ _ _) C)
   (side-condition ,(< (expt 2 (term j_1))
                       (type-width (term t) (term tp))))
   (side-condition (satisfies φ_1 ((empty (i32 a))
                                   (and (le (add (add a (i32 j_2)) (i32 ,(/ (type-width (term t) (term tp)) 8))) (i32 j))
                                        (ge (add a (i32 j_2)) (i32 0))))))
   ------------------------------------------------------------------------------
   (⊢ S i C ((t store/unsafe (tp) j_1 j_2)) ((((i32 a) (t a_1)) locals globals φ_1)
                                             -> (() locals globals φ_1)))]

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  [-----------------------------------------------------------
   (⊢ S i C () ((() locals globals φ) -> (() locals globals φ)))]

  [(⊢ S i C (e_1 ...) (ticond_1 -> ((ti_2 ...) locals globals φ_2)))
   (⊢ S i C (e_2) (((ti_2 ...) locals globals φ_3) -> ticond_3))
   (side-condition (satisfies φ_2 φ_3))
   --------------------------------------------
   (⊢ S i C (e_1 ... e_2) (ticond_1 -> ticond_3))]

  [(⊢ S i C (e ...) (((ti_1 ...) locals globals φ_1)
                     -> ((ti_2 ...) locals globals φ_2)))
   ------------------------------------------------------
   (⊢ S i C (e ...) (((ti ... ti_1 ...) locals globals φ_1)
                     -> ((ti ... ti_2 ...) locals globals φ_2)))]

  ;; Subtyping
  ;; TODO: This here?
  [(⊢ S i C (e ...) tfi_2)
   (<: tfi_1 tfi_2)
   ---------------------
   (⊢ S i C (e ...) tfi_1)])
