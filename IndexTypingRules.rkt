#lang racket

(require redex
         "IndexTypes.rkt"
         "SubTyping.rkt"
         "TableValidation.rkt"
         "Utilities.rkt"
         "WASM-Redex/Utilities.rkt")

(provide ⊢ tfi-ok)

(define-metafunction WASMIndexTypes
  tfi-ok : tfi -> boolean
  [(tfi-ok (((ti_1 ...) locals_1 φ_1) -> ((ti_2 ...) locals_2 φ_2)))
   ,(and (subset? (term (domain-φ φ_1)) (term (domain-tis (merge (ti_1 ...) locals_1))))
         (subset? (term (domain-φ φ_2)) (term (domain-tis (merge (merge (ti_1 ...) locals_1) (merge (ti_2 ...) locals_2)))))
         (term (distinct (domain-tis (merge (merge (ti_1 ...) locals_1) (merge (ti_2 ...) locals_2))))))])

(define-judgment-form WASMIndexTypes
  #:contract (⊢ C (e ...) tficond)

  [(where #f (in ivar Γ)) ;; ivar fresh
   --- "Const"
   (⊢ C ((t const c)) ((() locals Γ φ) -> (((t ivar)) locals (Γ (t ivar)) (φ (= ivar (t c))))))]

  [(where #f (in ivar_2 Γ)) ;; ivar fresh
   --- "Unop"
   (⊢ C ((t unop)) ((((t ivar_1)) locals Γ φ) -> (((t ivar_2)) locals (Γ (t ivar_2)) (φ (= ivar_2 ((t unop) ivar_1))))))]

  [(side-condition (satisfies Γ φ (empty (not (= ivar_2 (t 0))))))
   (where #f (in ivar_3 Γ)) ;; ivar_3 fresh
   ---------------------------------------------------------- "Div-S-Prechk"
   (⊢ C ((t div-s/unsafe)) ((((t ivar_1) (t ivar_2)) locals Γ φ)
                            -> (((t ivar_3)) locals (Γ (t ivar_3)) (φ (= ivar_3 ((t div-s) ivar_1 ivar_2))))))]

  [(side-condition (satisfies Γ φ (empty (not (= ivar_2 (t 0))))))
   (where #f (in ivar_3 Γ)) ;; ivar_3 fresh
   ---------------------------------------------------------- "Div-U-Prechk"
   (⊢ C ((t div-u/unsafe)) ((((t ivar_1) (t ivar_2)) locals Γ φ)
                            -> (((t ivar_3)) locals (Γ (t ivar_3)) (φ (= ivar_3 ((t div-u) ivar_1 ivar_2))))))]

  [(side-condition (satisfies Γ φ (empty (not (= ivar_2 (t 0))))))
   (where #f (in ivar_3 Γ)) ;; ivar_3 fresh
   ---------------------------------------------------------- "Rem-S-Prechk"
   (⊢ C ((t rem-s/unsafe)) ((((t ivar_1) (t ivar_2)) locals Γ φ)
                            -> (((t ivar_3)) locals (Γ (t ivar_3)) (φ (= ivar_3 ((t rem-s) ivar_1 ivar_2))))))]

  [(side-condition (satisfies Γ φ (empty (not (= ivar_2 (t 0))))))
   (where #f (in ivar_3 Γ)) ;; ivar_3 fresh
   ---------------------------------------------------------- "Rem-U-Prechk"
   (⊢ C ((t rem-u/unsafe)) ((((t ivar_1) (t ivar_2)) locals Γ φ)
                            -> (((t ivar_3)) locals (Γ (t ivar_3)) (φ (= ivar_3 ((t rem-u) ivar_1 ivar_2))))))]

  [(where (binop_!_1 binop_!_1 binop_!_1) (binop div-s/unsafe div-u/unsafe))
   (where (binop_!_1 binop_!_1 binop_!_1) (binop rem-s/unsafe rem-u/unsafe))
   (where #f (in ivar_3 Γ)) ;; ivar_3 fresh
   ------------------------------------------------ "Binop"
   (⊢ C ((t binop)) ((((t ivar_1) (t ivar_2)) locals Γ φ)
                     -> (((t ivar_3)) locals (Γ (t ivar_3)) (φ (= ivar_3 ((t binop) ivar_1 ivar_2))))))]

  [(where #f (in ivar_2 Γ)) ;; ivar_2 fresh
   -------- "Testop"
   (⊢ C ((t testop)) ((((t ivar)) locals Γ φ)
                      -> (((i32 ivar_2)) locals (Γ (i32 ivar_2)) (φ (= ivar_2 ((t testop) ivar))))))]

  [(where #f (in ivar_3 Γ)) ;; ivar_3 fresh
   ------- "Relop"
   (⊢ C ((t relop)) ((((t ivar_1) (t ivar_2)) locals Γ φ)
                     -> (((t ivar_3)) locals (Γ (t ivar_3)) (φ (= ivar_3 ((t relop) ivar_1 ivar_2))))))]

  [(where (t_!_1 t_!_1) (t_1 t_2))
   (side-condition ,(or (and (term (inn? t_1)) (term (inn? t_2))
                             (< (term (bit-width t_1)) (term (bit-width t_2))))
                        (and (term (fnn? t_1)) (term (fnn? t_2)))))
   (where #f (in ivar_1 Γ)) ;; ivar_1 fresh
   ---------------------------------------------------------------------------- "Convert"
   (⊢ C ((t_1 convert t_2)) ((((t_2 ivar_2)) locals Γ φ)
                             -> (((t_1 ivar_1)) locals (Γ (t_1 ivar_1)) (φ (= ivar_1 ((t_1 convert t_2) ivar_2))))))]

  [(where (t_!_1 t_!_1) (t_1 t_2))
   (side-condition ,(nor (and (term (inn? t_1)) (term (inn? t_2))
                              (< (term (bit-width t_1)) (term (bit-width t_2))))
                         (and (term (fnn? t_1)) (term (fnn? t_2)))))
   (where #f (in ivar_1 Γ)) ;; ivar_1 fresh
   ----------------------------------------------------------------------------- "Convert-SX"
   (⊢ C ((t_1 convert t_2 sx)) ((((t_2 ivar_2)) locals Γ φ)
                                -> (((t_1 ivar_1)) locals (Γ (t_1 ivar_1)) (φ (= ivar_1 ((t_1 convert t_2 sx) ivar_2))))))]

  [(where (t_!_1 t_!_1) (t_1 t_2))
   (side-condition ,(= (term (bit-width t_1)) (term (bit-width t_2))))
   (where #f (in ivar_1 Γ)) ;; ivar_1 fresh
   ------------------------------------------------------------------- "Reinterpret"
   (⊢ C ((t_1 reinterpret t_2)) ((((t_2 ivar_2)) locals Γ φ)
                                 -> (((t_1 ivar_1)) locals (Γ (t_1 ivar_1)) (φ (= ivar_1 ((t_1 reinterpret t_2) ivar_2))))))]

  [(side-condition (equiv-gammas Γ_2 (build-gamma (merge (ti_2 ...) ((t ivar) ...)))))
   (where (t ...) (context-locals C))
   --- "Unreachable"
   (⊢ C (unreachable) (((ti_1 ...) locals Γ_1 φ) -> ((ti_2 ...) ((t ivar) ...) Γ_2 (empty ⊥))))]

  [--- "Nop"
   (⊢ C (nop) ((() locals Γ φ) -> (() locals Γ φ)))]

  [--- "Drop"
   (⊢ C (drop) ((((t ivar)) locals Γ φ) -> (() locals Γ φ)))]

  [(where #f (in ivar_3 Γ)) ;; ivar_3 fresh
   --- "Select"
   (⊢ C (select) ((((t ivar_1) (t ivar_2) (i32 ivar)) locals Γ φ)
                  -> (((t ivar_3)) locals (Γ (t ivar))
                                   (φ (if (= ivar (i32 0))
                                          (= ivar_3 ivar_2)
                                          (= ivar_3 ivar_1))))))]
  
  [(where C_2 (add-label C_1 ((ti_3 ...) locals_3 φ_3)))
   (⊢ C_2 (e ...) (((ti_2 ...) locals_2 Γ_2 φ_2) -> ((ti_5 ...) locals_5 Γ_5 φ_5)))
   (side-condition (equiv-gammas Γ_2 (build-gamma (merge (ti_2 ...) locals_2))))
   (side-condition (satisfies Γ_1 φ_1 (substitute-ivars (merge (ti_1 ...) locals_1)
                                                        (merge (ti_2 ...) locals_2)
                                                        φ_2))) ;; Strengthen precondition outside
   (side-condition (satisfies Γ_5 φ_5 (substitute-ivars (merge (merge (ti_1 ...) locals_1) (merge (ti_5 ...) locals_5))
                                                        (merge (merge (ti_2 ...) locals_2) (merge (ti_3 ...) locals_3))
                                                        φ_3))) ;; Weaken postcondition inside
   (side-condition (tfi-ok (((ti_2 ...) locals_2 φ_2) -> ((ti_3 ...) locals_3 φ_3))))
   (side-condition (distinct (merge (domain-tis (merge (ti_4 ...) locals_4)) (domain-Γ Γ_1))))
   (side-condition (equiv-gammas Γ_4 (union Γ_1 (build-gamma (merge (ti_4 ...) locals_4)))))
   (where φ_4 (union φ_1 (substitute-ivars (merge (ti_4 ...) locals_4)
                                           (merge (ti_3 ...) locals_3)
                                           φ_3)))
   --------------------------- "Block"
   (⊢ C_1 ((block (((ti_2 ...) locals_2 φ_2) -> ((ti_3 ...) locals_3 φ_3)) (e ...)))
      (((ti_1 ...) locals_1 Γ_1 φ_1) -> ((ti_4 ...) locals_4 Γ_4 φ_4)))]

  [(where C_2 (add-label C_1 ((ti_2 ...) locals_2 φ_2)))
   (⊢ C_2 (e ...) (((ti_2 ...) locals_2 Γ_2 φ_2) -> ((ti_5 ...) locals_5 Γ_5 φ_5)))
   (side-condition (equiv-gammas Γ_2 (build-gamma (merge (ti_2 ...) locals_2))))
   (side-condition (satisfies Γ_1 φ_1 (substitute-ivars (merge (ti_1 ...) locals_1)
                                                        (merge (ti_2 ...) locals_2)
                                                        φ_2))) ;; Strengthen precondition outside
   (side-condition (satisfies Γ_5 φ_5 (substitute-ivars (merge (merge (ti_1 ...) locals_1) (merge (ti_5 ...) locals_5))
                                                        (merge (merge (ti_2 ...) locals_2) (merge (ti_3 ...) locals_3))
                                                        φ_3))) ;; Weaken postcondition inside
   (side-condition (tfi-ok (((ti_2 ...) locals_2 φ_2) -> ((ti_3 ...) locals_3 φ_3))))
   (side-condition (distinct (merge (domain-tis (merge (ti_4 ...) locals_4)) (domain-Γ Γ_1))))
   (side-condition (equiv-gammas Γ_4 (union Γ_1 (build-gamma (merge (ti_4 ...) locals_4)))))
   (where φ_4 (union φ_1 (substitute-ivars (merge (ti_4 ...) locals_4)
                                           (merge (ti_3 ...) locals_3)
                                           φ_3)))
   --------------------------- "Loop"
   (⊢ C_1 ((loop (((ti_2 ...) locals_2 φ_2) -> ((ti_3 ...) locals_3 φ_3)) (e ...)))
      (((ti_1 ...) locals_1 Γ_1 φ_1) -> ((ti_4 ...) locals_4 Γ_4 φ_4)))]

  [(where C_2 (add-label C_1 ((ti_2 ...) locals_2 φ_2)))
   (⊢ C_2 (e_1 ...) (((ti_2 ...) locals_2 Γ_2 φ_2)
                     -> ((ti_5 ...) locals_5 Γ_5 φ_5)))
   (⊢ C_2 (e_2 ...) (((ti_2 ...) locals_2 Γ_2 φ_2)
                     -> ((ti_6 ...) locals_6 Γ_6 φ_6)))
   (side-condition (equiv-gammas Γ_2 (build-gamma (merge (ti_2 ...) locals_2)))) ;; Γ_2 = ti_1 ... locals_1
   (side-condition (satisfies Γ_1 φ_1 (substitute-ivars (merge (ti_1 ...) locals_1)
                                                        (merge (ti_2 ...) locals_2)
                                                        φ_2))) ;; Strengthen precondition outside
   (side-condition (satisfies Γ_5 φ_5 (substitute-ivars (merge (merge (ti_1 ...) locals_1) (merge (ti_5 ...) locals_5))
                                                        (merge (merge (ti_2 ...) locals_2) (merge (ti_3 ...) locals_3))
                                                        φ_3))) ;; Weaken postcondition inside then
   (side-condition (satisfies Γ_6 φ_6 (substitute-ivars (merge (merge (ti_1 ...) locals_1) (merge (ti_6 ...) locals_6))
                                                        (merge (merge (ti_2 ...) locals_2) (merge (ti_3 ...) locals_3))
                                                        φ_3))) ;; Weaken postcondition inside else
   (side-condition (tfi-ok (((ti_2 ...) locals_2 φ_2) -> ((ti_3 ...) locals_3 φ_3))))
   (side-condition (distinct (merge (domain-tis (merge (ti_4 ...) locals_4)) (domain-Γ Γ_1))))
   (side-condition (equiv-gammas Γ_4 (union Γ_1 (build-gamma (merge (ti_4 ...) locals_4)))))
   (where φ_4 (union φ_1 (substitute-ivars (merge (ti_4 ...) locals_4)
                                           (merge (ti_3 ...) locals_3)
                                           φ_3)))
   --------------------------------------------------------------------- "If"
   (⊢ C_1 ((if (((ti_2 ...) locals_2 φ_2) -> ((ti_3 ...) locals_3 φ_3)) (e_1 ...) (e_2 ...)))
      (((ti_1 ...) locals_1 Γ_1 φ_1) -> ((ti_4 ...) locals_4 Γ_4 φ_4)))]

  [(where ((ti_pat ...) locals_pat φ) (reverse-get (context-labels C) j))
   (side-condition (satisfies Γ_1 φ_1 (substitute-ivars (merge (ti ...) locals) (merge (ti_pat ...) locals_pat) φ)))
   (side-condition (equiv-gammas Γ_2 (build-gamma (merge (ti_2 ...) ((t_l ivar_l) ...)))))
   (where (t_l ...) (context-locals C))
   -------------------------------------------------------- "Br"
   (⊢ C ((br j))
      (((ti_1 ... ti ...) locals Γ_1 φ_1)
       -> ((ti_2 ...) ((t_l ivar_l) ...) Γ_2 (empty ⊥))))]

  [(where ((ti_pat ...) locals_pat φ) (reverse-get (context-labels C) j))
   (side-condition (satisfies Γ_1 φ_1 (substitute-ivars (merge (ti ...) locals) (merge (ti_pat ...) locals_pat) (φ (not (= ivar (i32 0)))))))
   ------------------------------------------------------------------------------ "Br-If"
   (⊢ C ((br-if j))
      (((ti ... (i32 ivar)) locals Γ_1 φ_1)
       -> ((ti ...) locals Γ_1 (φ_1 (= ivar (i32 0))))))]

  [(where (((ti_pat ...) locals_pat φ) ...) ((reverse-get (context-labels C) j) ...))
   (where (ti_s ...) (merge (ti_3 ...) locals))
   (side-condition (satisfies-all Γ_1 φ_1 ((substitute-ivars (ti_s ...) (merge (ti_pat ...) locals_pat) φ) ...)))
   (side-condition (equiv-gammas Γ_2 (build-gamma (merge (ti_2 ...) ((t_l ivar_l) ...)))))
   (where (t_l ...) (context-locals C))
   -------------------------------------------------------------- "Br-Table"
   (⊢ C ((br-table j ...))
      (((ti_1 ... ti_3 ... (i32 ivar)) locals Γ_1 φ_1)
       -> ((ti_2 ...) ((t_l ivar_l) ...) Γ_2 (empty ⊥))))]

  [(where ((ti_pat ...) _ φ) (context-return C))
   (side-condition (satisfies Γ_1 φ_1 (substitute-ivars (ti ...) (ti_pat ...) φ))) ;; Strengthen precondition
   (side-condition (equiv-gammas Γ_2 (build-gamma (merge (ti_2 ...) ((t_l ivar_l) ...)))))
   (where (t_l ...) (context-locals C))
   -------------------------------------- "Return"
   (⊢ C (return)
      (((ti_1 ... ti ...) locals Γ_1 φ_1) -> ((ti_2 ...) ((t_l ivar_l) ...) Γ_2 (empty ⊥))))]

  ;; Only works if Function is internal
  ;; Justin - Actually, I think this works fine, functions imported from other contexts have to
  ;;          have a type declaration in the context that they're called from.
  ;; Adam - This is the same as in the thesis
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  [(where (((ti_2 ...) _ φ_2) -> ((ti_3 ...) _ φ_3)) (context-func C j))
   (side-condition (tfi-ok (((ti_2 ...) () φ_2) -> ((ti_3 ...) () φ_3))))
   (side-condition (satisfies Γ_1 φ_1 (substitute-ivars (ti_1 ...) (ti_2 ...) φ_2))) ;; Strengthen precondition
   (side-condition (distinct (merge (domain-tis (ti_4 ...)) (domain-Γ Γ_1))))
   (side-condition (equiv-gammas Γ_4 (union Γ_1 (build-gamma (ti_4 ...)))))
   (where φ_4 (union φ_1 (substitute-ivars (ti_4 ...) (ti_3 ...) φ_3)))
   --------------------------- "Call"
   (⊢ C ((call j))
      (((ti_1 ...) locals Γ_1 φ_1)
       -> ((ti_4 ...) locals Γ_4 φ_4)))]
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  ;; TODO: Do we want to allow for indexed types on non-prechk call-indirect?
  [(where (j _ ...) (context-table C))
   (side-condition (tfi-ok (((ti_2 ...) () φ_2) -> ((ti_3 ...) () φ_3))))
   (side-condition (satisfies Γ_1 φ_1 (substitute-ivars (ti_1 ...) (ti_2 ...) φ_2))) ;; Strengthen precondition
   (side-condition (distinct (merge (domain-tis (ti_4 ...)) (domain-Γ Γ_1))))
   (side-condition (equiv-gammas Γ_4 (union Γ_1 (build-gamma (ti_4 ...)))))
   (where φ_4 (union φ_1 (substitute-ivars (ti_4 ...) (ti_3 ...) φ_3)))
   --------------------------- "Call-Indirect"
   (⊢ C ((call-indirect (((ti_2 ...) () φ_2) -> ((ti_3 ...) () φ_3))))
      (((ti_1 ... (i32 ivar)) locals Γ_1 φ_1)
       -> ((ti_4 ...) locals Γ_4 φ_4)))]
  
  [(where (j tfi ...) (context-table C))
   (side-condition (tfi-ok (((ti_2 ...) () φ_2) -> ((ti_3 ...) () φ_3))))
   (side-condition (satisfies Γ_1 φ_1 (substitute-ivars (ti_1 ...) (ti_2 ...) φ_2))) ;; Strengthen precondition
   (side-condition (valid-table-call (((ti_2 ...) () φ_2) -> ((ti_3 ...) () φ_3)) ivar (tfi ...) Γ_1 φ_1))
   (side-condition (distinct (merge (domain-tis (ti_4 ...)) (domain-Γ Γ_1))))
   (side-condition (equiv-gammas Γ_4 (union Γ_1 (build-gamma (ti_4 ...)))))
   (where φ_4 (union φ_1 (substitute-ivars (ti_4 ...) (ti_3 ...) φ_3)))
   ------------------------------------------------------- "Call-Indirect-Prechk"
   (⊢ C ((call-indirect/unsafe (((ti_2 ...) () φ_2) -> ((ti_3 ...) () φ_3))))
      (((ti_1 ... (i32 ivar)) locals Γ_1 φ_1)
       -> ((ti_4 ...) locals Γ_4 φ_4)))]

  [(where t_2 (context-local C j))
   (where (t_2 ivar) (index locals j))
   (where #f (in ivar_2 Γ)) ;; ivar_2 fresh
   --------------------------------- "Get-Local"
   (⊢ C ((get-local j))
      ((() locals Γ φ)
       -> (((t_2 ivar_2)) locals (Γ (t_2 ivar_2)) (φ (= ivar_2 ivar)))))]

  [(where t_2 (context-local C j))
   (where locals_2 (with-index locals_1 j (t_2 ivar)))
   -------------------------------------------- "Set-Local"
   (⊢ C ((set-local j))
      ((((t_2 ivar)) locals_1 Γ φ)
       -> (() locals_2 Γ φ)))]

  [(where t_2 (context-local C j))
   (where locals_2 (with-index locals_1 j (t_2 ivar)))
   (where #f (in ivar_2 Γ)) ;; ivar_2 fresh
   ---------------------------------- "Tee-Local"
   (⊢ C ((tee-local j))
      ((((t_2 ivar)) locals_1 Γ φ)
       -> (((t_2 ivar_2)) locals_2 (Γ (t_2 ivar_2)) (φ (= ivar_2 ivar)))))]

  [(where (_ t_2) (context-global C j))
   (where #f (in ivar Γ)) ;; ivar fresh
   ------------------- "Get-Global"
   (⊢ C ((get-global j))
      ((() locals Γ φ)
       -> (((t_2 ivar)) locals (Γ (t_2 ivar)) φ)))]

  [(where (var t_2) (context-global C j))
   ------------------------------------ "Set-Global"
   (⊢ C ((set-global j))
      ((((t_2 ivar)) locals Γ φ)
       -> (() locals Γ φ)))]

  [(where n (context-memory C))
   (side-condition ,(<= (expt 2 (term a)) (/ (term (bit-width t)) 8)))
   (side-condition (satisfies Γ φ_1 (empty
                                     (and (= (i32 1) ((i32 le-u) ((i32 add) ((i32 add) ivar (i32 o)) (i32 ,(/ (term (bit-width t)) 8))) (i32 n)))
                                          (= (i32 1) ((i32 ge-u) ((i32 add) ivar (i32 o)) (i32 0)))))))
   (where #f (in ivar_2 Γ)) ;; ivar_2 fresh
   ----------------------------------------------------------------------- "Load-Prechk"
   (⊢ C ((t load/unsafe a o)) ((((i32 ivar)) locals Γ φ_1)
                                     -> (((t ivar_2)) locals (Γ (t ivar_2)) φ_1)))]

  [(where n (context-memory C))
   (side-condition ,(<= (expt 2 (term a)) (/ (term (packed-bit-width tp)) 8)))
   (side-condition ,(< (term (packed-bit-width tp)) (term (bit-width t))))
   (side-condition (satisfies Γ φ_1 (empty
                                     (and (= (i32 1) ((i32 le-u) ((i32 add) ((i32 add) ivar (i32 o)) (i32 ,(/ (term (packed-bit-width tp)) 8))) (i32 n)))
                                          (= (i32 1) ((i32 ge-u) ((i32 add) ivar (i32 o)) (i32 0)))))))
   (where inn t)
   (where #f (in ivar_2 Γ)) ;; ivar_2 fresh
   ----------------------------------------------------------------------- "Load-Packed-Prechk"
   (⊢ C ((t load/unsafe (tp sz) a o)) ((((i32 ivar)) locals Γ φ_1)
                                           -> (((t ivar_2)) locals (Γ (t ivar_2)) φ_1)))]

  [(where n (context-memory C))
   (side-condition ,(<= (expt 2 (term a)) (/ (term (bit-width t)) 8)))
   (side-condition (satisfies Γ φ_1 (empty
                                     (and (= (i32 1) ((i32 le-u) ((i32 add) ((i32 add) ivar (i32 o)) (i32 ,(/ (term (bit-width t)) 8))) (i32 n)))
                                          (= (i32 1) ((i32 ge-u) ((i32 add) ivar (i32 o)) (i32 0)))))))
   ------------------------------------------------------------------------- "Store-Prechk"
   (⊢ C ((t store/unsafe a o)) ((((i32 ivar) (t ivar_1)) locals Γ φ_1)
                                    -> (() locals Γ φ_1)))]

  [(where n (context-memory C))
   (side-condition ,(<= (expt 2 (term a)) (/ (term (packed-bit-width tp)) 8)))
   (side-condition ,(< (term (packed-bit-width tp)) (term (bit-width t))))
   (side-condition (satisfies Γ φ_1 (empty
                                     (and (= (i32 1) ((i32 le-u) ((i32 add) ((i32 add) ivar (i32 o)) (i32 ,(/ (term (packed-bit-width tp)) 8))) (i32 n)))
                                          (= (i32 1) ((i32 ge-u) ((i32 add) ivar (i32 o)) (i32 0)))))))
   (where inn t)
   ------------------------------------------------------------------------------ "Store-Packed-Prechk"
   (⊢ C ((t store/unsafe tp a o)) ((((i32 ivar) (t ivar_1)) locals Γ φ_1)
                                   -> (() locals Γ φ_1)))]
  
  [(where n (context-memory C))
   (side-condition ,(<= (expt 2 (term a)) (/ (term (bit-width t)) 8)))
   (where #f (in ivar_2 Γ)) ;; ivar_2 fresh
   ------------------------------------------------------------- "Load"
   (⊢ C ((t load a o)) ((((i32 ivar_1)) locals Γ φ) -> (((t ivar)) locals (Γ (t ivar_2)) φ)))]

  [(where n (context-memory C))
   (side-condition ,(<= (expt 2 (term a)) (/ (term (packed-bit-width tp)) 8)))
   (side-condition ,(< (term (packed-bit-width tp)) (term (bit-width t))))
   (where inn t)
   (where #f (in ivar_2 Γ)) ;; ivar_2 fresh
   ----------------------------------------------------------------------- "Load-Packed"
   (⊢ C ((t load (tp sx) a o)) ((((i32 ivar_1)) locals Γ φ) -> (((t ivar)) locals (Γ (t ivar_2)) φ)))]

  [(where n (context-memory C))
   (side-condition ,(<= (expt 2 (term a)) (/ (term (bit-width t)) 8)))
   ------------------------------------------------------------- "Store"
   (⊢ C ((t store a o)) ((((i32 ivar_1) (t ivar_2)) locals Γ φ) -> (() locals Γ φ)))]

  [(where n (context-memory C))
   (side-condition ,(<= (expt 2 (term a)) (/ (term (packed-bit-width tp)) 8)))
   (side-condition ,(< (term (packed-bit-width tp)) (term (bit-width t))))
   (where inn t)
   ----------------------------------------------------------------------- "Store-Packed"
   (⊢ C ((t store tp a o)) ((((i32 ivar_1) (t ivar_2)) locals Γ φ) -> (() locals Γ φ)))]

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  [------------------------------------------ "Empty"
   (⊢ C () ((() locals Γ φ) -> (() locals Γ φ)))]

  [(⊢ C (e_1 ...) (ticond_1 -> ticond_2))
   (⊢ C (e_2) (ticond_2 -> ticond_3))
   -------------------------------------------- "Composition"
   (⊢ C (e_1 ... e_2) (ticond_1 -> ticond_3))]

  ;; Stack polymorphism
  ;; TODO: check that ti ... are in Γ_1 and Γ_2
  [(⊢ C (e ...) (((ti_1 ...) locals Γ_1 φ_1)
                   -> ((ti_2 ...) locals Γ_2 φ_2)))
   ------------------------------------------------------ "Stack-Poly"
   (⊢ C (e ...) (((ti ... ti_1 ...) locals Γ_1 φ_1)
                   -> ((ti ... ti_2 ...) locals Γ_2 φ_2)))])
