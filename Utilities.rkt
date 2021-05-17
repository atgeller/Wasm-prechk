#lang racket

(require redex
         "IndexTypes.rkt"
         "WASM-Redex/Utilities.rkt")

(provide (all-defined-out))

(define (list-ref-right lst pos)
  (list-ref (reverse lst) pos))

(define-metafunction WASMIndexTypes
  reverse-get : (any ...) j -> any
  [(reverse-get (any ...) j)
   ,(list-ref-right (term (any ...)) (term j))])

(define-metafunction WASMIndexTypes
  extend : φ_1 φ_2 -> φ
  [(extend φ_1 empty) φ_1]
  [(extend φ_1 (φ_2 P)) ((extend φ_1 φ_2) P)]
  [(extend φ_1 (φ_2 (t ivar))) ((extend φ_1 φ_2) (t ivar))])

;; Sets the local variable types, used in the typing rule for functions to set up the context to type check the function body
(define-metafunction WASMIndexTypes
  with-locals : C (t ...) -> C
  [(with-locals ((func tfi_f ...) (global tg ...) (table (n_t tfi_t ...) ...) (memory n_m ...) _ (label ticond_l ...) (return ticond_r ...)) (t ...))
   ((func tfi_f ...) (global tg ...) (table (n_t tfi_t ...) ...) (memory n_m ...) (local t ...) (label ticond_l ...) (return ticond_r ...))])

;; Adds a branch condition (the pre-condition of a branch instruction) onto the label stack.
;; Used in typing rules for block, loop, and if to append the branching condition of the block
(define-metafunction WASMIndexTypes
  add-label : C ticond -> C
  [(add-label ((func tfi_f ...) (global tg ...) (table (n_t tfi_t ...) ...) (memory n_m ...) (local t_l ...) (label ticond_l ...) (return ticond_r ...)) ticond)
   ((func tfi_f ...) (global tg ...) (table (n_t tfi_t ...) ...) (memory n_m ...) (local t_l ...) (label ticond_l ... ticond) (return ticond_r ...))])

;; Sets the return condition, used in the typing rule for functions to set up the context to type check the function body
(define-metafunction WASMIndexTypes
  with-return : C ticond -> C
  [(with-return ((func tfi_f ...) (global tg ...) (table (n_t tfi_t ...) ...) (memory n_m ...) (local t_l ...) (label ticond_l ...) (return _ ...)) ticond)
   ((func tfi_f ...) (global tg ...) (table (n_t tfi_t ...) ...) (memory n_m ...) (local t_l ...) (label ticond_l ...) (return ticond))])

;; Metafunctions for getting data out of a context
(define-metafunction WASMIndexTypes
  context-funcs : C -> (tfi ...)
  [(context-funcs ((func tfi ...) _ _ _ _ _ _)) (tfi ...)])

(define-metafunction WASMIndexTypes
  context-func : C i -> tfi
  [(context-func C i) (index (context-funcs C) i)])

(define-metafunction WASMIndexTypes
  context-globals : C -> (tg ...)
  [(context-globals (_ (global tg ...) _ _ _ _ _)) (tg ...)])

(define-metafunction WASMIndexTypes
  context-global : C i -> tg
  [(context-global C i) (index (context-globals C) i)])

(define-metafunction WASMIndexTypes
  context-table : C -> (n tfi ...)
  [(context-table (_ _ (table (n tfi ...)) _ _ _ _)) (n tfi ...)])

(define-metafunction WASMIndexTypes
  context-memory : C -> n
  [(context-memory (_ _ _ (memory n) _ _ _)) n])

(define-metafunction WASMIndexTypes
  context-locals : C -> (t ...)
  [(context-locals (_ _ _ _ (local t ...) _ _)) (t ...)])

(define-metafunction WASMIndexTypes
  context-local : C i -> t
  [(context-local C i) (index (context-locals C) i)])

(define-metafunction WASMIndexTypes
  context-labels : C -> (ticond ...)
  [(context-labels (_ _ _ _ _ (label ticond ...) _)) (ticond ...)])

(define-metafunction WASMIndexTypes
  context-label : C i -> ticond
  [(context-label C i) (reverse-get (context-labels C) i)])

(define-metafunction WASMIndexTypes
  context-return : C -> ticond
  [(context-return (_ _ _ _ _ _ (return ticond))) ticond])

(define-metafunction WASMIndexTypes
  erase-mut : tg -> t
  [(erase-mut (mut? t)) t]
  [(erase-mut t) t])

(define-metafunction WASMIndexTypes
  in : any any -> boolean
  [(in _ empty) #f]
  [(in any_1 (any any_1)) #t]
  [(in any_1 (any any_2)) (in any_1 any)])

(define-metafunction WASMIndexTypes
  union : any any -> any
  [(union any empty) any]
  [(union any (any_1 any_2)) (union any any_1) (where #t (in any_2 any))]
  [(union any (any_1 any_2)) ((union any any_1) any_2) (where #f (in any_2 any))])

(define-metafunction WASMIndexTypes
  subset : any any -> boolean
  [(subset empty any) #t]
  [(subset (any_1 any_2) any) (subset any_1 any) (where #t (in any_2 any))]
  [(subset (any_1 any_2) any) #f (where #f (in any_2 any))])

(define-metafunction WASMIndexTypes
  superset : any any -> boolean
  [(superset any any) #t]
  [(superset any_1 any_2) #t (where #f (subset any_1 any_2))]
  [(superset any_1 any_2) #f (where #t (subset any_1 any_2))])

(define-metafunction WASMIndexTypes
  merge : (any ...) (any ...) -> (any ...)
  [(merge (any_1 ...) (any_2 ...)) (any_1 ... any_2 ...)])

(define-metafunction WASMIndexTypes
  contains-all : any (any ...) -> boolean
  [(contains-all any ()) #t]
  [(contains-all any (any_1 any_2 ...)) (contains-all any (any_2 ...)) (where #t (in any_1 any))]
  [(contains-all any (any_1 any_2 ...)) #f (where #f (in any_1 any))])

(define-metafunction WASMIndexTypes
  build-gamma : (ti ...) -> Γ
  [(build-gamma ()) empty]
  [(build-gamma (ti_1 ... ti_2)) ((build-gamma (ti_1 ...)) ti_2) (where #f (in ti_2 (build-gamma (ti_1 ...))))]
  [(build-gamma (ti_1 ... ti_2)) (build-gamma (ti_1 ...)) (where #t (in ti_2 (build-gamma (ti_1 ...))))])

(define-metafunction WASMIndexTypes
  equiv-gammas : Γ Γ -> boolean
  [(equiv-gammas Γ_1 Γ_2) #t (where (#t #t) ((superset Γ_1 Γ_2) (subset Γ_1 Γ_2)))])

(define-metafunction WASMIndexTypes
  build-phi : (t ...) (ivar ...) (c ...) -> φ
  [(build-phi () () ()) empty]
  [(build-phi (t_1 ... t_2) (ivar_1 ... ivar_2) (c_1 ... c_2)) ((build-phi (t_1 ...) (ivar_1 ...) (c_1 ...)) (= ivar_2 (t_2 c_2)))])

(define-metafunction WASMIndexTypes
  build-phi-zeros : (t ...) (ivar ...) -> φ
  [(build-phi-zeros () ()) empty]
  [(build-phi-zeros (t_1 ... t_2) (ivar_1 ... ivar_2) ) ((build-phi-zeros (t_1 ...) (ivar_1 ...)) (= ivar_2 (t_2 0)))])

(define-metafunction WASMIndexTypes
  domain-x : x -> (ivar ...)
  [(domain-x (t c)) ()]
  [(domain-x ivar) (ivar)]
  [(domain-x (binop x y)) (merge (domain-x x) (domain-x y))]
  [(domain-x (testop x)) (domain-x x)]
  [(domain-x (relop x y)) (merge (domain-x x) (domain-x y))])

(define-metafunction WASMIndexTypes
  domain-P : P -> (ivar ...)
  [(domain-P (= x y)) (merge (domain-x x) (domain-x y))]
  [(domain-P (if P_1 P_2 P_3)) (merge (merge (domain-P P_1) (domain-P P_2)) (domain-P P_3))]
  [(domain-P (and P_1 P_2)) (merge (domain-P P_1) (domain-P P_2))]
  [(domain-P (or P_1 P_2)) (merge (domain-P P_1) (domain-P P_2))]
  [(domain-P (not P)) (domain-P P)])

(define-metafunction WASMIndexTypes
  domain-φ : φ -> (ivar ...)
  [(domain-φ empty) ()]
  [(domain-φ (φ P)) (merge (domain-φ φ) (domain-P P))])

(define-metafunction WASMIndexTypes
  domain-Γ : Γ -> (ivar ...)
  [(domain-Γ empty) ()]
  [(domain-Γ (Γ (t ivar)))
   (ivar ivar_rest ...)
   (where (ivar_rest ...) (domain-Γ Γ))])

;; returns true if everything in the list is the same as the second argument,
;; otherwise returns false
(define-metafunction WASMIndexTypes
  same : (any ...) any -> boolean
  [(same () any) #t]
  [(same (any_!_ any_rest ...) any_!_) #f]
  [(same (any any_rest ...) any)
   (same (any_rest ...) any)])
