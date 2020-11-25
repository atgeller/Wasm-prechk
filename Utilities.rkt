#lang racket

(require redex
         "IndexTypes.rkt"
         "WASM-Redex/Utilities.rkt"
         "WASM-Redex/Bits.rkt")

(provide (all-defined-out))

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
  [(subset any empty) #t]
  [(subset any (any_1 any_2)) (subset any any_1) (where #t (in any_2 any))]
  [(subset any (any_1 any_2)) #f (where #f (in any_2 any))])

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
  build-phi : (a ...) (t ...) (c ...) -> φ
  [(build-phi ()) empty]
  [(build-phi (a_1 ... a_2) (t_1 ... t_2) (c_1 ... c_2)) ((build-phi (a_1 ...) (t_1 ...) (c_1 ...)) (= a_2 (t_2 c_2)))])

(define-metafunction WASMIndexTypes
  domain-x : x -> (a ...)
  [(domain-x (t c)) ()]
  [(domain-x a) (a)]
  [(domain-x (binop x y)) (merge (domain-x x) (domain-x y))]
  [(domain-x (testop x)) (domain-x x)]
  [(domain-x (relop x y)) (merge (domain-x x) (domain-x y))])

(define-metafunction WASMIndexTypes
  domain-P : P -> (a ...)
  [(domain-P (= x y)) (merge (domain-x x) (domain-x y))]
  [(domain-P (if P_1 P_2 P_3)) (merge (merge (domain-P P_1) (domain-P P_2)) (domain-P P_3))]
  [(domain-P (and P_1 P_2)) (merge (domain-P P_1) (domain-P P_2))]
  [(domain-P (or P_1 P_2)) (merge (domain-P P_1) (domain-P P_2))]
  [(domain-P (not P)) (domain-P P)])

(define-metafunction WASMIndexTypes
  domain-φ : φ -> (a ...)
  [(domain-φ empty) ()]
  [(domain-φ (φ P)) (merge (domain-φ φ) (domain-P P))])
