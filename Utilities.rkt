#lang racket

(require redex
         "IndexTypes.rkt"
         "SubTyping.rkt"
         "TableValidation.rkt"
         "WASM-Redex/Utilities.rkt"
         "WASM-Redex/Bits.rkt")

(provide (all-defined-out))

(define-judgment-form WASMIndexTypes
  #:contract (label-types (ticond ...) (j ...) ticond)
  #:mode (label-types I I I)

  [(label-types (ticond ...) () ticond_3)]

  [(where ((ti_2 ...) locals_2 Γ_2 φ_2) (reverse-get (ticond ...) j))
   (side-condition (satisfies (union Γ_1 Γ_2) φ_1 φ_2))
   ;; TODO: (side-condition (subset Γ_2 Γ_1))
   (label-types (ticond ...) (j_2 ...) ((ti_1 ...) locals_1 Γ_1 φ_1))
   ------------------------------------------------------------------
   (label-types (ticond ...) (j j_2 ...) ((ti_1 ...) locals_1 Γ_1 φ_1))])

(define-metafunction WASMIndexTypes
  valid-table-call : tfi a (tfi ...) Γ φ -> boolean
  [(valid-table-call tfi a (tfi_2 ...) Γ φ)
   ,(check-table-call (term tfi) (term a) (term (tfi_2 ...)) (term Γ) (term φ))])

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
