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
  [(erase-mut (mut? t)) t]
  [(erase-mut t) t])