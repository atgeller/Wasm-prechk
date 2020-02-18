#lang racket

(require redex "WASM-Redex/Syntax.rkt")

(provide WASMIndexTypes label-types)

(define-extended-language WASMIndexTypes WASM
  (binop ::= .... div/unsafe)
  (e ::= .... (call-indirect/unsafe tfi) (if tfi (e ...) (e ...)))

  ;; Index types
  (a ::= variable-not-otherwise-mentioned)
  (x y ::= a (t c) (binop x y))
  (P ::= (testop x) (relop x y) (not P) (and P P) (or P P))
  ;(γ ::= t (a : γ P)) TODO: I don't think we really need these? Syntactic sugar
  (φ ::= empty (φ (t a)) (φ P))

  (ti ::= (t a))
  (mut? ::= boolean)
  (tgi ::= (mut? ti))
  ;; Index-type pre/post-condition: types on stack and constraint context
  (ticond ::= ((ti ...) φ))
  (tfi ::= (ticond -> ticond))

  (C ::= ((func (tfi ...)) (global (tgi ...)) (table (j (i ...)) ...) (memory j ...) (local (ti ...)) (label (ticond  ...)) (return ticond))
     ((func (tfi ...)) (global (tgi ...)) (table (j (i ...)) ...) (memory j ...) (local (ti ...)) (label (ticond ...)) (return))))

(define-metafunction WASMIndexTypes
  reverse-get : (any ...) j -> any
  [(reverse-get (any ... any_1) j)
   (reverse-get (any ...) ,(sub1 (term j)))
   (side-condition (< 0 (term j)))]
  [(reverse-get (any ... any_1) 0) any_1])

(define-judgment-form WASMIndexTypes
  #:contract (label-types (ticond ...) (j ...) ticond)
  #:mode (label-types I I O)

  [(where ticond_2 (reverse-get (ticond ...) j))
   ---------------------------------------------
   (label-types (ticond ...) (j) ticond_2)]

  [(where ticond_2 (reverse-get (ticond ...) j))
   (label-types (ticond ...) (j_2 ...) ticond_2)
   ---------------------------------------------
   (label-types (ticond ...) (j j_2 ...) ticond_2)])
