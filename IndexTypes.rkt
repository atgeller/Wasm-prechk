#lang racket

(require redex "WASM-Redex/Syntax.rkt")

(provide WASMIndexTypes)

(define-extended-language WASMIndexTypes WASM
  (binop ::= .... div/unsafe)
  (e ::= .... (call-indirect/unsafe tfi) (if tfi (e ...) (e ...))
     (t load/unsafe j j) (t load/unsafe (tp sz) j j)
     (t store/unsafe j j) (t store/unsafe (tp) j j))

  ;; Index types
  (a ::= variable-not-otherwise-mentioned)
  (x y ::= a (t c) (binop x y))
  (P ::= (testop x) (relop x y) (not P) (and P P) (or P P))
  ;(γ ::= t (a : γ P)) TODO: I don't think we really need these? Syntactic sugar
  (φ ::= empty (φ (t a)) (φ P))

  (ti ::= (t a))
  (mut? ::= boolean)
  (tgi ::= (mut? ti))
  ;; Index-type pre/post-condition: types on stack, locals, globals, and constraint context
  (locals ::= (ti ...))
  (globals ::= (ti ...))
  (ticond ::= ((ti ...) locals globals φ))
  (tfi ::= (ticond -> ticond))

  (C ::= ((func (tfi ...)) (global (tg ...)) (table (j (i ...)) ...) (memory j ...) (local (t ...)) (label (ticond  ...)) (return ticond))
     ((func (tfi ...)) (global (tg ...)) (table (j (i ...)) ...) (memory j ...) (local (t ...)) (label (ticond ...)) (return)))

  (f ::= ((ex ...) (func tfi (local (t ...) (e ...))))))

(define-metafunction WASMIndexTypes
  reverse-get : (any ...) j -> any
  [(reverse-get (any ... any_1) j)
   (reverse-get (any ...) ,(sub1 (term j)))
   (side-condition (< 0 (term j)))]
  [(reverse-get (any ... any_1) 0) any_1])
