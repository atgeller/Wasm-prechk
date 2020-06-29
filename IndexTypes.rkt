#lang racket

(require redex "WASM-Redex/Syntax.rkt")

(provide WASMIndexTypes add-vars)

(define-extended-language WASMIndexTypes WASM
  (binop ::= .... div/unsafe)
  (e ::= .... (call-indirect/unsafe tfi) (if tfi (e ...) (e ...))
     (t load/unsafe j j) (t load/unsafe (tp sz) j j)
     (t store/unsafe j j) (t store/unsafe (tp) j j))

  ;; Index language
  (a ::= variable-not-otherwise-mentioned)
  (x y ::= a (t c) (binop x y))
  (P ::= (testop x) (relop x y) (not P) (and P P) (or P P))
  (φ ::= empty (φ (t a)) (φ P))
  (ti ::= (t a))  

  ;; Instruction index types
  (locals ::= (ti ...))
  (globals ::= (ti ...))
  ;; Index-type pre/post-condition: types on stack, locals, globals, and constraint context
  (ticond ::= ((ti ...) locals globals φ))
  (tfi ::= (ticond -> ticond))

  ;; Indexed module contexts
  (C ::= ((func (tfi ...)) (global (tg ...)) (table (j (tfi ...)) ...) (memory j ...) (local (t ...)) (label (ticond  ...)) (return ticond))
     ((func (tfi ...)) (global (tg ...)) (table (j (tfi ...)) ...) (memory j ...) (local (t ...)) (label (ticond ...)) (return)))

  (S ::= ((C ...) (table ((j (tfi ...)) ...)) (memory (j ...))))

  ;; Module-level indexed declarations
  (f ::= ((ex ...) (func tfi (local (t ...) (e ...))))
     ((ex ...) (func tfi im)))
  (glob ::= ((ex ...) (global tg (e ...)))
        ((ex ...) (global tg im)))
  (tab ::= ((ex ...) (table j (tfi ...)))
       ((ex ...) (table j (tfi ...) im)))
  (mem ::= ((ex ...) (memory i))
       ((ex ...) (memory i im)))
  (im ::= (import string string))
  (ex ::= (export string))
  (m ::= (module (f ...) (glob ...) (tab ...) (mem ...))))
