#lang racket

(require redex "WASM-Redex/Syntax.rkt")

(provide WASMIndexTypes)

(define-extended-language WASMIndexTypes WASM
  (binop ::= .... (div/unsafe sx))
  (e ::= .... (call-indirect/unsafe tfi)
     (t load/unsafe j j) (t load/unsafe (tp sz) j j)
     (t store/unsafe j j) (t store/unsafe (tp) j j)
     (if tfi (e ...) (e ...)) (block tfi (e ...)) (loop tfi (e ...)))

  ;; Index language
  (a ::= variable-not-otherwise-mentioned)
  (x y ::= a (t c) (binop x y) (testop x) (relop x y))
  (P ::= (= x y) (if P P P) (not P) (and P P) (or P P) ⊥)
  (φ ::= empty (φ P))
  (Γ ::= empty (Γ ti))
  (ti ::= (t a))

  ;; Instruction index types
  (locals ::= (ti ...))
  ;; Index-type pre/post-condition: types on stack, locals, and constraint context
  (ticond ::= ((ti ...) locals Γ φ))
  (tfi ::= (ticond -> ticond))

  ;; Indexed module contexts
  (C ::= ((func (tfi ...)) (global (tg ...)) (table (j (tfi ...)) ...) (memory j ...) (local (t ...)) (label (ticond  ...)) (return ticond))
     ((func (tfi ...)) (global (tg ...)) (table (j (tfi ...)) ...) (memory j ...) (local (t ...)) (label (ticond ...)) (return)))

  (S ::= ((C ...) (table ((j (tfi ...)) ...)) (memory (j ...))))

  ;; Module-level indexed declarations
  (f ::= (func (ex ...) tfi (local (t ...) (e ...)))
     (func (ex ...) tfi im))
  (glob ::= (global (ex ...) tg (e ...))
        (global (ex ...) tg im))
  (tab ::= (table (ex ...) j (j ...))
       (table (ex ...) j im (tfi ...)))
  (mem ::= (memory (ex ...) i)
       (memory (ex ...) i im))
  (im ::= (import string string))
  (ex ::= (export string))
  (m ::= (module (f ...) (glob ...) (tab ...) (mem ...))))
