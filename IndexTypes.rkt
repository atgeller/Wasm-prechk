#lang racket

(require redex/reduction-semantics "WASM-Redex/Syntax.rkt")

(provide WASMIndexTypes)

(define-extended-language WASMIndexTypes WASM
  (ibinop ::= .... div-u/unsafe div-s/unsafe rem-u/unsafe rem-s/unsafe)
  
  (e ::= .... (call-indirect/unsafe tfi)
     (t load/unsafe j j) (t load/unsafe (tp sx) j j)
     (t store/unsafe j j) (t store/unsafe tp j j)
     (if tfi (e ...) else (e ...)) (block tfi (e ...)) (loop tfi (e ...)))

  ;; Index language
  (ivar ::= variable-not-otherwise-mentioned)
  (x y ::= ivar (t c) (binop x y) (testop x) (relop x y) (cvtop x t) (cvtop x t sx))
  (P ::= (= x y) (if P P P) (not P) (and P P) (or P P) ⊥)
  (φ ::= empty (φ P))
  (Γ ::= empty (Γ ti))
  (ti ::= (t ivar))

  ;; Instruction index types
  (locals ::= (ti ...))
  ;; Index-type pre/post-condition: types on stack, locals, and constraint context
  (ticond ::= ((ti ...) locals Γ φ))
  (tficond ::= (ticond -> ticond))
  (tiann ::= ((ti ...) locals φ))
  (tfi ::= (tiann -> tiann))

  ;; Indexed module contexts
  (C ::= ((func tfi ...) (global tg ...) (table (j tfi ...)) (memory j) (local t ...) (label ticond  ...) (return ticond))
     ((func tfi ...) (global tg ...) (table (j tfi ...)) (memory j) (local t ...) (label ticond ...) (return))
     ((func tfi ...) (global tg ...) (table (j tfi ...)) (memory) (local t ...) (label ticond  ...) (return ticond))
     ((func tfi ...) (global tg ...) (table (j tfi ...)) (memory) (local t ...) (label ticond ...) (return))
     ((func tfi ...) (global tg ...) (table) (memory j) (local t ...) (label ticond  ...) (return ticond))
     ((func tfi ...) (global tg ...) (table) (memory j) (local t ...) (label ticond ...) (return))
     ((func tfi ...) (global tg ...) (table) (memory) (local t ...) (label ticond  ...) (return ticond))
     ((func tfi ...) (global tg ...) (table) (memory) (local t ...) (label ticond ...) (return)))

  (S ::= ((C ...) (table ((j (tfi ...)) ...)) (memory (j ...))))

  ;; Module-level indexed declarations
  (f ::= ((ex ...) (func tfi (local (t ...) (e ...))))
     ((ex ...) (func tfi im)))
  (glob ::= ((ex ...) (global tg (e ...)))
        ((ex ...) (global tg im)))
  (tab ::= ((ex ...) (table n i ...))
       ((ex ...) (table n im tfi ...)))
  (mem ::= ((ex ...) (memory n))
       ((ex ...) (memory n im)))
  (im ::= (import string string))
  (ex ::= (export string))
  (mod ::= (module (f ...) (glob ...) (tab ...) (mem ...))))
