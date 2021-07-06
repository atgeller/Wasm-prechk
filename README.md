# Wasm-prechk: Indexed types for faster WebAssembly

[![DOI](https://zenodo.org/badge/224305190.svg)](https://zenodo.org/badge/latestdoi/224305190)



- The syntax for the Wasm-prechk language is defined in [IndexTypes.rkt](IndexTypes.rkt).
- The typing rules for instruction sequences are defined in [IndexTypingRules.rkt](IndexTypingRules.rkt).
- The typing rules for modules are defined in [IndexModuleTyping.rkt](IndexModuleTyping.rkt).
- The syntax and typing rules for the run-time system are defined in [IndexAdministrativeTyping.rkt](IndexAdministrativeTyping.rkt).
  These administrative typing rules are out-of-date with respect to the submission.
- The Z3 implementation of the constraint solver is defined in [Satisfies.rkt](Satisfies.rkt).
- The code for generating queries to handle the checking of table calls is in [TableValidation.rkt](TableValidation.rkt).
- A typechecking algorithm is defined in [Typechecking.rkt](Typechecking.rkt).
- A definition of erasing Wasm-prechk programs to plain WASM is defined in [Erasure.rkt](Erasure.rkt).

## Dependencies

* Racket v8.0+ (https://download.racket-lang.org/racket-v8.0.html)
* z3 4.5.0 (https://github.com/Z3Prover/z3/releases/tag/z3-4.5.0), compiled and
  executable placed in PATH or in a directory named `bin` located in the same
  directory as `Solver.rtk`.
* redex

Both `redex` can be installed with `raco pkg install <name>`, once Racket is installed.

## Usage

### Typechecking

- Open and run `Typechecking.rkt`.
- In the REPL, call `typecheck-`*syntax-object* with the term to be type checked.
  * Syntax objects other than modules require a context that they are typed under.
- Typechecking will either produce a derivation that can be verified with `test-judgment-holds`,
  or `#f` indicating that no derivation could be found.

Examples:
```
> (typecheck-func
   '((func ((((i32 a) (i32 b) (i32 c)) () empty) -> (((i32 d) (i32 e)) () (empty (= d e)))))
     (global)
     (table)
     (memory)
     (local)
     (label)
     (return))
   '(() (func ((((i32 a) (i32 b) (i32 c)) () empty)
               ->
               (((i32 d) (i32 e)) () (empty (= d e))))
              (local ()
                ((get-local 0)
                 (get-local 1)
                 (i32 add)
                 (get-local 2)
                 (i32 add)
                 (get-local 0)
                 (get-local 1)
                 (get-local 2)
                 (i32 add)
                 (i32 add))))))
(derivation ...)

> (typecheck-func
   '((func ((((i32 a)) () (empty (not (= a (i32 0)))))
            ->
            (((i32 b)) () (empty (= b (i32 0))))))
     (global)
     (table)
     (memory)
     (local)
     (label)
     (return))
   '(() (func ((((i32 a)) () (empty (not (= a (i32 0)))))
               ->
               (((i32 b)) () (empty (= b (i32 0)))))
              (local ()
                ((loop ((() ((i32 a)) (empty (not (= a (i32 0)))))
                        ->
                        (() ((i32 b)) (empty (= b (i32 0)))))
                       ((get-local 0)
                        (i32 const 1)
                        (i32 sub)
                        (tee-local 0)
                        (br-if 0)))
                 (get-local 0))))))
(derivation ...)

> (typecheck-module
   '(module
        ((() (func ((((i32 a) (i32 b)) () empty)
                    ->
                    (((i32 c)) () (empty (= c ((i32 add) a b)))))
                   (local ()
                     ((get-local 0)
                      (get-local 1)
                      (i32 add)))))
         (() (func ((((i32 a)) () empty)
                    ->
                    (((i32 b)) () (empty (= b ((i32 mul) a (i32 2))))))
                   (local ()
                     ((get-local 0)
                      (get-local 0)
                      (call 0))))))
      () () ()))
(derivation ...)
```

### Erasure

- Open and run `Erasure.rkt`.
- In the REPL, call `erase-`*syntax-object* with the term to be erased.
