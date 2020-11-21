# Wasm-prechk: Indexed types for safer and faster WebAssembly

[![DOI](https://zenodo.org/badge/224305190.svg)](https://zenodo.org/badge/latestdoi/224305190)


Some typing rules are slightly out-of-date compared to the paper's type system model, particularly the administrative rules.
However, the Z3 implementation is up-to-date.

The code to generate Z3 queries from constraints is in `satisfies.rkt`, and the

- The syntax for the Wasm-prechk language is defined in [IndexTypes.rkt](IndexTypes.rkt).
- The typing rules for instruction sequences are defined in [IndexTypingRules.rkt](IndexTypingRules.rkt).
- The typing rules for modules are defined in [IndexModuleTyping.rkt](IndexModuleTyping.rkt).
- The syntax and typing rules for the run-time system are defined in [IndexAdministrativeTyping.rkt](IndexAdministrativeTyping.rkt).
- The Z3 implementation of the constraint solver is defined in [Satisfies.rkt](Satisfies.rkt).
- The code for generating queries to handle the checking of table calls is in [TableValidation.rkt](TableValidation.rkt).

## Dependencies
* bitsyntax
* redex

Both dependencies can be installed with `raco pkg install <name>`.
