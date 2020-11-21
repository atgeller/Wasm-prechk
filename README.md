# Wasm-prechk: Indexed types for safer and faster WebAssembly

[![DOI](https://zenodo.org/badge/224305190.svg)](https://zenodo.org/badge/latestdoi/224305190)

Unfortunately, the typing rules here are still out-of-date compared to our type system model. However, the code for compiling constraint sets (the syntax of which can be found in `indextypes.rkt` into Z3 is correct. The code to generate Z3 queries from constraints is in `satisfies.rkt`, and the code for generating queries to handle the checking of table calls is in `tablevalidation.rkt`.

The syntax for the Wasm-prechk language is defined in [IndexTypes.rkt](IndexTypes.rkt).

The typing rules for instruction sequences are defined in [IndexTypingRules.rkt](IndexTypingRules.rkt).

The typing rules for modules are defined in [IndexModuleTyping.rkt](IndexModuleTyping.rkt).

The syntax and typing rules for the runtime system are defined in [IndexAdministrativeTyping.rkt](IndexAdministrativeTyping.rkt).

The Z3 implementation of the constraint solver is defined in [Satisfies.rkt](Satisfies.rkt).
