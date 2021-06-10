#lang racket

(require redex/reduction-semantics
         "IndexTypes.rkt"
         "SubTyping.rkt"
         "IndexTypingRules.rkt"
         "Utilities.rkt")

(provide ⊢-module-func
         ⊢-module-global
         ⊢-module-table
         ⊢-module-memory
         ⊢-module
         valid-indices
         global-contexts
         extract-module-type)

;; Validates the function definition and returns all exports and the type of the function
(define-judgment-form WASMIndexTypes
  #:contract (⊢-module-func C f ((ex ...) tfi))

  ;; Should (t _) ... be instiantiated in phi_1?
  [(where ((((t_1 ivar_1) ...) () Γ_1 φ_1) -> ((ti_2 ...) () Γ_4 φ_4)) tfi)
   (⊢ C_2 (e ...) ((() ((t_1 ivar_1) ... (t ivar) ...) Γ_5 φ_5) -> ((ti_2 ...) locals_2 Γ_3 φ_3)))
   (where ((ti_2 ...) locals_1 Γ_6 φ_4) (context-return C_2))
   (where (((ti_2 ...) locals_1 Γ_6 φ_4)) (context-labels C_2))
   (where (t_1 ... t ...) (context-locals C_2))
   (where φ_5 (extend φ_1 (build-phi-zeros (t ...) (ivar ...))))
   (side-condition (equiv-gammas Γ_6 (union Γ_4 (build-gamma locals_1))))
   (side-condition (equiv-gammas Γ_5 (union Γ_1 (build-gamma ((t ivar) ...)))))
   (side-condition (equiv-gammas Γ_1 (build-gamma ((t_1 ivar_1) ...)))) ;; Γ_2 = ((t_1 a_1) ...)
   (side-condition ,(subset? (term (domain-φ φ_1)) (term (domain-Γ Γ_1)))) ;; domain(φ_1) subset of Γ_1
   (side-condition (satisfies Γ_3 φ_3 φ_4))
   ----------------------------------------------------------------------------------------------------
   (⊢-module-func C ((ex ...) (func tfi (local (t ...) (e ...)))) ((ex ...) tfi))]

  ;; Imported function is easy
  [---------------------------------------------------------
   (⊢-module-func C ((ex ...) (func tfi im)) ((ex ...) tfi))])

;; Validates the global variable definition and returns all exports and the type of the global
(define-judgment-form WASMIndexTypes
  #:contract (⊢-module-global C glob ((ex ...) tg))

  [;; Can't have exports if global is mutable
   (where (mut t) tg)
   (⊢ C (e ...) ((() () empty empty) -> (((t ivar)) () Γ_2 φ_2)))
   (side-condition ,(or (empty? (term (ex ...))) (equal? (term (mut t)) (term (const t)))))
   ----------------------------------------------------------------------------------------
   (⊢-module-global C ((ex ...) (global tg (e ...))) ((ex ...) tg))]

  [;; Can't import a mutable global
   -----------------------------------------------------------------------
   (⊢-module-global C ((ex ...) (global (const t) im)) ((ex ...) (const t)))])

;; Helper function to ensure a table is well-formed
;; Checks that there are exactly `i` indices (j ...), and that each one points to a valid function
(define-judgment-form WASMIndexTypes
  #:contract (valid-indices (any ...) (j ...) i)
  #:mode (valid-indices I I I)

  [(side-condition
    ,(and (= (length (term (j ...))) (term i))
          (let ([bound (length (term (any ...)))])
            (andmap
             (lambda (index) (< index bound))
             (term (j ...))))))
    ---------------------------
    (valid-indices (any ...) (j ...) i)])

;; Validates the table and returns all exports and the table size
(define-judgment-form WASMIndexTypes
  #:contract (⊢-module-table C tab ((ex ...) (i tfi ...)))

  [(where ((func tfi ...) _ _ _ _ _ _) C)
   (valid-indices (tfi ...) (j ...) i)
   (where (tfi_2 ...) ,(map (curry list-ref (term (tfi ...)))
                            (term (j ...))))
   -----------------------------------------
   (⊢-module-table C
                   ((ex ...) (table i j ...))
                   ((ex ...) (i tfi_2 ...)))]

  [(where i ,(length (term (tfi ...))))
   ------------------------------------
   (⊢-module-table C
                   ((ex ...) (table i im tfi ...))
                   ((ex ...) (i tfi ...)))])

;; Returns all exports and the memory size
(define-judgment-form WASMIndexTypes
  #:contract (⊢-module-memory C mem ((ex ...) i))

  [------------------------------------------------------
   (⊢-module-memory C ((ex ...) (memory i)) ((ex ...) i))]

  [---------------------------------------------------------
   (⊢-module-memory C ((ex ...) (memory i im)) ((ex ...) i))])

;; Validates all definitions in the module against the types declared in the module
(define-judgment-form WASMIndexTypes
  #:contract (⊢-module mod)

  [(⊢-module-func C_f f ((ex_f ...) tfi_f)) ...
   (⊢-module-global C_g glob ((ex_g ...) tg)) ...
   (⊢-module-table C_t tab ((ex_t ...) (n_t tfi_t ...))) ...
   (⊢-module-memory C_m mem ((ex_m ...) n_m)) ...

   (where (C_g ...) (global-contexts (tg ...)))

   (where C ((func tfi_f ...) (global tg ...) (table (n_t tfi_t ...) ...) (memory n_m ...) (local) (label) (return)))
   (side-condition (same (C_f ... C_t ... C_m ...) C))

   (side-condition (distinct (ex_f ... ... ex_g ... ... ex_t ... ... ex_m ... ...)))
   ---------------------------------------------------------------------------------------------------
   (⊢-module (module (f ...) (glob ...) (tab ...) (mem ...)))])


(define-metafunction WASMIndexTypes
  global-contexts : (tg ...) -> (C ...)
  [(global-contexts ()) ()]
  [(global-contexts (tg_i-1 ... tg))
   (C ... ((func) (global tg_i-1 ...) (table) (memory) (local) (label) (return)))
   (where (C ...) (global-contexts (tg_i-1 ...)))])


;; Helper metafunction to extract a function type declaration from the function definition
(define-metafunction WASMIndexTypes
  extract-func-types : (f ...) -> (tfi ...)
  [(extract-func-types ()) ()]
  [(extract-func-types ((_ (func tfi _)) f_2 ...))
   (tfi tfi_2 ...)
   (where (tfi_2 ...) (extract-func-types (f_2 ...)))])

(define-metafunction WASMIndexTypes
  extract-func-type : f -> tfi
  [(extract-func-type (_ (func tfi _))) tfi])

;; Helper metafunction to extract a global variable's type from the global variable definition
(define-metafunction WASMIndexTypes
  extract-global-types : (glob ...) -> (tg ...)
  [(extract-global-types ()) ()]
  [(extract-global-types ((_ (global tg _)) glob_2 ...))
   (tg tg_2 ...)
   (where (tg_2 ...) (extract-global-types (glob_2 ...)))])

(define-metafunction WASMIndexTypes
  extract-global-type : glob -> tg
  [(extract-global-type (_ (global tg _))) tg])

;; Helper metafunction to extract a tables type from the table and the function types
;; requires that the tables all have valid indices
(define-metafunction WASMIndexTypes
  extract-table-types : (tfi ...) (tab ...) -> ((j (tfi ...)) ...)
  [(extract-table-types (tfi ...) ()) ()]
  [(extract-table-types (tfi ...) ((table _ i j ...) tab ...))
   ((i ,@(map (curry list-ref (term (tfi ...))) (term (j ...)))) (i_2 tfi_2 ...) ...)
   (where ((i_2 tfi_2 ...) ...) (extract-table-types (tfi ...) (tab ...)))]
  [(extract-table-types (tfi ...) ((table _ i (tfi_1 ...) _) tab ...))
   ((i tfi_1 ...) (i_2 tfi_2 ...) ...)
   (where ((i_2 tfi_2 ...) ...) (extract-table-types (tfi ...) (tab ...)))])

;; Helper metafunction to extract a memories type
(define-metafunction WASMIndexTypes
  extract-memory-type : mem -> j
  [(extract-memory-type (_ (memory j))) j]
  [(extract-memory-type (_ (memory j _))) j])

;; Extracts the declared module type (consisting of all declared function and global types in that module,
;; as well as the size of table and memory if applicable)
(define-metafunction WASMIndexTypes
  extract-module-type : mod -> C
  [(extract-module-type (module (f ...) (glob ...) (tab ...) (mem ...)))
   ((func tfi ...)
    (global (extract-global-type glob) ...)
    (table (i (tfi_1 ...)) ...)
    (memory (extract-memory-type mem) ...)
    (local)
    (label)
    (return))
   (where (tfi ...) ((extract-func-type f) ...))
   (where ((i tfi_1 ...) ...) (extract-table-types (tfi ...) (tab ...)))])

