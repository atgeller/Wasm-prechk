#lang racket

(require redex
         "IndexTypes.rkt"
         "SubTyping.rkt"
         "IndexTypingRules.rkt"
         "Utilities.rkt"
         "WASM-Redex/Utilities.rkt")

(provide ⊢-module-func
         ⊢-module-func-list
         ⊢-module-global
         ⊢-module-global-list
         ⊢-module-table
         ⊢-module-mem
         ⊢-module
         valid-indices
         extract-module-type)

(define-metafunction WASMIndexTypes
  make-locals : (ti ...) -> (t ...)
  [(make-locals ((t a) ...)) (t ...)])

;; Validates the function definition and returns all exports and the type of the function
(define-judgment-form WASMIndexTypes
  #:contract (⊢-module-func C f ((ex ...) tfi))

  ;; Should (t _) ... be instiantiated in phi_1?
  [(⊢ ((func (tfi_1 ...))
       (global (tg ...))
       (table (j_1 (tfi ...)) ...)
       (memory j_2 ...)
       (local (t_1 ... t ...))
       (label (((ti_2 ...) locals_2 Γ_3 φ_3)))
       (return ((ti_2 ...) locals_2 Γ_3 φ_3)))
      (e ...)
      ((() ((t_1 a_1) ... (t a) ...) Γ_1 φ_1) -> ((ti_2 ...) locals_2 Γ_3 φ_3)))
   (side-condition (equiv-gammas Γ_1 (build-gamma ((t_1 a_1) ... (t a) ...)))) ;; Γ_2 = ((t_1 a_1) ... (t a) ...)
   (side-condition ,(subset? (term (domain-φ φ_1)) (term (domain-Γ Γ_1)))) ;; domain(φ_1) subset of Γ_1
   (side-condition (satisfies Γ_3 φ_3 φ_4))
   ---------------------------------------------------
   (⊢-module-func ((func (tfi_1 ...)) (global (tg ...)) (table (j_1 (tfi ...)) ...) (memory j_2 ...) _ _ _)
                  (func (ex ...) ((((t_1 a_1) ...) () Γ_1 φ_1) -> ((ti_2 ...) () Γ_4 φ_4)) (local (t ...) (e ...)))
                  ((ex ...) ((((t_1 a_1) ...) () Γ_1 φ_1) -> ((ti_2 ...) () Γ_4 φ_4))))]

  ;; Imported function is easy
  [-----------------------------------------------------------
   (⊢-module-func C (func (ex ...) tfi im) ((ex ...) tfi))])

;; Helper judgement to ensure that function declarations/definitions are valid
;; Ensures each function in the list matches its respective type under a the module type consisting only of the preceeding global definitions in the list
(define-judgment-form WASMIndexTypes
  #:contract (⊢-module-func-list C (f ...) (((ex ...) tfi) ...))

  [-----------------------------
   (⊢-module-func-list C () ())]

  [(⊢-module-func C f_1 ((ex_1 ...) tfi_1))
   (⊢-module-func-list C (f_2 ...) (((ex_2 ...) tfi_2) ...))
   ---------------------------------------------------------
   (⊢-module-func-list C (f_1 f_2 ...) (((ex_1 ...) tfi_1) ((ex_2 ...) tfi_2) ...))])

;; Validates the global variable definition and returns all exports and the type of the global
(define-judgment-form WASMIndexTypes
  #:contract (⊢-module-global C glob ((ex ...) tg))

  [;; Can't have exports if global is mutable
   (side-condition ,(or (not (term mut?)) (null? (term (ex ...)))))
   (⊢ C (e ...) ((() () empty empty) -> ((t a) () Γ_2 φ_2)))
   ----------------------------------------------
   (⊢-module-global C
                    (global (ex ...) (mut? t) (e ...))
                    ((ex ...) (mut? t)))]

  [;; Can't import a mutable global
   -------------------
   (⊢-module-global C
                    (global (ex ...) (#f t) im)
                    ((ex ...) (#f t)))])

;; Helper judgement to ensure that global variable definitions are valid
;; Ensures each global in the list matches its respective type under a the module type consisting only of the preceeding global definitions in the list
(define-judgment-form WASMIndexTypes
  #:contract (⊢-module-global-list (glob ...) (((ex ...) tg) ...))

  [-----------------------------
   (⊢-module-global-list () ())]

  [(⊢-module-global ((func ()) (global (tg ...)) (table) (memory) (local ()) (label ()) (return)) glob_1 ((ex_1 ...) tg_1))
   (⊢-module-global-list (glob ...) (((ex ...) tg) ...))
   ------------------------------------------------------------------------------------------------------------------------
   (⊢-module-global-list (glob ... glob_1) (((ex ...) tg) ... ((ex_1 ...) tg_1)))])

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
  #:contract (⊢-module-table C tab ((ex ...) (i (tfi ...))))

  [(where ((func (tfi ...)) _ _ _ _ _ _) C)
   (valid-indices (tfi ...) (j ...) i)
   (where (tfi_2 ...) ,(map (curry list-ref (term (tfi ...)))
                            (term (j ...))))
   -----------------------------------------
   (⊢-module-table C
                   (table (ex ...) i (j ...))
                   ((ex ...) (i (tfi_2 ...))))]

  [(where i ,(length (term (tfi ...))))
   -----------------------------------
   (⊢-module-table C
                   (table (ex ...) i im (tfi ...))
                   ((ex ...) (i (tfi ...))))])

;; Returns all exports and the memory size
(define-judgment-form WASMIndexTypes
  #:contract (⊢-module-mem C mem ((ex ...) i))

  [----------------------------------------------------
   (⊢-module-mem C (memory (ex ...) i) ((ex ...) i))]

  [----------------------------------------------------
   (⊢-module-mem C (memory (ex ...) i im) ((ex ...) i))])

;; Validates all definitions in the module against the types declared in the module
(define-judgment-form WASMIndexTypes
  #:contract (⊢-module m)

  [(⊢-module-func-list C (f ...) (((ex_1_ ...) tfi) ...))
   (⊢-module-global-list (glob ...) (((ex_2_ ...) tg) ...))
   (⊢-module-table C tab ((ex_3_ ...) (i (tfi_2 ...))))
   (⊢-module-mem C mem ((ex_4_ ...) j))
   (where C ((func (tfi ...)) (global (tg ...)) (table (i (tfi_2 ...))) (memory j) (local ()) (label ()) (return)))
   ------------------------------------
   (⊢-module (module (f ...) (glob ...) (tab) (mem)))]

  [(⊢-module-func-list C (f ...) (((ex_1_ ...) tfi) ...))
   (⊢-module-global-list (glob ...) (((ex_2_ ...) tg) ...))
   (⊢-module-table C tab ((ex_3_ ...) (i (tfi_2 ...))))
   (where C ((func (tfi ...)) (global (tg ...)) (table (i (tfi_2 ...))) (memory) (local ()) (label ()) (return)))
   --------------------------------------------------
   (⊢-module (module (f ...) (glob ...) (tab) ()))]

  [(⊢-module-func-list C (f ...) (((ex_1_ ...) tfi) ...))
   (⊢-module-global-list (glob ...) (((ex_2_ ...) tg) ...))
   (⊢-module-mem C mem ((ex_4_ ...) j))
   (where C ((func (tfi ...)) (global (tg ...)) (table) (memory j) (local ()) (label ()) (return)))
   ------------------------------------
   (⊢-module (module (f ...) (glob ...) () (mem)))]

  [(⊢-module-func-list C (f ...) (((ex_1_ ...) tfi) ...))
   (⊢-module-global-list (glob ...) (((ex_2_ ...) tg) ...))
   (where C ((func (tfi ...)) (global (tg ...)) (table) (memory) (local ()) (label ()) (return)))
   ---------------------------------------------------------------------------------------------
   (⊢-module (module (f ...) (glob ...) () ()))])


;; Helper metafunction to extract a function type declaration from the function definition
(define-metafunction WASMIndexTypes
  extract-func-types : (f ...) -> (tfi ...)
  [(extract-func-types ()) ()]
  [(extract-func-types ((func _ tfi _) f_2 ...))
   (tfi tfi_2 ...)
   (where (tfi_2 ...) (extract-func-types (f_2 ...)))])

;; Helper metafunction to extract a global variable's type from the global variable definition
(define-metafunction WASMIndexTypes
  extract-global-types : (glob ...) -> (tg ...)
  [(extract-global-types ()) ()]
  [(extract-global-types ((global _ tg _) glob_2 ...))
   (tg tg_2 ...)
   (where (tg_2 ...) (extract-global-types (glob_2 ...)))])

;; Helper metafunction to extract a tables type from the table and the function types
;; requires that the tables all have valid indices
(define-metafunction WASMIndexTypes
  extract-table-types : (tfi ...) (tab ...) -> ((j (tfi ...)) ...)
  [(extract-table-types (tfi ...) ()) ()]
  [(extract-table-types (tfi ...) ((table _ i (j ...)) tab ...))
   ((i ,(map (curry list-ref (term (tfi ...))) (term (j ...)))) (i_2 (tfi_2 ...)) ...)
   (where ((i_2 (tfi_2 ...)) ...) (extract-table-types (tfi ...) (tab ...)))]
  [(extract-table-types (tfi ...) ((table _ i (tfi_1 ...) _) tab ...))
   ((i (tfi_1 ...)) (i_2 (tfi_2 ...)) ...)
   (where ((i_2 (tfi_2 ...)) ...) (extract-table-types (tfi ...) (tab ...)))])

;; Helper metafunction to extract a memories type
(define-metafunction WASMIndexTypes
  extract-memory-type : mem -> j
  [(extract-memory-type (memory _ j)) j]
  [(extract-memory-type (memory _ j _)) j])

;; Extracts the declared module type (consisting of all declared function and global types in that module,
;; as well as the size of table and memory if applicable)
(define-metafunction WASMIndexTypes
  extract-module-type : m -> C
  [(extract-module-type (module (f ...) (glob ...) (tab ...) (mem ...)))
   ((func (tfi ...))
    (global (extract-global-types (glob ...)))
    (table (i (tfi_1 ...)) ...)
    (memory (extract-memory-type mem) ...)
    (local ())
    (label ())
    (return))
   (where (tfi ...) (extract-func-types (f ...)))
   (where ((i (tfi_1 ...)) ...) (extract-table-types (tfi ...) (tab ...)))])

