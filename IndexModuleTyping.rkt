#lang racket

(require redex
         "IndexTypes.rkt"
         "SubTyping.rkt"
         "IndexTypingRules.rkt")

(provide ⊢-module-func valid-indices)

(define-metafunction WASMIndexTypes
  make-locals : (ti ...) -> (t ...)
  [(make-locals ((t a) ...)) (t ...)])

;; Validates the function definition and returns all exports and the type of the function
(define-judgment-form WASMIndexTypes
  #:contract (⊢-module-func C f ((ex ...) tfi))

  ;; Should (t _) ... be instiantiated in phi_1?
  [(⊢ ((func (tfi_1 ...))
       (global ((_ t_2) ...)) (table (j_1 (tfi ...)) ...)
       (memory j_2 ...) (local (t_1 ... t ...))
       (label (((ti_2 ...) locals_2 φ_2))) (return ((ti_2 ...) locals_2 φ_2)))
      (e ...)
      ((() ((t_1 a) ... (t a_2) ...) φ_1) -> ((ti_2 ...) locals_2 φ_2)))
   ;; a_2 ... fresh
   ---------------------------------------------------------------------------
   (⊢-module-func ((func (tfi_1 ...)) (global ((_ t_2) ...)) (table (j_1 (tfi ...)) ...) (memory j_2 ...) _ _ _)
                  ((ex ...) (func ((((t_1 a) ...) () φ_1) -> ((ti_2 ...) locals_2 φ_2)) (local (t ...) (e ...))))
                  ((ex ...) ((((t_1 a) ...) () φ_1) -> ((ti_2 ...) locals_2 φ_2))))]

  ;; Imported function is easy
  [-----------------------------------------------------------
   (⊢-module-func C ((ex ...) (func tfi im)) ((ex ...) tfi))])

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
   (⊢ C (e ...) ((() () φ_1) -> ((t a) () φ_2)))
   ----------------------------------------------
   (⊢-module-global C
                    ((ex ...) (global (mut? t) (e ...)))
                    ((ex ...) (mut? t)))]

  [;; Can't import a mutable global
   -------------------
   (⊢-module-global C
                    ((ex ...) (global (#f t) im))
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
                   ((ex ...) (table i (j ...)))
                   ((ex ...) (i (tfi_2 ...))))]

  [-----------------------------------
   (⊢-module-table C
                   ((ex ...) (table (i (tfi ...)) im))
                   ((ex ...) (i (tfi ...))))])

;; Returns all exports and the memory size
(define-judgment-form WASMIndexTypes
  #:contract (⊢-module-mem C mem ((ex ...) i))

  [----------------------------------------------------
   (⊢-module-mem C ((ex ...) (memory i)) ((ex ...) i))]

  [----------------------------------------------------
   (⊢-module-mem C ((ex ...) (memory i im)) ((ex ...) i))])

;; Validates all definitions in the module against the types declared in the module
(define-judgment-form WASMIndexTypes
  #:contract (⊢-module m C)

  [(where ((func (tfi ...)) (global (tg ...)) (table (i (tfi_2 ...))) (memory j) (local ()) (label ()) (return)) C)
   (⊢-module-func-list C (f ...) (((ex_1_ ...) tfi) ...))
   (⊢-module-global-list (glob ...) (((ex_2_ ...) tg) ...))
   (⊢-module-table C tab ((ex_3_ ...) (i (tfi_2 ...))))
   (⊢-module-mem C mem ((ex_4_ ...) j))
   ------------------------------------
   (⊢-module (module (f ...) (glob ...) (tab) (mem)) C)]

  [(where ((func (tfi ...)) (global (tg ...)) (table (i (tfi_2 ...))) (memory) (local ()) (label ()) (return)) C)
   (⊢-module-func-list C (f ...) (((ex_1_ ...) tfi) ...))
   (⊢-module-global-list (glob ...) (((ex_2_ ...) tg) ...))
   (⊢-module-mem C tab ((ex_3_ ...) (i (tfi_2 ...))))
   --------------------------------------------------
   (⊢-module (module (f ...) (glob ...) (tab) ()) C)]

  [(where ((func (tfi ...)) (global (tg ...)) (table) (memory j) (local ()) (label ()) (return)) C)
   (⊢-module-func-list C (f ...) (((ex_1_ ...) tfi) ...))
   (⊢-module-global-list (glob ...) (((ex_2_ ...) tg) ...))
   (⊢-module-mem C mem ((ex_4_ ...) j))
   ------------------------------------
   (⊢-module (module (f ...) (glob ...) () (mem)) C)]

  [(⊢-module-func-list C (f ...) (((ex_1_ ...) tfi) ...))
   (⊢-module-global-list (glob ...) (((ex_2_ ...) tg) ...))
   (where C ((func (tfi ...)) (global (tg ...)) (table) (memory) (local ()) (label ()) (return)))
   ---------------------------------------------------------------------------------------------
   (⊢-module (module (f ...) (glob ...) () ()) C)]
  )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; TODO: These were for a redex implementation, but that may never happen.
;;       If it is to happen, these must be updated
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Helper metafunction to extract a function type declaration from the function definition
(define-metafunction WASMIndexTypes
  extract-func-types : (f ...) -> (tfi ...)
  [(extract-func-types ()) ()]
  [(extract-func-types ((_ (func tfi _)) f_2 ...))
   (tfi (extract-func-types (f_2 ...)))])

;; Helper metafunction to extract a global variable's type from the global variable definition
(define-metafunction WASMIndexTypes
  extract-global-types : (glob ...) -> (tg ...)
  [(extract-global-types ()) ()]
  [(extract-global-types ((_ (global tg _)) glob_2 ...))
   (tg (extract-global-types (glob_2 ...)))])

;; Extracts the declared module type (consisting of all declared function and global types in that module, as well as the size of table and memory if applicable)
;; Eventually may be useful for deriving module types
(define-metafunction WASMIndexTypes
  extract-module-type : m -> C
  [(extract-module-type (module (f ...) (glob ...) ((table i _)) ((memory j))))
   ((extract-func-types (f ...)) (extract-global-types (glob ...)) (table i) (memory j) (local ()) (label ()) (return))]
  [(extract-module-type (module (f ...) (glob ...) ((table i _)) ()))
   ((extract-func-types (f ...)) (extract-global-types (glob ...)) (table i) (memory) (local ()) (label ()) (return))]
  [(extract-module-type (module (f ...) (glob ...) () ((memory j))))
   ((extract-func-types (f ...)) (extract-global-types (glob ...)) (table) (memory j) (local ()) (label ()) (return))]
  [(extract-module-type (module (f ...) (glob ...) () ()))
   ((extract-func-types (f ...)) (extract-global-types (glob ...)) (table) (memory) (local ()) (label ()) (return))])

