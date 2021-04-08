#lang racket

(require redex/reduction-semantics
         "IndexTypes.rkt"
         "IndexTypingRules.rkt")

;; Base version, fails
(define-judgment-form WASMIndexTypes
  #:contract (⊢-module-func1 any any any)

  [(⊢ ((func tfi_f ...)
       (global tg ...)
       (table (n tfi_t ...) ...)
       (memory m ...)
       (local t_1 ... t ...)
       (label ((ti_2 ...) locals_1 Γ_6 φ_4))
       (return ((ti_2 ...) locals_1 Γ_6 φ_4)))
      (e ...)
      ((() ((t_1 ivar_1) ...) Γ_5 φ_5) -> ((ti_2 ...) locals_2 Γ_3 φ_3)))
   -------------------------------------------------------------------------------------------------
   (⊢-module-func1 ((func tfi_f ...) (global tg ...) (table (n tfi_t ...) ...) (memory m ...) _ _ _)
                   (() (func ((((t_1 ivar_1) ...) () Γ_1 φ_1) -> ((ti_2 ...) () Γ_4 φ_4))
                             (local (t ...) (e ...))))
                   (() ((((t_1 ivar_1) ...) () Γ_1 φ_1) -> ((ti_2 ...) () Γ_4 φ_4))))])

;; This one also fails
(define-judgment-form WASMIndexTypes
  #:contract (⊢-module-func2 any any any)

  [(⊢ ((func tfi_f ...)
       (global tg ...)
       (table (n tfi_t ...) ...)
       (memory m ...)
       (local t_1 ... t ...)
       (label ((ti_92 ...) locals_1 Γ_6 φ_4))
       (return ((ti_92 ...) locals_1 Γ_6 φ_4)))
      (e ...)
      ((() ((t_1 ivar_1) ...) Γ_5 φ_5) -> ((ti_2 ...) locals_2 Γ_3 φ_3)))
   -------------------------------------------------------------------------------------------------
   (⊢-module-func2 ((func tfi_f ...) (global tg ...) (table (n tfi_t ...) ...) (memory m ...) _ _ _)
                   (() (func ((((t_1 ivar_1) ...) () Γ_1 φ_1) -> ((ti_2 ...) () Γ_4 φ_4))
                             (local (t ...) (e ...))))
                   (() ((((t_1 ivar_1) ...) () Γ_1 φ_1) -> ((ti_2 ...) () Γ_4 φ_4))))])

;; This one passes
(define-judgment-form WASMIndexTypes
  #:contract (⊢-module-func3 any any any)

  [(⊢ ((func tfi_f ...)
       (global tg ...)
       (table (n tfi_t ...) ...)
       (memory m ...)
       (local t_1 ... t ...)
       (label ((ti_92 ..._1) locals_1 Γ_6 φ_4))
       (return ((ti_92 ..._1) locals_1 Γ_6 φ_4)))
      (e ...)
      ((() ((t_1 ivar_1) ...) Γ_5 φ_5) -> ((ti_2 ...) locals_2 Γ_3 φ_3)))
   -------------------------------------------------------------------------------------------------
   (⊢-module-func3 ((func tfi_f ...) (global tg ...) (table (n tfi_t ...) ...) (memory m ...) _ _ _)
                   (() (func ((((t_1 ivar_1) ...) () Γ_1 φ_1) -> ((ti_2 ...) () Γ_4 φ_4))
                             (local (t ...) (e ...))))
                   (() ((((t_1 ivar_1) ...) () Γ_1 φ_1) -> ((ti_2 ...) () Γ_4 φ_4))))])


;; This one very mysteriously passes, ((memory m ...) replaced with _)
(define-judgment-form WASMIndexTypes
  #:contract (⊢-module-func4 any any any)

  [(⊢ ((func tfi_f ...)
       (global tg ...)
       (table (n tfi_t ...) ...)
       (memory m ...)
       (local t_1 ... t ...)
       (label ((ti_2 ...) locals_1 Γ_6 φ_4))
       (return ((ti_2 ...) locals_1 Γ_6 φ_4)))
      (e ...)
      ((() ((t_1 ivar_1) ...) Γ_5 φ_5) -> ((ti_2 ...) locals_2 Γ_3 φ_3)))
   -------------------------------------------------------------------------------------------------
   (⊢-module-func4 ((func tfi_f ...) (global tg ...) (table (n tfi_t ...) ...) _ _ _ _)
                   (() (func ((((t_1 ivar_1) ...) () Γ_1 φ_1) -> ((ti_2 ...) () Γ_4 φ_4))
                             (local (t ...) (e ...))))
                   (() ((((t_1 ivar_1) ...) () Γ_1 φ_1) -> ((ti_2 ...) () Γ_4 φ_4))))])


;; This one passes, best workaround, replace all (ti_2 ...) with (ti_2 ..._1)
(define-judgment-form WASMIndexTypes
  #:contract (⊢-module-func5 any any any)

  [(⊢ ((func tfi_f ...)
       (global tg ...)
       (table (n tfi_t ...) ...)
       (memory m ...)
       (local t_1 ... t ...)
       (label ((ti_2 ..._1) locals_1 Γ_6 φ_4))
       (return ((ti_2 ..._1) locals_1 Γ_6 φ_4)))
      (e ...)
      ((() ((t_1 ivar_1) ...) Γ_5 φ_5) -> ((ti_2 ..._1) locals_2 Γ_3 φ_3)))
   -------------------------------------------------------------------------------------------------
   (⊢-module-func5 ((func tfi_f ...) (global tg ...) (table (n tfi_t ...) ...) (memory m ...) _ _ _)
                   (() (func ((((t_1 ivar_1) ...) () Γ_1 φ_1) -> ((ti_2 ..._1) () Γ_4 φ_4))
                             (local (t ...) (e ...))))
                   (() ((((t_1 ivar_1) ...) () Γ_1 φ_1) -> ((ti_2 ..._1) () Γ_4 φ_4))))])



(define ticond0 `(((i32 a) (i32 b)) () ((empty (i32 a)) (i32 b)) empty))
(define ticond1 `(() ((i32 a) (i32 b)) ((empty (i32 a)) (i32 b)) empty))
(define ticond2 `(((i32 a_2)) ((i32 a) (i32 b)) (((empty (i32 a)) (i32 b)) (i32 a_2)) (empty (= a_2 a))))
(define ticond2_1 `(() ((i32 a) (i32 b)) (((empty (i32 a)) (i32 b)) (i32 a_2)) (empty (= a_2 a))))
(define ticond3 `(((i32 a_2) (i32 b_2)) ((i32 a) (i32 b)) ((((empty (i32 a)) (i32 b)) (i32 a_2)) (i32 b_2)) ((empty (= a_2 a)) (= b_2 b))))
(define ticond3_1 `(((i32 b_2)) ((i32 a) (i32 b)) ((((empty (i32 a)) (i32 b)) (i32 a_2)) (i32 b_2)) ((empty (= a_2 a)) (= b_2 b))))
(define ticond4 `(((i32 c)) ((i32 a) (i32 b)) (((((empty (i32 a)) (i32 b)) (i32 a_2)) (i32 b_2)) (i32 c)) (((empty (= a_2 a)) (= b_2 b)) (= c (add a_2 b_2)))))
(define ticond5 `(((i32 c)) () (((empty (i32 a)) (i32 b)) (i32 c)) (empty (= c (add a b)))))
(define ticond5_1 `(((i32 c)) ((i32 a) (i32 b)) (((empty (i32 a)) (i32 b)) (i32 c)) (empty (= c (add a b)))))

(define context1
  (term ((func (,ticond0 -> ,ticond5))
         (global)
         (table)
         (memory)
         (local)
         (label)
         (return))))
  
(define context1-inner
  (term ((func (,ticond0 -> ,ticond5))
         (global)
         (table)
         (memory)
         (local i32 i32)
         (label ,ticond5_1)
         (return ,ticond5_1))))

(define deriv1
  (derivation `(⊢ ,context1-inner
                  ((get-local 0))
                  (,ticond1 -> ,ticond2))
              "Get-Local"
              (list)))

(test-judgment-holds ⊢ deriv1)

(define deriv2_0
  (derivation `(⊢ ,context1-inner
                  ((get-local 1))
                  (,ticond2_1 -> ,ticond3_1))
              "Get-Local"
              (list)))

(test-judgment-holds ⊢ deriv2_0)

(define deriv2_1
  (derivation `(⊢ ,context1-inner
                  ((get-local 1))
                  (,ticond2 -> ,ticond3))
              "Stack-Poly"
              (list deriv2_0)))

(test-judgment-holds ⊢ deriv2_1)
  
(define deriv2
  (derivation `(⊢ ,context1-inner
                  ((get-local 0) (get-local 1))
                  (,ticond1 -> ,ticond3))
              "Composition"
              (list deriv1 deriv2_1 )))

(test-judgment-holds ⊢ deriv2)

(define deriv3_0
  (derivation `(⊢ ,context1-inner
                  ((i32 add))
                  (,ticond3 -> ,ticond4))
              "Binop"
              (list)))

(test-judgment-holds ⊢ deriv3_0)

(define deriv3
  (derivation `(⊢ ,context1-inner
                  ((get-local 0) (get-local 1) (i32 add))
                  (,ticond1 -> ,ticond4))
              "Composition"
              (list deriv2 deriv3_0)))

(test-judgment-holds ⊢ deriv3)

(define deriv4
  (derivation `(⊢-module-func1 ,context1
                              (() (func (,ticond0 -> ,ticond5)
                                        (local () ((get-local 0) (get-local 1) (i32 add)))))
                              (() (,ticond0 -> ,ticond5)))
              #f
              (list deriv3)))

(test-judgment-holds ⊢-module-func1 deriv4)

(define deriv5
  (derivation `(⊢-module-func2 ,context1
                              (() (func (,ticond0 -> ,ticond5)
                                        (local () ((get-local 0) (get-local 1) (i32 add)))))
                              (() (,ticond0 -> ,ticond5)))
              #f
              (list deriv3)))

(test-judgment-holds ⊢-module-func2 deriv5)

(define deriv6
  (derivation `(⊢-module-func3 ,context1
                              (() (func (,ticond0 -> ,ticond5)
                                        (local () ((get-local 0) (get-local 1) (i32 add)))))
                              (() (,ticond0 -> ,ticond5)))
              #f
              (list deriv3)))

(test-judgment-holds ⊢-module-func3 deriv6)

(define deriv7
  (derivation `(⊢-module-func4 ,context1
                              (() (func (,ticond0 -> ,ticond5)
                                        (local () ((get-local 0) (get-local 1) (i32 add)))))
                              (() (,ticond0 -> ,ticond5)))
              #f
              (list deriv3)))

(test-judgment-holds ⊢-module-func4 deriv7)

(define deriv8
  (derivation `(⊢-module-func5 ,context1
                              (() (func (,ticond0 -> ,ticond5)
                                        (local () ((get-local 0) (get-local 1) (i32 add)))))
                              (() (,ticond0 -> ,ticond5)))
              #f
              (list deriv3)))

(test-judgment-holds ⊢-module-func5 deriv8)