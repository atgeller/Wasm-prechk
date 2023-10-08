#lang racket

(module+ test
  (require "../IndexTypingRules.rkt"
           "../IndexModuleTyping.rkt"
           "../SubTyping.rkt"
           redex/reduction-semantics
           rackunit)

  (define ticond0 `(((i32 a) (i32 b)) () ((empty (i32 a)) (i32 b)) empty))
  (define ticond1 `(() ((i32 a) (i32 b)) ((empty (i32 a)) (i32 b)) empty))
  (define ticond2 `(((i32 a_2)) ((i32 a) (i32 b)) (((empty (i32 a)) (i32 b)) (i32 a_2)) (empty (= a_2 a))))
  (define ticond2_1 `(() ((i32 a) (i32 b)) (((empty (i32 a)) (i32 b)) (i32 a_2)) (empty (= a_2 a))))
  (define ticond3 `(((i32 a_2) (i32 b_2)) ((i32 a) (i32 b)) ((((empty (i32 a)) (i32 b)) (i32 a_2)) (i32 b_2)) ((empty (= a_2 a)) (= b_2 b))))
  (define ticond3_1 `(((i32 b_2)) ((i32 a) (i32 b)) ((((empty (i32 a)) (i32 b)) (i32 a_2)) (i32 b_2)) ((empty (= a_2 a)) (= b_2 b))))
  (define ticond4 `(((i32 c)) ((i32 a) (i32 b)) (((((empty (i32 a)) (i32 b)) (i32 a_2)) (i32 b_2)) (i32 c)) (((empty (= a_2 a)) (= b_2 b)) (= c ((i32 add) a_2 b_2)))))
  #;(define ticond5 `(((i32 c)) () (((empty (i32 a)) (i32 b)) (i32 c)) (empty (= c ((i32 add) a b)))))
  #;(define ticond5_1 `(((i32 c)) ((i32 a) (i32 b)) (((empty (i32 a)) (i32 b)) (i32 c)) (empty (= c ((i32 add) a b)))))

  (define context1
    (term ((func ((((i32 a) (i32 b)) empty) -> (((i32 c)) (empty (= c ((i32 add) a b))))))
           (global)
           (table)
           (memory)
           (local)
           (label)
           (return))))
  
  (define context1-inner
    (term ((func ((((i32 a) (i32 b)) empty) -> (((i32 c)) (empty (= c ((i32 add) a b))))))
           (global)
           (table)
           (memory)
           (local i32 i32)
           (label (((i32 c)) ((i32 a) (i32 b)) (empty (= c ((i32 add) a b)))))
           (return (((i32 c)) (empty (= c ((i32 add) a b))))))))

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
    (derivation `(⊢-module-func ,context1
                                (() (func ((((i32 a) (i32 b)) empty) -> (((i32 c)) (empty (= c ((i32 add) a b)))))
                                          (local () ((get-local 0) (get-local 1) (i32 add)))))
                                (() ((((i32 a) (i32 b)) empty) -> (((i32 c)) (empty (= c ((i32 add) a b)))))))
                #f
                (list deriv3)))

  (test-judgment-holds ⊢-module-func deriv4))
