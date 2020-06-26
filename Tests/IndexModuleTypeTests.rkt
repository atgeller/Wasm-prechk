#lang racket

(module+ test
  (require "../IndexTypingRules.rkt"
           "../IndexModuleTyping.rkt"
           redex/reduction-semantics
           rackunit)

  (define ticond0 `(((i32 a) (i32 b)) () ()
                                      ((empty (i32 a)) (i32 b))))
  (define ticond1 `(() ((i32 a) (i32 b)) ()
                       ((empty (i32 a)) (i32 b))))
  (define ticond2 `(((i32 d)) ((i32 a) (i32 b)) ()
                              ((((empty (i32 a)) (i32 b)) (i32 d)) (eq d a))))
  (define ticond2_1 `(() ((i32 a) (i32 b)) ()
                         ((((empty (i32 a)) (i32 b)) (i32 d)) (eq d a))))
  (define ticond3 `(((i32 d) (i32 e)) ((i32 a) (i32 b)) ()
                                      ((((((empty (i32 a)) (i32 b)) (i32 d)) (eq d a)) (i32 e)) (eq e b))))
  (define ticond3_1 `(((i32 e)) ((i32 a) (i32 b)) ()
                                ((((((empty (i32 a)) (i32 b)) (i32 d)) (eq d a)) (i32 e)) (eq e b))))
  (define ticond4 `(((i32 c)) ((i32 a) (i32 b)) ()
                              ((((((((empty (i32 a)) (i32 b)) (i32 d)) (eq d a)) (i32 e)) (eq e b)) (i32 c)) (eq c (add d e)))))
  (define ticond5 `(((i32 c)) ((i32 a) (i32 b)) ()
                              ((((empty (i32 a)) (i32 b)) (i32 c)) (eq c (add a b)))))
  (define ticond6 `(((i32 c)) () () ((((empty (i32 a)) (i32 b)) (i32 c)) (eq c (add a b)))))

  (define dummy-store '(() (table ()) (memory ())))
  
  (define context1 (term ((func ((,ticond0 -> ,ticond6))) (global ())
                          (table) (memory)
                          (local ()) (label ()) (return))))
  (define context1-inner (term ((func ((,ticond0 -> ,ticond6)))
                                (global ()) (table)
                                (memory) (local (i32 i32)) (label (,ticond5))
                                (return ,ticond5))))

  (define deriv1
    (derivation `(⊢ ,dummy-store ,context1-inner
                    ((get-local 0))
                    (,ticond1 -> ,ticond2))
                #f
                (list)))

  (test-judgment-holds ⊢ deriv1)

  (define deriv2_0
    (derivation `(⊢ ,dummy-store ,context1-inner
                                 ((get-local 1))
                                 (,ticond2_1 -> ,ticond3_1))
                             #f
                             (list)))

  (test-judgment-holds ⊢ deriv2_0)

  (define deriv2_1
    (derivation `(⊢ ,dummy-store ,context1-inner
                                 ((get-local 1))
                                 (,ticond2 -> ,ticond3))
                             #f
                             (list deriv2_0)))

  (test-judgment-holds ⊢ deriv2_1)
  
  (define deriv2
    (derivation `(⊢ ,dummy-store ,context1-inner
                    ((get-local 0) (get-local 1))
                    (,ticond1 -> ,ticond3))
                #f
                (list deriv1 deriv2_1 )))

  (test-judgment-holds ⊢ deriv2)

  (define deriv3_0
    (derivation `(⊢ ,dummy-store ,context1-inner
                                 ((i32 add))
                                 (,ticond3 -> ,ticond4))
                             #f
                             (list)))

  (test-judgment-holds ⊢ deriv3_0)

  (define deriv3
    (derivation `(⊢ ,dummy-store ,context1-inner
                    ((get-local 0) (get-local 1) (i32 add))
                    (,ticond1 -> ,ticond4))
                #f
                (list deriv2 deriv3_0)))

  (test-judgment-holds ⊢ deriv3)

  (define deriv4_s
    (derivation `(<: (,ticond1 -> ,ticond5) (,ticond1 -> ,ticond4))
                #f
                (list)))

  (define deriv4
    (derivation `(⊢ ,dummy-store ,context1-inner
                    ((get-local 0) (get-local 1) (i32 add))
                    (,ticond1 -> ,ticond5))
                #f
                (list deriv3 deriv4_s)))
  
  (test-judgment-holds ⊢ deriv4)
  
  #;(displayln `(⊢ ,dummy-store ,context1-inner
                    ((get-local 0) (get-local 1) (i32 add))
                    (,ticond1 -> ,ticond5)))
  #;(displayln `(⊢-module-func ,context1
                             (() (func (,ticond0 -> ,ticond6)
                                       (local () ((get-local 0) (get-local 1) (i32 add)))))
                             (() (,ticond0 -> ,ticond6))))

  (define deriv5
    (derivation `(⊢-module-func ,dummy-store ,context1
                                (() (func (,ticond0 -> ,ticond6)
                                          (local () ((get-local 0) (get-local 1) (i32 add)))))
                                (() (,ticond0 -> ,ticond6)))
                #f
                (list deriv4)))

  (test-judgment-holds ⊢-module-func deriv5))
