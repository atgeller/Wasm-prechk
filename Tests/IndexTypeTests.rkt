#lang racket

(module+ test
  (require "../IndexTypes.rkt"
           "../IndexTypingRules.rkt"
           redex)

  #;(define dummy-store '(() (table ()) (memory ())))

  (define empty-context `((func) (global) (table) (memory) (local) (label) (return)))

  #;(test-judgment-holds ⊢
   (derivation `(⊢ ,empty-context ((if ((((i32 a) (i32 b)) empty) -> ((i32 c) empty))
                                       (i32 div-u/unsafe)
                                       (i32 const -1))
                   (((i32 a) (i32 b) (i32 b)) (((empty (a : i32)) (b : i32)) (>= b 0)))
                   ))))

  (define deriv1
    (derivation `(⊢ ,empty-context ((i32 sub))
                    ((((i32 b) (i32 c)) () (((empty (i32 a)) (i32 b)) (i32 c)) (empty (not (= b c))))
                     ->
                     (((i32 d))
                      ()
                      ((((empty (i32 a)) (i32 b)) (i32 c)) (i32 d))
                      ((empty (not (= b c))) (= d ((i32 sub) b c))))))
                "Binop"
                (list)))

  (test-judgment-holds ⊢ deriv1)

  (define deriv2
    (derivation `(⊢ ,empty-context ((i32 sub))
                    ((((i32 a) (i32 b) (i32 c))
                      ()
                      (((empty (i32 a)) (i32 b)) (i32 c))
                      (empty (not (= b c))))
                     ->
                     (((i32 a) (i32 d))
                      ()
                      ((((empty (i32 a)) (i32 b)) (i32 c)) (i32 d))
                      ((empty (not (= b c))) (= d ((i32 sub) b c))))))
                "Stack-Poly"
                (list deriv1)))

  (test-judgment-holds ⊢ deriv2)

  (define deriv3
    (derivation `(⊢ ,empty-context ((i32 div-u/unsafe))
                    ((((i32 a) (i32 d))
                      ()
                      ((((empty (i32 a)) (i32 b)) (i32 c)) (i32 d))
                      ((empty (not (= b c))) (= d ((i32 sub) b c))))
                     ->
                     (((i32 e))
                      ()
                      (((((empty (i32 a)) (i32 b)) (i32 c)) (i32 d)) (i32 e))
                      (((empty (not (= b c))) (= d ((i32 sub) b c))) (= e ((i32 div-u) a d))))))
                "Div-U-Prechk"
                (list)))

  (test-judgment-holds ⊢ deriv3)

  (define deriv4
    (derivation `(⊢ ,empty-context ((i32 sub) (i32 div-u/unsafe))
                    ((((i32 a) (i32 b) (i32 c))
                      ()
                      (((empty (i32 a)) (i32 b)) (i32 c))
                      (empty (not (= b c))))
                     ->
                     (((i32 e))
                      ()
                      (((((empty (i32 a)) (i32 b)) (i32 c)) (i32 d)) (i32 e))
                      (((empty (not (= b c))) (= d ((i32 sub) b c))) (= e ((i32 div-u) a d))))))
                "Composition"
                (list deriv2 deriv3)))

  (test-judgment-holds ⊢ deriv4)

  ;; This case worked in Adam's brain, but not in practice due to possible integer overflow (interesting to note that we catch possible overflow errors!)
  #;(test-judgment-holds ⊢ (derivation `(⊢ ((func
                                           (((((i32 a)) () ((empty (i32 a)) (lt-u a (i32 0)))) -> (((i32 b)) () (((empty (i32 a)) (i32 b)) (gt-u b (i32 0)))))
                                            ((((i32 a)) () (empty (i32 a))) -> (((i32 b)) () (((empty (i32 a)) (i32 b)) (= b (add a (i32 1))))))
                                            ((((i32 a)) () (empty (i32 a))) -> (((i32 b)) () ((empty (i32 a)) (i32 b))))
                                            ((((i32 a) (i32 b)) () ((empty (i32 a)) (i32 b))) -> (((i32 c)) () (((empty (i32 a)) (i32 b)) (i32 c))))))
                                          (global ())
                                          (table (3 (0 1 2)))
                                          (memory)
                                          (local ())
                                          (label ())
                                          (return))
                                         ((call-indirect/unsafe ((((i32 a)) () (empty (i32 a)))
                                                                 -> (((i32 b)) () (((empty (i32 a)) (i32 b)) (gt-u b a))))))
                                         ((((i32 a) (i32 c)) () (((empty (i32 a)) (i32 c)) (= c (i32 1))))
                                          -> (((i32 b)) () (((empty (i32 a)) (i32 b)) (gt-u b a)))))
                                     #f
                                     (list)))

  (test-judgment-holds ⊢ (derivation `(⊢ ((func)
                                          (global)
                                          (table (3 ((((i32 a)) () (empty (= (i32 1) ((i32 lt-u) a (i32 0))))) -> (((i32 b)) () (empty (= (i32 1) ((i32 gt-u) b (i32 0))))))
                                                    ((((i32 a)) () empty) -> (((i32 b)) () (empty (= (i32 1) ((i32 gt-u) b a)))))
                                                    ((((i32 a)) () empty) -> (((i32 b)) () empty))))
                                          (memory)
                                          (local)
                                          (label)
                                          (return))
                                         ((call-indirect/unsafe ((((i32 a)) () empty) -> (((i32 b)) () (empty (= (i32 1) ((i32 gt-u) b a)))))))
                                         ((((i32 a) (i32 c))
                                           ()
                                           ((empty (i32 a)) (i32 c))
                                           (empty (= c (i32 1))))
                                          -> (((i32 b))
                                              ()
                                              (((empty (i32 a)) (i32 c)) (i32 b))
                                              ((empty (= c (i32 1))) (= (i32 1) ((i32 gt-u) b a))))))
                                     "Call-Indirect-Prechk"
                                     (list)))

  (test-judgment-holds ⊢ (derivation `(⊢ ((func)
                                          (global)
                                          (table)
                                          (memory 4096)
                                          (local)
                                          (label)
                                          (return))
                                         ((i32 load/unsafe 0 0))
                                         ((((i32 a))
                                           ()
                                           (empty (i32 a))
                                           ((empty (= (i32 1) ((i32 lt-u) a (i32 1000)))) (= (i32 1) ((i32 ge-u) a (i32 0)))))
                                          -> (((i32 b))
                                              ()
                                              ((empty (i32 a)) (i32 b))
                                              ((empty (= (i32 1) ((i32 lt-u) a (i32 1000)))) (= (i32 1) ((i32 ge-u) a (i32 0)))))))
                                     "Load-Prechk"
                                     (list)))

  (test-judgment-holds ⊢ (derivation `(⊢ ((func)
                                          (global)
                                          (table)
                                          (memory 4096)
                                          (local)
                                          (label)
                                          (return))
                                         ((i32 store/unsafe 0 0))
                                         ((((i32 a) (i32 b))
                                           ()
                                           ((empty (i32 a)) (i32 b))
                                           ((empty (= (i32 1) ((i32 lt-u) a (i32 1000)))) (= (i32 1) ((i32 ge-u) a (i32 0)))))
                                          -> (()
                                              ()
                                              ((empty (i32 a)) (i32 b))
                                              ((empty (= (i32 1) ((i32 lt-u) a (i32 1000)))) (= (i32 1) ((i32 ge-u) a (i32 0)))))))
                                     "Store-Prechk"
                                     (list)))

  (test-judgment-holds ⊢ (derivation `(⊢ ((func)
                                          (global)
                                          (table)
                                          (memory 4096)
                                          (local)
                                          (label)
                                          (return))
                                         ((i32 store/unsafe i8 0 0))
                                         ((((i32 a) (i32 b))
                                           ()
                                           ((empty (i32 a)) (i32 b))
                                           ((empty (= (i32 1) ((i32 lt-u) a (i32 1000)))) (= (i32 1) ((i32 ge-u) a (i32 0)))))
                                          -> (()
                                              ()
                                              ((empty (i32 a)) (i32 b))
                                              ((empty (= (i32 1) ((i32 lt-u) a (i32 1000)))) (= (i32 1) ((i32 ge-u) a (i32 0)))))))
                                     "Store-Packed-Prechk"
                                     (list)))

  (test-judgment-holds ⊢ (derivation `(⊢ ((func)
                                          (global)
                                          (table)
                                          (memory)
                                          (local i32)
                                          (label)
                                          (return))
                                         ((set-local 0) (get-local 0))
                                         ((((i32 a)) ((i32 b)) ((empty (i32 a)) (i32 b)) empty)
                                          -> (((i32 a_2)) ((i32 a)) (((empty (i32 a)) (i32 b)) (i32 a_2)) (empty (= a_2 a)))))
                                     "Composition"
                                     (list
                                      (derivation `(⊢ ((func)
                                                       (global)
                                                       (table)
                                                       (memory)
                                                       (local i32)
                                                       (label)
                                                       (return))
                                                      ((set-local 0))
                                                      ((((i32 a)) ((i32 b)) ((empty (i32 a)) (i32 b)) empty)
                                                       -> (() ((i32 a)) ((empty (i32 a)) (i32 b)) empty)))
                                                  "Set-Local"
                                                  (list))
                                      (derivation `(⊢ ((func)
                                                       (global)
                                                       (table)
                                                       (memory)
                                                       (local i32)
                                                       (label)
                                                       (return))
                                                      ((get-local 0))
                                                      ((() ((i32 a)) ((empty (i32 a)) (i32 b)) empty)
                                                       -> (((i32 a_2)) ((i32 a)) (((empty (i32 a)) (i32 b)) (i32 a_2)) (empty (= a_2 a)))))
                                                  "Get-Local"
                                                  (list)))))

  (define deriv5
    (derivation `(⊢ ((func ((((i32 b)) () (empty (= (i32 1) ((i32 gt-u) b (i32 0)))))
                            -> (((i32 c)) () (empty (= (i32 1) ((i32 gt-u) c b))))))
                     (global)
                     (table)
                     (memory)
                     (local)
                     (label)
                     (return))
                    ((call 0))
                    ((((i32 b)) () ((empty (i32 a)) (i32 b)) (empty (= (i32 1) ((i32 gt-u) b (i32 0)))))
                     -> (((i32 c))
                         ()
                         (((empty (i32 a)) (i32 b)) (i32 c))
                         ((empty (= (i32 1) ((i32 gt-u) b (i32 0)))) (= (i32 1) ((i32 gt-u) c b))))))
                "Call"
                (list)))

  (test-judgment-holds ⊢ deriv5)

  (define deriv6
    (derivation `(⊢ ((func ((((i32 b)) () (empty (= (i32 1) ((i32 gt-u) b (i32 0)))))
                            -> (((i32 c)) () (empty (= (i32 1) ((i32 gt-u) c b))))))
                     (global)
                     (table)
                     (memory)
                     (local)
                     (label)
                     (return))
                    ((call 0))
                    ((((i32 a) (i32 b)) () ((empty (i32 a)) (i32 b)) (empty (= (i32 1) ((i32 gt-u) b (i32 0)))))
                     -> (((i32 a) (i32 c))
                         ()
                         (((empty (i32 a)) (i32 b)) (i32 c))
                         ((empty (= (i32 1) ((i32 gt-u) b (i32 0)))) (= (i32 1) ((i32 gt-u) c b))))))
                "Stack-Poly"
                (list deriv5)))

  (test-judgment-holds ⊢ deriv6)

  (define deriv7
    (derivation `(⊢ ((func ((((i32 b)) () (empty (= (i32 1) ((i32 gt-u) b (i32 0)))))
                            -> (((i32 c)) () (empty (= (i32 1) ((i32 gt-u) c b))))))
                     (global)
                     (table)
                     (memory)
                     (local)
                     (label)
                     (return))
                    ((i32 div-u))
                    ((((i32 a) (i32 c))
                      ()
                      (((empty (i32 a)) (i32 b)) (i32 c))
                      ((empty (= (i32 1) ((i32 gt-u) b (i32 0)))) (= (i32 1) ((i32 gt-u) c b))))
                     -> (((i32 d))
                         ()
                         ((((empty (i32 a)) (i32 b)) (i32 c)) (i32 d))
                         (((empty (= (i32 1) ((i32 gt-u) b (i32 0)))) (= (i32 1) ((i32 gt-u) c b))) (= d ((i32 div-u) a c))))))
                "Binop"
                (list)))

  (test-judgment-holds ⊢ deriv7)

  (define deriv8
    (derivation `(⊢ ((func ((((i32 b)) () (empty (= (i32 1) ((i32 gt-u) b (i32 0)))))
                            -> (((i32 c)) () (empty (= (i32 1) ((i32 gt-u) c b))))))
                     (global)
                     (table)
                     (memory)
                     (local)
                     (label)
                     (return))
                    ((call 0) (i32 div-u))
                    ((((i32 a) (i32 b)) () ((empty (i32 a)) (i32 b)) (empty (= (i32 1) ((i32 gt-u) b (i32 0)))))
                     -> (((i32 d))
                         ()
                         ((((empty (i32 a)) (i32 b)) (i32 c)) (i32 d))
                         (((empty (= (i32 1) ((i32 gt-u) b (i32 0)))) (= (i32 1) ((i32 gt-u) c b))) (= d ((i32 div-u) a c))))))
                "Composition"
                (list deriv6 deriv7)))

  (test-judgment-holds ⊢ deriv8)

  
  #;(test-judgment-holds
   ⊢
   (derivation
    `(⊢ ((func ((((i32 a)) () (empty (i32 a)) (empty (not (= a (i32 0)))))
                ->
                (((i32 b)) () (empty (i32 b)) (empty (= b (i32 0))))))
         (global)
         (table)
         (memory)
         (local i32)
         (label)
         (return))
        ((loop ((() ((i32 a)) (empty (i32 a)) (empty (not (= a (i32 0)))))
                ->
                (() ((i32 b)) (empty (i32 b)) (empty (= b (i32 0)))))
               ((get-local 0)
                (i32 const 1)
                (i32 sub)
                (tee-local 0)
                (br-if 0)))
         (get-local 0))
        ((() ((i32 a)) (empty (i32 a)) (empty (not (= a (i32 0)))))
         ->
         (((i32 c)) ((i32 b)) ((empty (i32 b)) (i32 c)) ((empty (= b (i32 0))) (= c (i32 0))))))
    "Composition"
    'TODO))
        
  #;'(() (func ((((i32 a)) () (empty (i32 a)) (empty (not (= a (i32 0)))))
                ->
                (((i32 b)) () (empty (i32 b)) (empty (= b (i32 0)))))
               (local ()
                 ((loop ((() ((i32 a)) (empty (i32 a)) (empty (not (= a (i32 0)))))
                         ->
                         (() ((i32 b)) (empty (i32 b)) (= b (i32 0))))
                        ((get-local 0)
                         (i32 const 1)
                         (i32 sub)
                         (tee-local 0)
                         (br-if 0)))
                  (get-local 0)))))
)

