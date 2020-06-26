#lang racket

(module+ test
  (require "../IndexTypes.rkt"
           "../IndexTypingRules.rkt"
           redex)

  (define dummy-store '(() (table ()) (memory ())))

  (define empty-context `((func ()) (global ()) (table) (memory) (local ()) (label ()) (return)))
  
  #;(test-judgment-holds ⊢
   (derivation `(⊢ ,dummy-store 0 ,empty-context ((if ((((i32 a) (i32 b)) empty) -> ((i32 c) empty))
                                       (i32 div/unsafe)
                                       (i32 const -1))
                   (((i32 a) (i32 b) (i32 b)) (((empty (a : i32)) (b : i32)) (>= b 0)))
                   ))))

  (test-judgment-holds ⊢
                       (derivation `(⊢ ,dummy-store 0 ,empty-context ((i32 sub))
                                       ((((i32 b) (i32 c)) () ()
                                         ((((empty (i32 a)) (i32 b)) (i32 c))
                                          (not (eq b c))))
                                        ->
                                        (((i32 d)) () ()
                                         ((((((empty (i32 a)) (i32 b)) (i32 c))
                                            (not (eq b c))) (i32 d)) (eq d (sub b c))))))
                                   #f
                                   (list)))

  (test-judgment-holds ⊢
                       (derivation `(⊢ ,dummy-store 0 ,empty-context ((i32 sub))
                                       ((((i32 a) (i32 b) (i32 c)) () ()
                                         ((((empty (i32 a)) (i32 b)) (i32 c))
                                          (not (eq b c))))
                                        ->
                                        (((i32 a) (i32 d)) () ()
                                         ((((((empty (i32 a)) (i32 b)) (i32 c))
                                           (not (eq b c))) (i32 d)) (eq d (sub b c))))))
                                   #f
                                   (list
                             (derivation `(⊢ ,dummy-store 0 ,empty-context ((i32 sub))
                                             ((((i32 b) (i32 c)) () ()
                                               ((((empty (i32 a)) (i32 b)) (i32 c))
                                                (not (eq b c))))
                                              ->
                                              (((i32 d)) () ()
                                               ((((((empty (i32 a)) (i32 b)) (i32 c))
                                                  (not (eq b c))) (i32 d)) (eq d (sub b c))))))
                                         #f
                                         (list)))))

  #;(test-judgment-holds ⊢
                       (derivation `(⊢ ,dummy-store 0 ,empty-context ((i32 div/unsafe))
                                ((((i32 a) (i32 d)) () ()
                                  ((((((empty (i32 a)) (i32 b)) (i32 c)) (i32 d))
                                     (not (eq d (i32 0)))) (eq d (sub b c))))
                                 ->
                                 (((i32 e)) () ()
                                  ((((((((empty (i32 a)) (i32 b)) (i32 c)) (i32 d))
                                     (not (eq d (i32 0)))) (eq d (sub b c))) (i32 e)) (eq e (div a d))))))
                            #f
                            (list)))

  (test-judgment-holds ⊢
   (derivation `(⊢ ,dummy-store 0 ,empty-context ((i32 sub) (i32 div/unsafe))
                   ((((i32 a) (i32 b) (i32 c)) () ()
                     ((((empty (i32 a)) (i32 b)) (i32 c))
                      (not (eq b c))))
                    ->
                    (((i32 e)) () ()
                     ((((((((empty (i32 a)) (i32 b)) (i32 c)) (i32 d))
                         (not (eq d (i32 0)))) (eq d (sub b c))) (i32 e)) (eq e (div a d))))))
               #f
               (list
                (derivation `(⊢ ,dummy-store 0 ,empty-context ((i32 sub))
                                ((((i32 a) (i32 b) (i32 c)) () ()
                                  ((((empty (i32 a)) (i32 b)) (i32 c))
                                   (not (eq b c))))
                                 ->
                                 (((i32 a) (i32 d)) () ()
                                  ((((((empty (i32 a)) (i32 b)) (i32 c))
                                     (not (eq b c))) (i32 d)) (eq d (sub b c))))))
                                   #f
                                   (list
                             (derivation `(⊢ ,dummy-store 0 ,empty-context ((i32 sub))
                                             ((((i32 b) (i32 c)) () ()
                                               ((((empty (i32 a)) (i32 b)) (i32 c))
                                                (not (eq b c))))
                                              ->
                                              (((i32 d)) () ()
                                               ((((((empty (i32 a)) (i32 b)) (i32 c))
                                                  (not (eq b c))) (i32 d)) (eq d (sub b c))))))
                                         #f
                                         (list))))
                (derivation `(⊢ ,dummy-store 0 ,empty-context ((i32 div/unsafe))
                                ((((i32 a) (i32 d)) () ()
                                  ((((((empty (i32 a)) (i32 b)) (i32 c)) (i32 d))
                                     (not (eq d (i32 0)))) (eq d (sub b c))))
                                 ->
                                 (((i32 e)) () ()
                                  ((((((((empty (i32 a)) (i32 b)) (i32 c)) (i32 d))
                                     (not (eq d (i32 0)))) (eq d (sub b c))) (i32 e)) (eq e (div a d))))))
                            #f
                            (list)))))

  ;; This case worked in Adam's brain, but not in practice due to possible integer overflow
  #;(test-judgment-holds ⊢ (derivation `(⊢ ,dummy-store 0 ((func
                                           (((((i32 a)) () () ((empty (i32 a)) (lt a (i32 0)))) -> (((i32 b)) () () (((empty (i32 a)) (i32 b)) (gt b (i32 0)))))
                                            ((((i32 a)) () () (empty (i32 a))) -> (((i32 b)) () () (((empty (i32 a)) (i32 b)) (eq b (add a (i32 1))))))
                                            ((((i32 a)) () () (empty (i32 a))) -> (((i32 b)) () () ((empty (i32 a)) (i32 b))))
                                            ((((i32 a) (i32 b)) () () ((empty (i32 a)) (i32 b))) -> (((i32 c)) () () (((empty (i32 a)) (i32 b)) (i32 c))))))
                                          (global ())
                                          (table (3 (0 1 2)))
                                          (memory)
                                          (local ())
                                          (label ())
                                          (return))
                                         ((call-indirect/unsafe ((((i32 a)) () () (empty (i32 a)))
                                                                 -> (((i32 b)) () () (((empty (i32 a)) (i32 b)) (gt b a))))))
                                         ((((i32 a) (i32 c)) () () (((empty (i32 a)) (i32 c)) (eq c (i32 1))))
                                          -> (((i32 b)) () () (((empty (i32 a)) (i32 b)) (gt b a)))))
                                     #f
                                     (list)))

  (test-judgment-holds ⊢ (derivation `(⊢ ,dummy-store 0
                                         ((func
                                           (((((i32 a)) () () ((empty (i32 a)) (lt a (i32 0)))) -> (((i32 b)) () () (((empty (i32 a)) (i32 b)) (gt b (i32 0)))))
                                            ((((i32 a)) () () (empty (i32 a))) -> (((i32 b)) () () (((empty (i32 a)) (i32 b)) (gt b a))))
                                            ((((i32 a)) () () (empty (i32 a))) -> (((i32 b)) () () ((empty (i32 a)) (i32 b))))
                                            ((((i32 a) (i32 b)) () () ((empty (i32 a)) (i32 b))) -> (((i32 c)) () () (((empty (i32 a)) (i32 b)) (i32 c))))))
                                          (global ())
                                          (table (3 (((((i32 a)) () () ((empty (i32 a)) (lt a (i32 0)))) -> (((i32 b)) () () (((empty (i32 a)) (i32 b)) (gt b (i32 0)))))
                                                     ((((i32 a)) () () (empty (i32 a))) -> (((i32 b)) () () (((empty (i32 a)) (i32 b)) (gt b a))))
                                                     ((((i32 a)) () () (empty (i32 a))) -> (((i32 b)) () () ((empty (i32 a)) (i32 b)))))))
                                          (memory)
                                          (local ())
                                          (label ())
                                          (return))
                                         ((call-indirect/unsafe ((((i32 a)) () () (empty (i32 a)))
                                                                 -> (((i32 b)) () () (((empty (i32 a)) (i32 b)) (ge b a))))))
                                         ((((i32 a) (i32 c)) () () (((empty (i32 a)) (i32 c)) (eq c (i32 1))))
                                          -> (((i32 b)) () () (((empty (i32 a)) (i32 b)) (ge b a)))))
                                     #f
                                     (list)))

  (test-judgment-holds ⊢ (derivation `(⊢ ,dummy-store 0
                                         ((func ())
                                          (global ())
                                          (table)
                                          (memory 4096)
                                          (local ())
                                          (label ())
                                          (return))
                                         ((i32 load/unsafe 0 0))
                                         ((((i32 a)) () () (((empty (i32 a)) (lt a (i32 1000))) (ge a (i32 0))))
                                          -> (((i32 b)) () () ((((empty (i32 a)) (lt a (i32 1000))) (ge a (i32 0))) (i32 b)))))
                                     #f
                                     (list)))

  (test-judgment-holds ⊢ (derivation `(⊢ ,dummy-store 0
                                         ((func ())
                                          (global ())
                                          (table)
                                          (memory 4096)
                                          (local ())
                                          (label ())
                                          (return))
                                         ((i32 store/unsafe 0 0))
                                         ((((i32 a) (i32 b)) () () (((empty (i32 a)) (lt a (i32 1000))) (ge a (i32 0))))
                                          -> (() () () (((empty (i32 a)) (lt a (i32 1000))) (ge a (i32 0))))))
                                     #f
                                     (list)))

  (test-judgment-holds ⊢ (derivation `(⊢ ,dummy-store 0
                                         ((func ())
                                          (global ())
                                          (table)
                                          (memory 4096)
                                          (local ())
                                          (label ())
                                          (return))
                                         ((i32 store/unsafe (i8) 0 0))
                                         ((((i32 a) (i32 b)) () () (((empty (i32 a)) (lt a (i32 4096))) (ge a (i32 0))))
                                          -> (() () () (((empty (i32 a)) (lt a (i32 4096))) (ge a (i32 0))))))
                                     #f
                                     (list)))

  (test-judgment-holds ⊢ (derivation `(⊢ ,dummy-store 0
                                         ((func ())
                                          (global ())
                                          (table)
                                          (memory)
                                          (local (i32))
                                          (label ())
                                          (return))
                                         ((set-local 0) (get-local 0))
                                         ((((i32 a)) ((i32 b)) () ((empty (i32 a)) (i32 b)))
                                          -> (((i32 d)) ((i32 c)) () ((((((empty (i32 a)) (i32 b)) (i32 c)) (eq c a)) (i32 d)) (eq d c)))))
                                     #f
                                     (list
                                      (derivation `(⊢ ,dummy-store 0
                                                      ((func ())
                                                       (global ())
                                                       (table)
                                                       (memory)
                                                       (local (i32))
                                                       (label ())
                                                       (return))
                                                      ((set-local 0))
                                                      ((((i32 a)) ((i32 b)) () ((empty (i32 a)) (i32 b)))
                                                       -> (() ((i32 c)) () ((((empty (i32 a)) (i32 b)) (i32 c)) (eq c a)))))
                                                  #f
                                                  (list))
                                      (derivation `(⊢ ,dummy-store 0
                                                      ((func ())
                                                       (global ())
                                                       (table)
                                                       (memory)
                                                       (local (i32))
                                                       (label ())
                                                       (return))
                                                      ((get-local 0))
                                                      ((() ((i32 c)) () ((((empty (i32 a)) (i32 b)) (i32 c)) (eq c a)))
                                                       -> (((i32 d)) ((i32 c)) () ((((((empty (i32 a)) (i32 b)) (i32 c)) (eq c a)) (i32 d)) (eq d c)))))
                                                  #f
                                                  (list)))))

  (test-judgment-holds ⊢ (derivation `(⊢ ,dummy-store 0
                                         ((func (((((i32 b)) () () ((empty (i32 b)) (gt b (i32 0))))
                                                  -> (((i32 c)) () () ((empty (i32 c)) (gt c b))))))
                                          (global ())
                                          (table)
                                          (memory)
                                          (local ())
                                          (label ())
                                          (return))
                                         ((call 0) (i32 div))
                                         ((((i32 a) (i32 b)) () () (((empty (i32 a)) (i32 b)) (gt b (i32 0))))
                                          -> (((i32 d)) () () (((((((empty (i32 a)) (i32 b)) (gt b (i32 0))) (i32 c)) (gt c b)) (i32 d)) (eq d (div a c))))))
                                     #f
                                     (list
                                      (derivation `(⊢ ,dummy-store 0
                                                      ((func (((((i32 b)) () () ((empty (i32 b)) (gt b (i32 0))))
                                                               -> (((i32 c)) () () ((empty (i32 c)) (gt c b))))))
                                                       (global ())
                                                       (table)
                                                       (memory)
                                                       (local ())
                                                       (label ())
                                                       (return))
                                                      ((call 0))
                                                      ((((i32 a) (i32 b)) () () (((empty (i32 a)) (i32 b)) (gt b (i32 0))))
                                                       -> (((i32 a) (i32 c)) () () (((((empty (i32 a)) (i32 b)) (gt b (i32 0))) (i32 c)) (gt c b)))))
                                                  #f
                                                  (list
                                                   (derivation `(⊢ ,dummy-store 0
                                                                   ((func (((((i32 b)) () () ((empty (i32 b)) (gt b (i32 0))))
                                                                            -> (((i32 c)) () () ((empty (i32 c)) (gt c b))))))
                                                                    (global ())
                                                                    (table)
                                                                    (memory)
                                                                    (local ())
                                                                    (label ())
                                                                    (return))
                                                                   ((call 0))
                                                                   ((((i32 b)) () () (((empty (i32 a)) (i32 b)) (gt b (i32 0))))
                                                                    -> (((i32 c)) () () (((((empty (i32 a)) (i32 b)) (gt b (i32 0))) (i32 c)) (gt c b)))))
                                                               #f
                                                               (list))))
                                      (derivation `(⊢ ,dummy-store 0
                                                      ((func (((((i32 b)) () () ((empty (i32 b)) (gt b (i32 0))))
                                                               -> (((i32 c)) () () ((empty (i32 c)) (gt c b))))))
                                                       (global ())
                                                       (table)
                                                       (memory)
                                                       (local ())
                                                       (label ())
                                                       (return))
                                                      ((i32 div))
                                                      ((((i32 a) (i32 c)) () () (((((empty (i32 a)) (i32 b)) (gt b (i32 0))) (i32 c)) (gt c b)))
                                                       -> (((i32 d)) () () (((((((empty (i32 a)) (i32 b)) (gt b (i32 0))) (i32 c)) (gt c b)) (i32 d)) (eq d (div a c))))))
                                                  #f
                                                  (list))))))

