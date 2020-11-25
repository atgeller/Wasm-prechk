#lang racket

(require redex
         "IndexTypes.rkt")

;; module -> derivation of ⊢-module or #f
(define (typecheck module)
  (match module
    [`(module ,fs ,globs (,tab) (,mem))
     '()]
    [`(module ,fs ,globs (,tab) ())
     '()]
    [`(module ,fs ,globs () (,mem))
     '()]
    [`(module ,fs ,globs () ())
     '()]))

;; (listof glob) -> derivation of ⊢-module-global-list or #f
(define (typecheck-globals globs)
  (match globs
    [`() (derivation `(⊢-module-global-list () ()) #f (list))]
    [`(,globs ... ,glob)
     (let ([globs-deriv? (typecheck-globals globs)])
       (match globs-deriv?
         [(derivation `(⊢-module-global-list ,_ ((,exs_1 ,tg_1) ...)) _ _)
          (let ([glob-deriv? (typecheck-global `((func ())
                                                 (global ,tg_1)
                                                 (table)
                                                 (memory)
                                                 (local ())
                                                 (label ())
                                                 (return))
                                               glob)])
            (match glob-deriv?
              [(derivation `(⊢-module-global ,_ ,_ (,exs ,tg)) _ _)
               (derivation `(⊢-module-global-list ,globs ((,exs_1 ,tg_1) ... (,exs ,tg)))
                           #f
                           (list globs-deriv? glob-deriv?))]
              [#f #f]))]
         [#f #f]))]))

;; C glob -> derivation of ⊢-module-global or #f
(define (typecheck-global C glob)
  (match glob
    [`(,exs (global (,mut? ,t) ,es))
     (if (and mut? (not (empty? exs)))
         #f
         (let ([ins-deriv? (typecheck-ins C es)])
           (match ins-deriv?
             [(derivation `(⊢ ,_ ,_ (,_ -> (((,t_1 ,_)) ,_ ,_ ,_))) #f (list))
              (if (equal? t t_1)
                  (derivation `(⊢-module-global ,C ,glob (,exs (,mut? ,t)))
                              #f
                              (list ins-deriv?))
                  #f)]
             [#f #f])))]
    [`(,exs (global (#f ,t) im)) (derivation `(⊢-module-global ,C ,glob (,exs (#f ,t))) #f (list))]))

;; C tab -> derivation of ⊢-module-table or #f
(define (typecheck-tab C tab)
  #f)

;; C mem -> derivation of ⊢-module-mem or #f
(define (typecheck-mem C mem)
  #f)

;; C func -> derivation of ⊢-module-func or #f
(define (typecheck-func C func)
  #f)

;; C (listof e) -> derivation of ⊢ or #f
(define (typecheck-ins C es)
  #f)