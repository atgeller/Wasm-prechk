#lang racket

(require redex
         "IndexTypes.rkt"
         "IndexModuleTyping.rkt")

;; module -> derivation of ⊢-module or #f
(define (typecheck module)
  (match module
    [`(module ,fs ,globs ,tab? ,mem?)
     #f]))

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
    [`(global ,exs global (,mut? ,t) ,es)
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
    [`(global ,exs (#f ,t) im) (derivation `(⊢-module-global ,C ,glob (,exs (#f ,t))) #f (list))]))

;; C tab -> derivation of ⊢-module-table or #f
;; TODO: This typecheck function confusingly needs to produce a derivation with a different context,
;;       it needs to add the type of the table to the context since the type isn't known until checked.
(define (typecheck-tab C tab)
  (match tab
    [`(table ,exs ,i ,js)
     (redex-let WASMIndexTypes ([((func (tfi ...)) _ _ _ _ _ _) C])
       (if (judgment-holds (valid-indices (tfi ...) ,js ,i))
           (derivation `(⊢-module-table ,C ,tab (,exs (,i ,(map (curry list-ref (term (tfi ...))) js))))
                       #f
                       (list (first (build-derivations (valid-indices (tfi ...) ,js ,i)))))
           #f))]
    [`(table ,exs ,i ,_ ,tfis)
     (if (equal? i (length tfis))
         (derivation `(⊢-module-table ,C ,tab (,exs (,i ,tfis)))
                     #f
                     (list))
         #f)]))

;; C mem -> derivation of ⊢-module-mem or #f
;; TODO: This function also needs to change the context passed to them, maybe the structure needs to be changed
(define (typecheck-mem C mem)
  (match mem
    [`(memory ,exs ,i)
     (derivation `(⊢-module-mem ,C ,mem (,exs ,i)) #f (list))]
    [`(memory ,exs ,i ,im)
     (derivation `(⊢-module-mem ,C ,mem (,exs ,i)) #f (list))]))

;; C func -> derivation of ⊢-module-func or #f
(define (typecheck-func C func)
  #f)

;; C (listof e) -> derivation of ⊢ or #f
(define (typecheck-ins C es)
  #f)