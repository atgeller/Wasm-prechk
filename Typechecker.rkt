#lang racket

(require redex
         "IndexTypes.rkt"
         "IndexModuleTyping.rkt")

;; module -> derivation of ⊢-module or #f
;; TODO: distinct exports
(define (typecheck module)
  (match module
    ;; tab? and mem? are lists of zero or one elements.
    ;; I know this doesn't quite fit with how ? is used normally, but idk what else to use.
    ;; Really should build an optional with the language syntax.
    [`(module ,fs ,globs ,tab? ,mem?)
     (if (andmap (curry valid-table? fs) tab?)
         (let ([C (term (extract-module-type ,module))])
           ;; tab-derivs, mem-derivs will both be either zero or one - this is so hacky
           (let ([tab-derivs (map (curry build-table-derivation C) tab?)]
                 [mem-derivs (map (curry build-memory-derivation C) mem?)]
                 [globs-deriv? (typecheck-globals globs)]
                 [funcs-deriv? (typecheck-funcs C fs)])
             (if (and globs-deriv? funcs-deriv?)
                 (derivation `(⊢-module ,module)
                             #f
                             (append (list funcs-deriv? globs-deriv?)
                                     tab-derivs
                                     mem-derivs))
                 #f)))
         #f)]))

(define (valid-table? fs tab)
  (match tab
    [`(table ,_ ,i ,js)
     (judgment-holds (valid-indices ,fs ,js ,i))]
    [`(table ,_ ,i ,_ ,tfis)
     (= i (length tfis))]))

;; (listof glob) -> derivation of ⊢-module-global-list or #f
(define (typecheck-globals globs)
  (match globs
    [`() (derivation `(⊢-module-global-list () ()) #f (list))]
    [`(,rest-globs ... ,glob)
     (let ([rest-deriv? (typecheck-globals rest-globs)])
       (match rest-deriv?
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
                           (list rest-deriv? glob-deriv?))]
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
             [(derivation `(⊢ ,_ ,_ (,_ -> (((,t_1 ,_)) ,_ ,_ ,_))) _ _)
              (if (equal? t t_1)
                  (derivation `(⊢-module-global ,C ,glob (,exs (,mut? ,t)))
                              #f
                              (list ins-deriv?))
                  #f)]
             [#f #f])))]
    [`(global ,exs (#f ,t) im)
     (derivation `(⊢-module-global ,C ,glob (,exs (#f ,t))) #f (list))]))

;; C tab -> derivation of ⊢-module-table
;; Requires that the table has valid indices and length
(define (build-table-derivation C tab)
  (match tab
    [`(table ,exs ,i ,js)
     (redex-let WASMIndexTypes ([((func (tfi ...)) _ _ _ _ _ _) C])
       (derivation `(⊢-module-table ,C ,tab (,exs (,i ,(map (curry list-ref (term (tfi ...))) js))))
                   #f
                   (list (first (build-derivations (valid-indices (tfi ...) ,js ,i))))))]
    [`(table ,exs ,i ,_ ,tfis)
     (derivation `(⊢-module-table ,C ,tab (,exs (,i ,tfis)))
                 #f
                 (list))]))

;; C mem -> derivation of ⊢-module-mem
(define (build-memory-derivation C mem)
  (match mem
    [`(memory ,exs ,i)
     (derivation `(⊢-module-mem ,C ,mem (,exs ,i)) #f (list))]
    [`(memory ,exs ,i ,im)
     (derivation `(⊢-module-mem ,C ,mem (,exs ,i)) #f (list))]))

;; C (listof func) -> derivation of ⊢-module-func-list or #f
(define (typecheck-funcs C funcs)
  (match funcs
    [`() (derivation `(⊢-module-func-list () () #f (list)))]
    [`(,func ,rest-funcs ...)
     (let ([func-deriv? (typecheck-func C func)]
           [rest-deriv? (typecheck-funcs C rest-funcs)])
       (match func-deriv?
         [(derivation `(⊢-module-func ,_ ,_ (,exs ,tfi)) _ _)
          (match rest-deriv?
            [(derivation `(⊢-module-func-list ,_ ,_ ((,exs_1 ,tfi_1) ...)) _ _)
             (derivation `(⊢-module-func-list ,C ,funcs ((,exs ,tfi) (,exs_1 ,tfi_1) ...))
                         #f
                         (list func-deriv? rest-deriv?))]
            [#f #f])]
         [#f #f]))]))

;; C func -> derivation of ⊢-module-func or #f
(define (typecheck-func C func)
  (match func
    [`(func ,exs ,tfi (local ,ts ,es))
     #f]
    [`(func ,exs ,tfi (import ,_ ,_))
     (derivation `(⊢-module-func ,C ,func (,exs ,tfi)))]))

;; C (listof e) -> derivation of ⊢ or #f
(define (typecheck-ins C es)
  #f)