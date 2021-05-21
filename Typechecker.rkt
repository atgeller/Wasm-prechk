#lang racket

(require redex/reduction-semantics
         "IndexTypes.rkt"
         "IndexTypingRules.rkt"
         "IndexModuleTyping.rkt"
         "Utilities.rkt"
         "Erasure.rkt"
         (prefix-in plain- "WASM-Redex/Validation/Typechecking.rkt"))

(define (typecheck-module module)
  (match (plain-typecheck-module (erase module))
    [(derivation _ _ sub-derivs)
     (let* ([C (term (extract-module-type ,module))]
            [glob-Cs (term (global-contexts (context-globals ,C)))]
            [plain-fs-derivs (filter (λ (d) (match d [(derivation `(⊢-module-func ,_ ,_ ,_) _ _) #t] [_ #f])) sub-derivs)]
            [plain-globs-derivs (filter (λ (d) (match d [(derivation `(⊢-module-global ,_ ,_ ,_) _ _) #t] [_ #f])) sub-derivs)]
            [plain-tabs-derivs (filter (λ (d) (match d [(derivation `(⊢-module-table ,_ ,_ ,_) _ _) #t] [_ #f])) sub-derivs)]
            [plain-mems-derivs (filter (λ (d) (match d [(derivation `(⊢-module-memory ,_ ,_ ,_) _ _) #t] [_ #f])) sub-derivs)])
       (match module
         [`(module ,fs ,globs ,tabs ,mems)
          (let ([fs-derivs (map (curry typecheck-func C) fs plain-fs-derivs)]
                [globs-derivs (map typecheck-global glob-Cs globs plain-globs-derivs)]
                [tab-derivs (map (curry typecheck-table C) tabs plain-tabs-derivs)]
                [mem-derivs (map (curry typecheck-memory C) mems plain-mems-derivs)])
            (if (and (andmap identity fs-derivs)
                     (andmap identity globs-derivs)
                     (andmap identity tab-derivs)
                     (andmap identity mem-derivs))
                (derivation `(⊢-module ,module)
                            #f (append fs-derivs
                                       globs-derivs
                                       tab-derivs
                                       mem-derivs))
                #f))]))]
    [#f #f]))

(define (typecheck-func C f plain-deriv)
  #f)

(define (typecheck-global C glob plain-deriv)
  (match glob
    [`(,exs (global (,mut ,t) (import ,_ ,_)))
     (if (equal? mut 'const)
         (derivation `(⊢-module-global ,C ,glob (,exs (const ,t))) #f (list))
         #f)]
    [`(,exs (global (,mut ,t) ,es))
     (if (or (empty? exs) (equal? mut 'const))
         (match (typecheck-ins C es `(() () empty empty) (first (derivation-subs plain-deriv)))
           [#f #f]
           [ins-deriv ;; We don't have to check the produced type since plain-typechecking verifies it
            (derivation `(⊢-module-global ,C ,glob (,exs (,mut ,t)))
                        #f
                        (list ins-deriv))])
         #f)]))

(define (typecheck-table C tab plain-deriv)
  (match tab
    [`(,exs (table ,i (import ,_ ,_) ,tfis ...))
     (derivation `(⊢-module-table ,C ,tab (,exs (,i ,@tfis)))
                 #f (list))]
    [`(,exs (table ,i ,js ...))
     (redex-let WASMIndexTypes ([((func (tfi ...)) _ _ _ _ _ _) C])
                (derivation `(⊢-module-table ,C ,tab (,exs (,i ,@(map (curry list-ref (term (tfi ...))) js))))
                            #f (list (first (build-derivations (valid-indices (tfi ...) ,js ,i))))))]))

(define (typecheck-memory C mem plain-deriv)
  (match mem
    [`(,exs (memory ,i)) (derivation `(⊢-module-memory ,C ,mem (,exs ,i)) #f (list))]
    [`(,exs (memory ,i (import ,_ ,_))) (derivation `(⊢-module-memory ,C ,mem (,exs ,i)) #f (list))]))

(define (typecheck-ins C ins pre plain-deriv)
  (define (typecheck-e C e pre plain-deriv)
    (match-let ([`(,tis ,locals ,gamma ,phi) pre])
      (match e
        [`(,t const ,c)
         (let* ([a (gensym)]
                [post `(((,t ,a)) ,locals (,gamma (,t ,a)) (,phi (= ,a (,t ,c))))]
                [deriv (derivation `(⊢ ,C (,e) ((() ,locals ,gamma ,phi) -> ,post))
                                   "Const"
                                   empty)])
           (if (empty? tis)
               deriv
               (derivation `(⊢ ,C (,e) (,pre -> ,post)) "Stack-Poly" (list deriv))))]

        [_ #f])))
  
  (cond
    [(empty? ins) (derivation `(⊢ ,C () (,pre -> ,pre)) "Empty" (list))]
    [(empty? (rest ins)) (typecheck-e C (first ins) pre plain-deriv)]
    [else
     ;; Note: this follows the recursive structure of the composition rule
     ;;       could make more efficient by flattening the derivation tree and folding over the instructions
     ;;       but this would have to detect when stack-polymorphism is used
     (match-let ([(derivation _ _ (list plain-es-deriv plain-e-deriv)) plain-deriv])
       (match (typecheck-ins C (drop-right ins 1) pre plain-es-deriv)
         [#f #f]
         [es-deriv (match (typecheck-e C (last ins) (deriv-post es-deriv) plain-e-deriv)
                     [#f #f]
                     [e-deriv (derivation `(⊢ ,C ,ins (,pre -> ,(deriv-post e-deriv)))
                                          "Composition"
                                          (list es-deriv e-deriv))])]))]))

(define (deriv-post deriv)
  (match (derivation-term deriv)
    [`(⊢ ,_ ,_ (,_ -> ,post)) post]))

;; module -> derivation of ⊢-module or #f
;; TODO: distinct exports
#;(define (typecheck module)
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
                             #f (append (list funcs-deriv? globs-deriv?)
                                        tab-derivs
                                        mem-derivs))
                 #f)))
         #f)]))

#;(define (valid-table? fs tab)
  (match tab
    [`(table ,_ ,i ,js)
     (judgment-holds (valid-indices ,fs ,js ,i))]
    [`(table ,_ ,i ,_ ,tfis)
     (= i (length tfis))]))

;; (listof glob) -> derivation of ⊢-module-global-list or #f
#;(define (typecheck-globals globs)
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
                                               glob)]
                [rest-types (map list exs_1 tg_1)])
            (match glob-deriv?
              [(derivation `(⊢-module-global ,_ ,_ (,exs ,tg)) _ _)
               (derivation `(⊢-module-global-list ,globs (,@rest-types ... (,exs ,tg)))
                           #f (list rest-deriv? glob-deriv?))]
              [#f #f]))]
         [#f #f]))]))

;; C glob -> derivation of ⊢-module-global or #f
#;(define (typecheck-global C glob)
  (match glob
    [`(global ,exs global (,mut? ,t) ,es)
     (if (or (empty? exs) (not mut?))
         (let ([ins-deriv? (typecheck-ins C es)])
           (match ins-deriv?
             [(derivation `(⊢ ,_ ,_ (,_ -> (((,t_1 ,_)) ,_ ,_ ,_))) _ _)
              (if (equal? t t_1)
                  (derivation `(⊢-module-global ,C ,glob (,exs (,mut? ,t)))
                              #f (list ins-deriv?))
                  #f)]
             [#f #f]))
         #f)]
    [`(global ,exs (#f ,t) im)
     (derivation `(⊢-module-global ,C ,glob (,exs (#f ,t))) #f (list))]))

;; C tab -> derivation of ⊢-module-table
;; Requires that the table has valid indices and length
#;(define (build-table-derivation C tab)
  (match tab
    [`(table ,exs ,i ,js)
     (redex-let WASMIndexTypes ([((func (tfi ...)) _ _ _ _ _ _) C])
       (derivation `(⊢-module-table ,C ,tab (,exs (,i ,(map (curry list-ref (term (tfi ...))) js))))
                   #f (list (first (build-derivations (valid-indices (tfi ...) ,js ,i))))))]
    [`(table ,exs ,i ,_ ,tfis)
     (derivation `(⊢-module-table ,C ,tab (,exs (,i ,tfis)))
                 #f (list))]))

;; C mem -> derivation of ⊢-module-mem
#;(define (build-memory-derivation C mem)
  (match mem
    [`(memory ,exs ,i)
     (derivation `(⊢-module-mem ,C ,mem (,exs ,i)) #f (list))]
    [`(memory ,exs ,i ,im)
     (derivation `(⊢-module-mem ,C ,mem (,exs ,i)) #f (list))]))

;; C (listof func) -> derivation of ⊢-module-func-list or #f
#;(define (typecheck-funcs C funcs)
  (match funcs
    [`() (derivation `(⊢-module-func-list ,C () ()) #f (list))]
    [`(,func ,rest-funcs ...)
     (let ([func-deriv? (typecheck-func C func)]
           [rest-deriv? (typecheck-funcs C rest-funcs)])
       (match func-deriv?
         [(derivation `(⊢-module-func ,_ ,_ (,exs ,tfi)) _ _)
          (match rest-deriv?
            [(derivation `(⊢-module-func-list ,_ ,_ (,rest-types ...)) _ _)
             (derivation `(⊢-module-func-list ,C ,funcs ((,exs ,tfi) ,@rest-types))
                         #f (list func-deriv? rest-deriv?))]
            [#f #f])]
         [#f #f]))]))

;; C func -> derivation of ⊢-module-func or #f
#;(define (typecheck-func C func)
  (match func
    [`(func ,exs ((((,t ,a) ...) () ,Gamma1 ,phi1) -> (,ti () ,Gamma2 ,phi2)) (local (,tl ...) ,es))
     (if (subset? (term (domain-φ ,phi1)) (term (domain-Γ ,Gamma1)))
         (match C
           [`((func ,tfis) (global ,tgs) (table ,tabs ...) (memory ,mems ...) ,_ ,_ ,_)
            (let* ([ti-args (map list t a)]
                   [al (map gensym tl)]
                   [ti-ls (map list tl al)]
                   [ticond (term (,ti () ,Gamma2 ,phi2))]
                   [C2 `((func ,tfis)
                         (global ,tgs)
                         (table ,@tabs)
                         (memory ,@mems)
                         (local (,@t ,@tl))
                         (label (,ticond))
                         (return ,ticond))]
                   [ins-deriv? (typecheck-ins C2 es
                                              (term (()
                                                     ,(append ti-args ti-ls)
                                                     (build-gamma ,(append ti-args ti-ls))
                                                     (extend ,phi1 (build-phi-zeros ,tl ,al)))))])
              #f)])
         #f)]
    [`(func ,exs ,tfi (import ,_ ,_))
     (derivation `(⊢-module-func ,C ,func (,exs ,tfi)) #f (list))]))

;; C (listof e) ticond -> derivation of ⊢ or #f
;; Typechecking takes the precondition for the instructions
;; if the usage needs to unify with specific postcondition
;; index variables they can rename the vars in the derivation
#;(define (typecheck-ins C es ticond)
  (match ticond
    [`(,tis ,locals ,Γ ,φ)
     (match es
       [`((,t const ,c))
        (let* ([a (gensym)]
               [deriv (derivation
                       `(⊢ ,C ,es ((() ,locals ,Γ ,φ)
                                     ->
                                     (((,t ,a)) ,locals (,Γ (,t ,a)) (,φ (= ,a (,t ,c))))))
                       "Const" (list))])
          (if (empty? tis)
              deriv
              (derivation
               `(⊢ ,C ,es (,ticond
                             ->
                             ((,@tis (,t ,a)) ,locals (,Γ (,t ,a)) (,φ (= ,a (,t ,c))))))
               "Stack-Poly" (list deriv))))]

       [`((unreachable))
        #f]

       [`((nop))
        (let ([deriv (derivation `(⊢ ,C ,es ((() ,locals ,Γ ,φ) -> (() ,locals ,Γ ,φ)))
                                 "Nop" (list))])
          (if (empty? tis)
              deriv
              (derivation `(⊢ ,C ,es (,ticond -> ,ticond)) "Stack-Poly" (list deriv))))]

       [`(drop)
        (if (not (empty? tis))
            (let ([deriv (derivation `(⊢ ,C ,es (((,(last tis)) ,locals ,Γ ,φ) -> (() ,locals ,Γ ,φ)))
                                     "Drop" (list))])
              (if (= (length tis) 1)
                  deriv
                  (derivation `(⊢ ,C ,es (,ticond -> (,(drop-right tis 1) ,locals ,Γ ,φ)))
                              "Stack-Poly" (list deriv))))
            #f)]

       [`()
        (let ([deriv (derivation `(⊢ ,C () ((() ,locals ,Γ ,φ) -> (() ,locals ,Γ ,φ)))
                                 "Empty" (list))])
          (if (empty? tis)
              deriv
              (derivation
               `(⊢ ,C ,es (,ticond -> ,ticond))
               "Stack-Poly" (list deriv))))]

       [`(,ess ... ,e)
        #:when (not (empty? ess))
        (let ([ess-deriv? (typecheck-ins C ess ticond)])
          (match ess-deriv?
            [(derivation `(⊢ ,_ ,_ (,_ -> ,ess-postcond)) _ _)
             (let ([e-deriv? (typecheck-ins C (list e) ess-postcond)])
               (match e-deriv?
                 [(derivation `(⊢ ,_ ,_ (,_ -> ,e-postcond)) _ _)
                  (derivation `(⊢ ,C ,es (,ticond -> ,e-postcond))
                              "Composition"
                              (list ess-deriv? e-deriv?))]
                 [#f #f]))]
            [#f #f]))])]))

#;(module+ test
  (require rackunit)
  
  (test-judgment-holds
   ⊢-module
   (typecheck
    (term (module () () () ()))))

  (test-judgment-holds
   ⊢-module
   (typecheck
    (term (module () () () ((memory () 1))))))
  
  (test-judgment-holds
   ⊢-module
   (typecheck
    (term (module
             ((func ()
                    ((() () empty empty) -> (() () empty empty))
                    (import "test" "test")))
           ()
           ()
           ((memory () 1))))))

  (test-judgment-holds
   ⊢-module
   (typecheck
    (term (module
             ((func ()
                    ((() () empty empty) -> (() () empty empty))
                    (local () ())))
           ()
           ()
           ((memory () 1))))))

  (test-judgment-holds
   ⊢
   (typecheck-ins
    `((func ())
      (global ())
      (table)
      (memory)
      (local ())
      (label ())
      (return (() () empty empty)))
    `((return) (i32 add))
    `(() () empty empty)))

  )