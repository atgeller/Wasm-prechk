#lang racket

(require redex/reduction-semantics
         "IndexTypes.rkt"
         "IndexTypingRules.rkt"
         "IndexModuleTyping.rkt"
         "Utilities.rkt"
         "WASM-Redex/Utilities.rkt"
         "Erasure.rkt"
         "SubTyping.rkt"
         (prefix-in plain- "WASM-Redex/Validation/Typechecking.rkt"))

(define (ivar-pairs tis-a tis-b)
  (map (λ (ti-a ti-b) (list (second ti-a) (second ti-b))) tis-a tis-b))

(define (typecheck-module module)
  (let* ([C (term (extract-module-type ,module))]
         [glob-Cs (term (global-contexts (context-globals ,C)))])
    (match module
      [`(module ,fs ,globs ,tabs ,mems)
       (let ([fs-derivs (map (curry typecheck-func C) fs)]
             [globs-derivs (map typecheck-global glob-Cs globs)]
             [tab-derivs (map (curry typecheck-table C) tabs)]
             [mem-derivs (map (curry typecheck-memory C) mems)])
         (if (and (andmap identity fs-derivs)
                  (andmap identity globs-derivs)
                  (andmap identity tab-derivs)
                  (andmap identity mem-derivs))
             (derivation `(⊢-module ,module)
                         #f (append fs-derivs
                                    globs-derivs
                                    tab-derivs
                                    mem-derivs))
             #f))])))

(define (typecheck-func C f)
  (match f
    [`(,exs (func ,tfi (import ,_ ,_)))
     (derivation `(⊢-module-func ,C ,f (,exs ,tfi)) #f empty)]
    
    [`(,exs (func ((,tis-pre () ,φ-pre) -> (,tis-post () ,φ-post)) (local ,ts ,ins)))
     (let* ([locals-pre (map (λ (t) `(,t ,(gensym))) ts)]
            [locals-post (map (λ (t) `(,t ,(gensym))) ts)]
            [φ-zeros (term (extend ,φ-pre (build-phi-zeros ,ts ,(map second locals-pre))))]
            [C2 (term (with-return
                          (add-label (with-locals ,C ,(append (map first tis-pre) ts))
                                     (,tis-post ,locals-post ,φ-post))
                        (,tis-post ,locals-post ,φ-post)))]
            [Γ-pre (term (build-gamma (,@tis-pre ,@locals-pre)))])
       (match (plain-typecheck-ins (erase-C C2) (map erase-e ins) empty (map first tis-post))
         [#f #f]
         [plain-deriv
          (match (typecheck-ins C2 ins `(() ,(append tis-pre locals-pre) ,Γ-pre ,φ-pre) plain-deriv)
            [#f #f]
            [ins-deriv
             (match-let ([`(,tis-ins-post ,_ ,Γ-post ,φ-ins-post) (deriv-post ins-deriv)])
               (if (term (satisfies ,Γ-post ,φ-ins-post (substitute-ivars ,@(ivar-pairs tis-ins-post tis-post) ,φ-post)))
                   (derivation `(⊢-module-func ,C ,f (,exs ((,tis-pre () ,φ-pre) -> (,tis-post () ,φ-post))))
                               #f
                               (list ins-deriv))
                   #f))])]))]))

(define (typecheck-global C glob)
  (match glob
    [`(,exs (global (,mut ,t) (import ,_ ,_)))
     (if (equal? mut 'const)
         (derivation `(⊢-module-global ,C ,glob (,exs (const ,t))) #f empty)
         #f)]
    [`(,exs (global (,mut ,t) ,es))
     (if (or (empty? exs) (equal? mut 'const))
         (match (plain-typecheck-ins (erase-C C) (map erase-e es) empty (list t))
           [#f #f]
           [plain-deriv
            (match (typecheck-ins C es `(() () empty empty) plain-deriv)
              [#f #f]
              [ins-deriv ;; We don't have to check the produced type since plain-typechecking verifies it
               (derivation `(⊢-module-global ,C ,glob (,exs (,mut ,t)))
                           #f
                           (list ins-deriv))])])
         #f)]))

(define (typecheck-table C tab)
  (match tab
    [`(,exs (table ,i (import ,_ ,_) ,tfis ...))
     (derivation `(⊢-module-table ,C ,tab (,exs (,i ,@tfis))) #f empty)]
    [`(,exs (table ,i ,js ...))
     (match-let ([`((func ,tfis ...) _ _ _ _ _ _) C])
       (if (judgment-holds (valid-indices ,tfis ,js ,i))
           (derivation `(⊢-module-table ,C ,tab (,exs (,i ,@(map (curry list-ref tfis) js))))
                       #f (list (first (build-derivations (valid-indices ,tfis ,js ,i)))))
           #f))]))

(define (typecheck-memory C mem)
  (match mem
    [`(,exs (memory ,i)) (derivation `(⊢-module-memory ,C ,mem (,exs ,i)) #f empty)]
    [`(,exs (memory ,i (import ,_ ,_))) (derivation `(⊢-module-memory ,C ,mem (,exs ,i)) #f empty)]))

(define (typecheck-ins C ins pre plain-deriv)
  
  (define (stack-polyize deriv e-pre)
    (match-let ([`(,e-pre-tis ,_ ,_ ,_) e-pre]
                [(derivation `(⊢ ,d-C ,d-ins ((,d-pre-tis ,d-pre-locals ,d-pre-gamma ,d-pre-phi)
                                              ->
                                              (,d-post-tis ,d-post-locals ,d-post-gamma ,d-post-phi))) _ _) deriv])
      (if (= (length e-pre-tis) (length d-pre-tis))
          deriv
          (derivation `(⊢ ,d-C ,d-ins ((,e-pre-tis ,d-pre-locals ,d-pre-gamma ,d-pre-phi)
                                       ->
                                       ((,@(drop-right e-pre-tis (length d-pre-tis)) ,@d-post-tis)
                                        ,d-post-locals
                                        ,d-post-gamma
                                        ,d-post-phi)))
                      "Stack-Poly" (list deriv)))))
  
  (define (typecheck-e e pre plain-deriv)
    (match-let ([`(,tis ,locals ,gamma ,phi) pre])
      (match e
        [`(,t const ,c)
         (let ([a (gensym)])
           (stack-polyize
            (derivation `(⊢ ,C ((,t const ,c))
                            ((() ,locals ,gamma ,phi)
                             ->
                             (((,t ,a)) ,locals (,gamma (,t ,a)) (,phi (= ,a (,t ,c))))))
                        "Const"
                        empty)
            pre))]

        [`(,t ,(? (redex-match? WASMIndexTypes unop) uop))
         (match-let ([`(,_ ... (,_ ,a1)) tis])
           (let ([a (gensym)])
             (stack-polyize
              (derivation `(⊢ ,C ((,t ,uop))
                              ((((,t ,a1)) ,locals ,gamma ,phi)
                               ->
                               (((,t ,a)) ,locals (,gamma (,t ,a)) (,phi (= ,a ((,t ,uop) ,a1))))))
                          "Unop"
                          empty)
              pre)))]

        [`(,t div-s/unsafe)
         (match-let ([`(,_ ... (,_ ,a1) (,_ ,a2)) tis])
           (if (term (satisfies ,gamma ,phi (empty (not (= ,a2 (,t 0))))))
               (let ([a (gensym)])
                 (stack-polyize
                  (derivation `(⊢ ,C ((,t div-s/unsafe))
                                  ((((,t ,a1) (,t ,a2)) ,locals ,gamma ,phi)
                                   ->
                                   (((,t ,a)) ,locals (,gamma (,t ,a)) (,phi (= ,a ((,t div-s) ,a1 ,a2))))))
                              "Div-S-Prechk"
                              empty)
                  pre))
               #f))]

        [`(,t div-u/unsafe)
         (match-let ([`(,_ ... (,_ ,a1) (,_ ,a2)) tis])
           (if (term (satisfies ,gamma ,phi (empty (not (= ,a2 (,t 0))))))
               (let ([a (gensym)])
                 (stack-polyize
                  (derivation `(⊢ ,C ((,t div-u/unsafe))
                                  ((((,t ,a1) (,t ,a2)) ,locals ,gamma ,phi)
                                   ->
                                   (((,t ,a)) ,locals (,gamma (,t ,a)) (,phi (= ,a ((,t div-u) ,a1 ,a2))))))
                              "Div-U-Prechk"
                              empty)
                  pre))
               #f))]

        [`(,t rem-s/unsafe)
         (match-let ([`(,_ ... (,_ ,a1) (,_ ,a2)) tis])
           (if (term (satisfies ,gamma ,phi (empty (not (= ,a2 (,t 0))))))
               (let ([a (gensym)])
                 (stack-polyize
                  (derivation `(⊢ ,C ((,t rem-s/unsafe))
                                  ((((,t ,a1) (,t ,a2)) ,locals ,gamma ,phi)
                                   ->
                                   (((,t ,a)) ,locals (,gamma (,t ,a)) (,phi (= ,a ((,t rem-s) ,a1 ,a2))))))
                              "Rem-S-Prechk"
                              empty)
                  pre))
               #f))]

        [`(,t rem-u/unsafe)
         (match-let ([`(,_ ... (,_ ,a1) (,_ ,a2)) tis])
           (if (term (satisfies ,gamma ,phi (empty (not (= ,a2 (,t 0))))))
               (let ([a (gensym)])
                 (stack-polyize
                  (derivation `(⊢ ,C ((,t rem-u/unsafe))
                                  ((((,t ,a1) (,t ,a2)) ,locals ,gamma ,phi)
                                   ->
                                   (((,t ,a)) ,locals (,gamma (,t ,a)) (,phi (= ,a ((,t rem-u) ,a1 ,a2))))))
                              "Rem-U-Prechk"
                              empty)
                  pre))
               #f))]

        [`(,t ,(? (redex-match? WASMIndexTypes binop) bop))
         (match-let ([`(,_ ... (,_ ,a1) (,_ ,a2)) tis])
           (let ([a (gensym)])
             (stack-polyize
              (derivation `(⊢ ,C ((,t ,bop))
                              ((((,t ,a1) (,t ,a2)) ,locals ,gamma ,phi)
                               ->
                               (((,t ,a)) ,locals (,gamma (,t ,a)) (,phi (= ,a ((,t ,bop) ,a1 ,a2))))))
                          "Binop"
                          empty)
              pre)))]

        [`(,t ,(? (redex-match? WASMIndexTypes testop) top))
         (match-let ([`(,_ ... (,_ ,a1)) tis])
           (let ([a2 (gensym)])
             (stack-polyize
              (derivation `(⊢ ,C ((,t ,top))
                              ((((,t ,a1)) ,locals ,gamma ,phi)
                               ->
                               (((i32 ,a2)) ,locals (,gamma (i32 ,a2)) (,phi (= ,a2 ((,t ,top) ,a1))))))
                          "Testop"
                          empty)
              pre)))]

        [`(,t ,(? (redex-match? WASMIndexTypes relop) rop))
         (match-let ([`(,_ ... (,_ ,a1) (,_ ,a2)) tis])
           (let ([a (gensym)])
             (stack-polyize
              (derivation `(⊢ ,C ((,t ,rop))
                              ((((,t ,a1) (,t ,a2)) ,locals ,gamma ,phi)
                               ->
                               (((i32 ,a)) ,locals (,gamma (i32 ,a)) (,phi (= ,a ((,t ,rop) ,a1 ,a2))))))
                          "Relop"
                          empty)
              pre)))]

        [`(,t1 convert ,t2)
         (match-let ([`(,_ ... (,_ ,a2)) tis])
           (let ([a1 (gensym)])
             (stack-polyize
              (derivation `(⊢ ,C ((,t1 convert ,t2))
                              ((((,t2 ,a2)) ,locals ,gamma ,phi)
                               ->
                               (((,t1 ,a1)) ,locals (,gamma (,t1 ,a1)) (,phi (= ,a1 ((,t1 convert ,t2) ,a2))))))
                          "Convert"
                          empty)
              pre)))]

        [`(,t1 convert ,t2 ,sx)
         (match-let ([`(,_ ... (,_ ,a2)) tis])
           (let ([a1 (gensym)])
             (stack-polyize
              (derivation `(⊢ ,C ((,t1 convert ,t2 ,sx))
                              ((((,t2 ,a2)) ,locals ,gamma ,phi)
                               ->
                               (((,t1 ,a1)) ,locals (,gamma (,t1 ,a1)) (,phi (= ,a1 ((,t1 convert ,t2 ,sx) ,a2))))))
                          "Convert-SX"
                          empty)
              pre)))]

        [`(,t1 reinterpret ,t2)
         (match-let ([`(,_ ... (,_ ,a2)) tis])
           (let ([a1 (gensym)])
             (stack-polyize
              (derivation `(⊢ ,C ((,t1 reinterpret ,t2))
                              ((((,t2 ,a2)) ,locals ,gamma ,phi)
                               ->
                               (((,t1 ,a1)) ,locals (,gamma (,t1 ,a1)) (,phi (= ,a1 ((,t1 reinterpret ,t2) ,a2))))))
                          "Reinterpret"
                          empty)
              pre)))]

        [`unreachable
         (let* ([post-tis (map (λ (t) `(,t ,(gensym))) (deriv-post plain-deriv))]
                [post-gamma (term (build-gamma (merge ,post-tis ,locals)))])
           (derivation `(⊢ ,C (unreachable) (,pre -> (,post-tis ,locals ,post-gamma (empty ⊥)))) "Unreachable" empty))]

        [`nop
         (stack-polyize
          (derivation `(⊢ ,C (nop) ((() ,locals ,gamma ,phi) -> (() ,locals ,gamma ,phi))) "Nop" empty)
          pre)]

        [`drop
         (match-let ([`(,_ ... (,t ,a)) tis])
           (stack-polyize
            (derivation `(⊢ ,C (drop) ((((,t ,a)) ,locals ,gamma ,phi) -> (() ,locals ,gamma ,phi))) "Drop" empty)
            pre))]

        [`select
         (match-let ([`(,_ ... (,t ,a1) (,_ ,a2) (i32 ,a)) tis])
           (let ([a3 (gensym)])
             (stack-polyize
              (derivation `(⊢ ,C (select)
                              ((((,t ,a1) (,t ,a2) (i32 ,a3)) ,locals ,gamma ,phi)
                               ->
                               (((,t ,a3)) ,locals (,gamma (,t ,a3)) (,phi (if (= ,a3 (i32 0)) (= ,a3 ,a1) (= ,a3 ,a2))))))
                          "Select"
                          empty)
              pre)))]

        [`(block ((,tis-pre ,locals-pre ,phi-pre) -> (,tis-post ,locals-post ,phi-post)) ,b-ins)
         (let ([tis (take-right tis (length tis-pre))])
           (if (and (term (tfi-ok ((,tis-pre ,locals-pre ,phi-pre) -> (,tis-post ,locals-post ,phi-post))))
                    (term (satisfies ,gamma ,phi (substitute-ivars
                                                  ,@(ivar-pairs (append tis locals)
                                                                (append tis-pre locals-pre))
                                                  ,phi-pre))))
               (match (typecheck-ins (term (add-label ,C (,tis-post ,locals-post ,phi-post)))
                                     b-ins
                                     (term (,tis-pre ,locals-pre (build-gamma ,(append tis-pre locals-pre)) ,phi-pre))
                                     (first (derivation-subs plain-deriv)))
                 [#f #f]
                 [b-ins-deriv
                  (match-let ([`(,d-tis ,d-locals ,d-gamma ,d-phi) (deriv-post b-ins-deriv)])
                    (if (term (satisfies ,d-gamma ,d-phi (substitute-ivars
                                                          ,@(ivar-pairs (append d-tis d-locals)
                                                                        (append tis-post locals-post))
                                                          ,phi-post)))
                        (let ([f-tis (map (λ (ti) `(,(first ti) ,(gensym))) tis-post)]
                              [f-locals (map (λ (ti) `(,(first ti) ,(gensym))) locals-post)])
                          (stack-polyize
                           (derivation `(⊢ ,C ((block ((,tis-pre ,locals-pre ,phi-pre)
                                                       ->
                                                       (,tis-post ,locals-post ,phi-post)) ,b-ins))
                                           ((,tis ,locals ,gamma ,phi)
                                            ->
                                            (,f-tis
                                             ,f-locals
                                             ,(term (union ,gamma (build-gamma ,(append f-tis f-locals))))
                                             ,(term (union ,phi (substitute-ivars
                                                                 ,@(ivar-pairs (append tis locals f-tis f-locals)
                                                                               (append tis-pre locals-pre tis-post locals-post))
                                                                 ,phi-post))))))
                                       "Block"
                                       (list b-ins-deriv))
                           pre))
                        #f))])
               #f))]

        [`(loop ((,tis-pre ,locals-pre ,phi-pre) -> (,tis-post ,locals-post ,phi-post)) ,l-ins)
         (let ([tis (take-right tis (length tis-pre))])
           (if (and (term (tfi-ok ((,tis-pre ,locals-pre ,phi-pre) -> (,tis-post ,locals-post ,phi-post))))
                    (term (satisfies ,gamma ,phi (substitute-ivars
                                                  ,@(ivar-pairs (append tis locals)
                                                                (append tis-pre locals-pre))
                                                  ,phi-pre))))
               (match (typecheck-ins (term (add-label ,C (,tis-pre ,locals-pre ,phi-pre)))
                                     l-ins
                                     (term (,tis-pre ,locals-pre (build-gamma ,(append tis-pre locals-pre)) ,phi-pre))
                                     (first (derivation-subs plain-deriv)))
                 [#f #f]
                 [l-ins-deriv
                  (match-let ([`(,d-tis ,d-locals ,d-gamma ,d-phi) (deriv-post l-ins-deriv)])
                    (if (term (satisfies ,d-gamma ,d-phi (substitute-ivars
                                                          ,@(ivar-pairs (append d-tis d-locals)
                                                                        (append tis-post locals-post))
                                                          ,phi-post)))
                        (let ([f-tis (map (λ (ti) `(,(first ti) ,(gensym))) tis-post)]
                              [f-locals (map (λ (ti) `(,(first ti) ,(gensym))) locals-post)])
                          (stack-polyize
                           (derivation `(⊢ ,C ((loop ((,tis-pre ,locals-pre ,phi-pre)
                                                      ->
                                                      (,tis-post ,locals-post ,phi-post)) ,l-ins))
                                           ((,tis ,locals ,gamma ,phi)
                                            ->
                                            (,f-tis
                                             ,f-locals
                                             ,(term (union ,gamma (build-gamma ,(append f-tis f-locals))))
                                             ,(term (union ,phi (substitute-ivars
                                                                 ,@(ivar-pairs (append tis locals f-tis f-locals)
                                                                               (append tis-pre locals-pre tis-post locals-post))
                                                                 ,phi-post))))))
                                       "Loop"
                                       (list l-ins-deriv))
                           pre))
                        #f))])
               #f))]

        [`(if ((,tis-pre ,locals-pre ,phi-pre) -> (,tis-post ,locals-post ,phi-post)) ,then-ins else ,else-ins)
         (let ([tis (take-right tis (add1 (length tis-pre)))])
           (if (and (term (tfi-ok ((,tis-pre ,locals-pre ,phi-pre) -> (,tis-post ,locals-post ,phi-post))))
                    (term (satisfies ,gamma ,phi (substitute-ivars
                                                  ,@(ivar-pairs (drop-right (append tis locals) 1)
                                                                (append tis-pre locals-pre))
                                                  ,phi-pre))))
               (match (typecheck-ins (term (add-label ,C (,tis-pre ,locals-pre ,phi-pre)))
                                     then-ins
                                     (term (,tis-pre ,locals-pre (build-gamma ,(append tis-pre locals-pre)) ,phi-pre))
                                     (first (derivation-subs plain-deriv)))
                 [#f #f]
                 [then-ins-deriv
                  (match-let ([`(,t-tis ,t-locals ,t-gamma ,t-phi) (deriv-post then-ins-deriv)])
                    (if (term (satisfies ,t-gamma ,t-phi (substitute-ivars
                                                          ,@(ivar-pairs (append t-tis t-locals)
                                                                        (append tis-post locals-post))
                                                          ,phi-post)))
                        (match (typecheck-ins (term (add-label ,C (,tis-pre ,locals-pre ,phi-pre)))
                                              else-ins
                                              (term (,tis-pre ,locals-pre (build-gamma ,(append tis-pre locals-pre)) ,phi-pre))
                                              (second (derivation-subs plain-deriv)))
                          [#f #f]
                          [else-ins-deriv
                           (match-let ([`(,e-tis ,e-locals ,e-gamma ,e-phi) (deriv-post else-ins-deriv)])
                             (if (term (satisfies ,e-gamma ,e-phi (substitute-ivars
                                                                   ,@(ivar-pairs (append e-tis e-locals)
                                                                                 (append tis-post locals-post))
                                                                   ,phi-post)))
                                 (let ([f-tis (map (λ (ti) `(,(first ti) ,(gensym))) tis-post)]
                                       [f-locals (map (λ (ti) `(,(first ti) ,(gensym))) locals-post)])
                                   (stack-polyize
                                    (derivation `(⊢ ,C ((if ((,tis-pre ,locals-pre ,phi-pre)
                                                             ->
                                                             (,tis-post ,locals-post ,phi-post))
                                                            ,then-ins else ,else-ins))
                                                    ((,tis ,locals ,gamma ,phi)
                                                     ->
                                                     (,f-tis
                                                      ,f-locals
                                                      ,(term (union ,gamma (build-gamma ,(append f-tis f-locals))))
                                                      ,(term (union ,phi (substitute-ivars
                                                                          ,@(ivar-pairs (append tis locals f-tis f-locals)
                                                                                        (append tis-pre locals-pre tis-post locals-post))
                                                                          ,phi-post))))))
                                                "If"
                                                (list then-ins-deriv else-ins-deriv))
                                    pre))
                                 #f))])
                        #f))])
               #f))]

        [`(br ,j)
         (match-let* ([`(,l-tis ,l-locals ,l-phi) (term (context-label ,C ,j))]
                      [br-tis (take-right tis (length l-tis))])
           (if (term (satisfies ,gamma ,phi (substitute-ivars
                                             ,@(ivar-pairs (append br-tis locals)
                                                           (append l-tis l-locals))
                                             ,l-phi)))
               (let* ([post-tis (map (λ (t) `(,t ,(gensym))) (deriv-post plain-deriv))]
                      [post-gamma (term (build-gamma (merge ,post-tis ,locals)))])
                 (derivation `(⊢ ,C ((br ,j)) (,pre -> (,post-tis ,locals ,post-gamma (empty ⊥))))
                             "Br"
                             empty))
               #f))]

        [`(br-if ,j)
         (match-let* ([`(,l-tis ,l-locals ,l-phi) (term (context-label ,C ,j))]
                      [`(,br-tis ... (i32 ,ivar)) (take-right tis (add1 (length l-tis)))])
           (if (term (satisfies ,gamma (,phi (not (= ,ivar (i32 0))))
                                (substitute-ivars
                                 ,@(ivar-pairs (append br-tis locals)
                                               (append l-tis l-locals))
                                 ,l-phi)))
               (stack-polyize
                (derivation `(⊢ ,C ((br-if ,j))
                                (((,@br-tis (i32 ,ivar)) ,locals ,gamma ,phi)
                                 ->
                                 (,br-tis ,locals ,gamma (,phi (= ,ivar (i32 0))))))
                            "Br-If"
                            empty)
                pre)
               #f))]

        [`(br-table ,js ...)
         (match-let* ([`((,l-tis ,l-locals ,l-phi) ...) (map (λ (j) (term (context-label ,C ,j))) js)] 
                      [`(,br-tis ... (i32 ,ivar)) (take-right tis (add1 (length (first l-tis))))])
           (if (term (satisfies-all ,gamma ,phi ,(map (λ (ll-tis ll-locals ll-phi)
                                                        (term (substitute-ivars ,@(ivar-pairs (append br-tis locals)
                                                                                              (append ll-tis ll-locals))
                                                                                ,ll-phi))
                                                        l-tis l-locals l-phi))))
               (let* ([post-tis (map (λ (t) `(,t ,(gensym))) (deriv-post plain-deriv))]
                      [post-gamma (term (build-gamma (merge ,post-tis ,locals)))])
                 (derivation `(⊢ ,C ((br-table ,@js))
                                 (,pre -> (,post-tis ,locals ,post-gamma (empty ⊥))))
                             "Br-Table"
                             empty))
               #f))]
        
        [`return
         (match-let ([`(,ret-tis () ,ret-phi) (term (context-return ,C))])
           (let ([tis (take-right tis (length ret-tis))])
             (if (term (satisfies ,gamma ,phi (substitute-ivars ,@(ivar-pairs tis ret-tis) ,ret-phi)))
                 (let* ([post-tis (map (λ (t) `(,t ,(gensym))) (deriv-post plain-deriv))]
                        [post-gamma (term (build-gamma (merge ,post-tis ,locals)))])
                   (derivation `(⊢ ,C (return) (,pre -> (,post-tis ,locals ,post-gamma (empty ⊥)))) "Return" empty))
                 #f)))]

        [`(call ,j)
         (match-let ([`((,func-tis-pre () ,func-phi-pre) -> (,func-tis-post () ,func-phi-post)) (term (context-func ,C ,j))])
           (let ([tis (take-right tis (length func-tis-pre))])
             (if (term (satisfies ,gamma ,phi (substitute-ivars ,@(ivar-pairs tis func-tis-pre) ,func-phi-pre)))
                 (let* ([post-tis (map (λ (ti) `(,(first ti) ,(gensym))) func-tis-post)]
                        [post-gamma (term (union ,gamma (build-gamma ,post-tis)))])
                   (derivation `(⊢ ,C ((call ,j)) ((,tis ,locals ,gamma ,phi)
                                                   ->
                                                   (,post-tis
                                                    ,locals
                                                    ,post-gamma
                                                    ,(term (union ,phi (substitute-ivars
                                                                        ,@(ivar-pairs (append tis post-tis)
                                                                                      (append func-tis-pre func-tis-post))
                                                                        ,func-phi-post))))))
                               "Call"
                               empty))
                 #f)))]

        [`(call-indirect ((,ann-tis-pre () ,ann-phi-pre) -> (,ann-tis-post () ,ann-phi-post)))
         (let ([tis (take-right tis (add1 (length ann-tis-pre)))])
           (if (and (term (tfi-ok ((,ann-tis-pre () ,ann-phi-pre) -> (,ann-tis-post () ,ann-phi-post))))
                    (term (satisfies ,gamma ,phi (substitute-ivars ,@(ivar-pairs (drop-right tis 1) ann-tis-pre) ,ann-phi-pre))))
               (let* ([post-tis (map (λ (ti) `(,(first ti) ,(gensym))) ann-tis-post)]
                      [post-gamma (term (union ,gamma (build-gamma ,post-tis)))])
                 (derivation `(⊢ ,C ((call-indirect ((,ann-tis-pre () ,ann-phi-pre) -> (,ann-tis-post () ,ann-phi-post))))
                                 ((,tis ,locals ,gamma ,phi)
                                  ->
                                  (,post-tis
                                   ,locals
                                   ,post-gamma
                                   ,(term (union ,phi (substitute-ivars
                                                       ,@(ivar-pairs (append (drop-right tis 1) post-tis)
                                                                     (append ann-tis-pre ann-tis-post))
                                                       ,ann-phi-post))))))
                             "Call-Indirect"
                             empty))
               #f))]

        [`(call-indirect/unsafe ((,ann-tis-pre () ,ann-phi-pre) -> (,ann-tis-post () ,ann-phi-post)))
         (let ([tis (take-right tis (add1 (length ann-tis-pre)))]
               [tfis (drop (term (context-table ,C)) 1)])
           (if (and (term (tfi-ok ((,ann-tis-pre () ,ann-phi-pre) -> (,ann-tis-post () ,ann-phi-post))))
                    (term (satisfies ,gamma ,phi (substitute-ivars ,@(ivar-pairs (drop-right tis 1) ann-tis-pre) ,ann-phi-pre)))
                    (term (valid-table-call ((,ann-tis-pre () ,ann-phi-pre) -> (,ann-tis-post () ,ann-phi-post))
                                            ,(second (last tis)) ,tfis ,gamma ,phi)))
               (let* ([post-tis (map (λ (ti) `(,(first ti) ,(gensym))) ann-tis-post)]
                      [post-gamma (term (union ,gamma (build-gamma ,post-tis)))])
                 (derivation `(⊢ ,C ((call-indirect/unsafe ((,ann-tis-pre () ,ann-phi-pre) -> (,ann-tis-post () ,ann-phi-post))))
                                 ((,tis ,locals ,gamma ,phi)
                                  ->
                                  (,post-tis
                                   ,locals
                                   ,post-gamma
                                   ,(term (union ,phi (substitute-ivars
                                                       ,@(ivar-pairs (append (drop-right tis 1) post-tis)
                                                                     (append ann-tis-pre ann-tis-post))
                                                       ,ann-phi-post))))))
                             "Call-Indirect-Prechk"
                             empty))
               #f))]

        [`(get-local ,j)
         (let ([a (gensym)]
               [t (term (context-local ,C ,j))])
           (stack-polyize
            (derivation `(⊢ ,C ((get-local ,j))
                            ((() ,locals ,gamma ,phi)
                             ->
                             (((,t ,a)) ,locals (,gamma (,t ,a)) (,phi (= ,a ,(second (list-ref locals j)))))))
                        "Get-Local"
                        empty)
            pre))]

        [`(set-local ,j)
         (let ([ti (last tis)])
           (stack-polyize
            (derivation `(⊢ ,C ((set-local ,j))
                            (((,ti) ,locals ,gamma ,phi)
                             ->
                             (() ,(term (with-index ,locals ,j ,ti)) ,gamma ,phi)))
                        "Set-Local"
                        empty)
            pre))]

        [`(tee-local ,j)
         (let ([a (gensym)]
               [t (term (context-local ,C ,j))]
               [ti (last tis)])
           (stack-polyize
            (derivation `(⊢ ,C ((tee-local ,j))
                            (((,ti) ,locals ,gamma ,phi)
                             ->
                             (((,t ,a))
                              ,(term (with-index ,locals ,j ,ti))
                              (,gamma (,t ,a))
                              (,phi (= ,a ,(second ti))))))
                        "Tee-Local"
                        empty)
            pre))]

        [`(get-global ,j)
         (let ([a (gensym)]
               [t (term (context-global ,C ,j))])
           (stack-polyize
            (derivation `(⊢ ,C ((get-global ,j))
                            ((() ,locals ,gamma ,phi)
                             ->
                             (((,t ,a)) ,locals (,gamma (,t ,a)) ,phi)))
                        "Get-Global"
                        empty)
            pre))]

        [`(set-global ,j)
         (stack-polyize
          (derivation `(⊢ ,C ((set-global ,j))
                          (((,(last tis)) ,locals ,gamma ,phi)
                           ->
                           (() ,locals ,gamma ,phi)))
                      "Set-Global"
                      empty)
          pre)]

        [`(,t load/unsafe ,a ,o)
         (let ([n (term (context-memory ,C))]
               [ivar-a (second (last tis))])
           (if (term (satisfies ,gamma ,phi (empty (valid-address ,ivar-a ,o (bit-width ,t) ,n))))
               (let ([ivar (gensym)])
                 (stack-polyize
                  (derivation `(⊢ ,C ((,t load/unsafe ,a ,o))
                                  ((((i32 ,ivar-a)) ,locals ,gamma ,phi)
                                   ->
                                   (((,t ,ivar)) ,locals (,gamma (,t ,ivar)) ,phi)))
                              "Load-Prechk"
                              empty)
                  pre))
               #f))]

        [`(,t load/unsafe (,tp ,sx) ,a ,o)
         (let ([n (term (context-memory ,C))]
               [ivar-a (second (last tis))])
           (if (term (satisfies ,gamma ,phi (empty (valid-address ,ivar-a ,o (packed-bit-width ,tp) ,n))))
               (let ([ivar (gensym)])
                 (stack-polyize
                  (derivation `(⊢ ,C ((,t load/unsafe (,tp ,sx) ,a ,o))
                                  ((((i32 ,ivar-a)) ,locals ,gamma ,phi)
                                   ->
                                   (((,t ,ivar)) ,locals (,gamma (,t ,ivar)) ,phi)))
                              "Load-Packed-Prechk"
                              empty)
                  pre))
               #f))]

        [`(,t store/unsafe ,a ,o)
         (match-let ([n (term (context-memory ,C))]
                     [`(,_ ... (i32 ,ivar-a) (,_ ,ivar)) tis])
           (if (term (satisfies ,gamma ,phi (empty (valid-address ,ivar-a ,o (bit-width ,t) ,n))))
               (stack-polyize
                (derivation `(⊢ ,C ((,t store/unsafe ,a ,o))
                                ((((i32 ,ivar-a) (,t ,ivar)) ,locals ,gamma ,phi)
                                 ->
                                 (() ,locals ,gamma ,phi)))
                            "Store-Prechk"
                            empty)
                pre)
               #f))]

        [`(,t store/unsafe ,tp ,a ,o)
         (match-let ([n (term (context-memory ,C))]
                     [`(,_ ... (i32 ,ivar-a) (,_ ,ivar)) tis])
           (if (term (satisfies ,gamma ,phi (empty (valid-address ,ivar-a ,o (packed-bit-width ,tp) ,n))))
               (stack-polyize
                (derivation `(⊢ ,C ((,t store/unsafe ,tp ,a ,o))
                                ((((i32 ,ivar-a) (,t ,ivar)) ,locals ,gamma ,phi)
                                 ->
                                 (() ,locals ,gamma ,phi)))
                            "Store-Packed-Prechk"
                            empty)
                pre)
               #f))]

        [`(,t load ,a ,o)
         (let ([ivar (gensym)])
           (stack-polyize
            (derivation `(⊢ ,C ((,t load ,a ,o))
                            (((,(last tis)) ,locals ,gamma ,phi)
                             ->
                             (((,t ,ivar)) ,locals (,gamma (,t ,ivar)) ,phi)))
                        "Load"
                        empty)
            pre))]

        [`(,t load (,tp ,sx) ,a ,o)
         (let ([ivar (gensym)])
           (stack-polyize
            (derivation `(⊢ ,C ((,t load (,tp ,sx) ,a ,o))
                            (((,(last tis)) ,locals ,gamma ,phi)
                             ->
                             (((,t ,ivar)) ,locals (,gamma (,t ,ivar)) ,phi)))
                        "Load-Packed"
                        empty)
            pre))]

        [`(,t store ,a ,o)
         (stack-polyize
          (derivation `(⊢ ,C ((,t store ,a ,o))
                          ((,(take-right tis 2) ,locals ,gamma ,phi)
                           ->
                           (() ,locals ,gamma ,phi)))
                      "Store"
                      empty)
          pre)]

        [`(,t store ,tp ,a ,o)
         (let ([tis (take-right tis 2)])
           (stack-polyize
            (derivation `(⊢ ,C ((,t store ,tp ,a ,o))
                            ((,tis ,locals ,gamma ,phi)
                             ->
                             (() ,locals ,gamma ,phi)))
                        "Store-Packed"
                        empty)
            pre))]

        [`current-memory
         (let ([a (gensym)])
           (stack-polyize
            (derivation `(⊢ ,C (current-memory)
                            ((() ,locals ,gamma ,phi)
                             ->
                             (((i32 ,a)) ,locals (,gamma (i32 ,a)) ,phi)))
                        "Current-Memory"
                        empty)
            pre))]

        [`grow-memory
         (match-let ([`(,_ ... (i32 ,a1)) tis]
                     [a2 (gensym)])
           (stack-polyize
            (derivation `(⊢ ,C (grow-memory)
                            ((((i32 ,a1)) ,locals ,gamma ,phi)
                             ->
                             (((i32 ,a2)) ,locals (,gamma (i32 ,a2)) ,phi)))
                        "Grow-Memory"
                        empty)
            pre))]

        [_ #f])))
  
  (cond
    [(empty? ins) (derivation `(⊢ ,C () (,pre -> ,pre)) "Empty" empty)]
    [(empty? (rest ins)) (typecheck-e (first ins) pre plain-deriv)]
    [else
     ;; Note: this follows the recursive structure of the composition rule
     ;;       could make more efficient by flattening the derivation tree and folding over the instructions
     ;;       but this would have to detect when stack-polymorphism is used
     (match-let ([(derivation _ _ (list plain-es-deriv plain-e-deriv)) plain-deriv])
       (match (typecheck-ins C (drop-right ins 1) pre plain-es-deriv)
         [#f #f]
         [es-deriv (match (typecheck-e (last ins) (deriv-post es-deriv) plain-e-deriv)
                     [#f #f]
                     [e-deriv (derivation `(⊢ ,C ,ins (,pre -> ,(deriv-post e-deriv)))
                                          "Composition"
                                          (list es-deriv e-deriv))])]))]))

(define (deriv-post deriv)
  (match (derivation-term deriv)
    [`(⊢ ,_ ,_ (,_ -> ,post)) post]))

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

#;(typecheck-module
   '(module
        ((() (func ((((i32 a) (i32 b)) () empty)
                    ->
                    (((i32 c)) () (empty (= c ((i32 add) a b)))))
                   (local ()
                     ((get-local 0)
                      (get-local 1)
                      (i32 add)))))
         (() (func ((((i32 a)) () empty)
                    ->
                    (((i32 b)) () (empty (= b ((i32 mul) a (i32 2))))))
                   (local ()
                     ((get-local 0)
                      (get-local 0)
                      (call 0))))))
      () () ()))

#;(typecheck-module
   '(module
        ((() (func ((((i32 a) (i32 b) (i32 c)) () empty)
                    ->
                    (((i32 d) (i32 e)) () (empty (= d e))))
                   (local ()
                     ((get-local 0)
                      (get-local 1)
                      (i32 add)
                      (get-local 2)
                      (i32 add)
                      (get-local 0)
                      (get-local 1)
                      (get-local 2)
                      (i32 add)
                      (i32 add))))))
      () () ()))

#;(typecheck-module
   '(module
        ((() (func ((((i32 a)) () (empty (not (= a (i32 0)))))
                    ->
                    (((i32 b)) () (empty (= b (i32 0)))))
                   (local ()
                     ((loop ((() ((i32 a)) (empty (not (= a (i32 0)))))
                             ->
                             (() ((i32 b)) (empty (= b (i32 0)))))
                            ((get-local 0)
                             (i32 const 1)
                             (i32 sub)
                             (tee-local 0)
                             (br-if 0)))
                      (get-local 0))))))
      () () ()))