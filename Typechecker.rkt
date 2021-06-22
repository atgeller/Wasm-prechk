#lang racket

(require redex/reduction-semantics
         "IndexTypes.rkt"
         "IndexTypingRules.rkt"
         "IndexModuleTyping.rkt"
         "Utilities.rkt"
         "Erasure.rkt"
         "SubTyping.rkt"
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
       (match (typecheck-ins C2 ins `(() ,(append tis-pre locals-pre) ,Γ-pre ,φ-pre) (first (derivation-subs plain-deriv)))
         [#f #f]
         [ins-deriv
          (match-let ([`(,tis-ins-post ,_ ,Γ-post ,φ-ins-post) (deriv-post ins-deriv)])
            (if (term (satisfies ,Γ-post ,φ-ins-post (substitute-ivars ,@(map (λ (ti-a ti-b) (list (second ti-a) (second ti-b)))
                                                                              tis-ins-post
                                                                              tis-post)
                                                                       ,φ-post)))
                (derivation `(⊢-module-func ,C ,f (,exs ((,tis-pre () ,φ-pre) -> (,tis-post () ,φ-post))))
                            #f
                            (list ins-deriv))
                #f))]))]))

(define (typecheck-global C glob plain-deriv)
  (match glob
    [`(,exs (global (,mut ,t) (import ,_ ,_)))
     (if (equal? mut 'const)
         (derivation `(⊢-module-global ,C ,glob (,exs (const ,t))) #f empty)
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
     (derivation `(⊢-module-table ,C ,tab (,exs (,i ,@tfis))) #f empty)]
    [`(,exs (table ,i ,js ...))
     (redex-let WASMIndexTypes ([((func (tfi ...)) _ _ _ _ _ _) C])
                (derivation `(⊢-module-table ,C ,tab (,exs (,i ,@(map (curry list-ref (term (tfi ...))) js))))
                            #f (list (first (build-derivations (valid-indices (tfi ...) ,js ,i))))))]))

(define (typecheck-memory C mem plain-deriv)
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

  (define (ivar-pairs tis-a tis-b)
    (map (λ (ti-a ti-b) (list (second ti-a) (second ti-b))) tis-a tis-b))
  
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
                                                      (,tis-post ,locals-pre ,phi-post)) ,l-ins))
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

        [`(if ((,tis-pre ,locals-pre ,phi-pre) -> (,tis-post ,locals-post ,phi-post)) ,then-ins ,else-ins)
         (let ([tis (take-right tis (length tis-pre))])
           (if (and (term (tfi-ok ((,tis-pre ,locals-pre ,phi-pre) -> (,tis-post ,locals-post ,phi-post))))
                    (term (satisfies ,gamma ,phi (substitute-ivars
                                                  ,@(ivar-pairs (append tis locals)
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
                                                            ,then-ins ,else-ins))
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
                                                                        ,@(ivar-pairs post-tis func-tis-post)
                                                                        ,func-phi-post))))))
                               "Call"
                               empty))
                 #f)))]

        [`(call-indirect ((,ann-tis-pre () ,ann-phi-pre) -> (,ann-tis-post () ,ann-phi-post)))
         (let ([tis (take-right tis (length ann-tis-pre))])
           (if (and (term (tfi-ok ((,ann-tis-pre () ,ann-phi-pre) -> (,ann-tis-post () ,ann-phi-post))))
                    (term (satisfies ,gamma ,phi (substitute-ivars ,@(ivar-pairs tis ann-tis-pre) ,ann-phi-pre))))
               (let* ([post-tis (map (λ (ti) `(,(first ti) ,(gensym))) ann-tis-post)]
                      [post-gamma (term (union ,gamma (build-gamma ,post-tis)))])
                 (derivation `(⊢ ,C ((call-indirect ((,ann-tis-pre () ,ann-phi-pre) -> (,ann-tis-post () ,ann-phi-post))))
                                 ((,tis ,locals ,gamma ,phi)
                                  ->
                                  (,post-tis
                                   ,locals
                                   ,post-gamma
                                   ,(term (union ,phi (substitute-ivars
                                                       ,@(ivar-pairs post-tis ann-tis-post)
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
                                                       ,@(ivar-pairs post-tis ann-tis-post)
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
         (let ([ti (last tis)])
           (stack-polyize
            (derivation `(⊢ ,C ((set-global ,j))
                            (((,ti) ,locals ,gamma ,phi)
                             ->
                             (() ,locals ,gamma ,phi)))
                            "Set-Global"
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
    [`() (derivation `(⊢-module-global-list () ()) #f empty)]
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
     (derivation `(⊢-module-global ,C ,glob (,exs (#f ,t))) #f empty)]))

;; C tab -> derivation of ⊢-module-table
;; Requires that the table has valid indices and length
#;(define (build-table-derivation C tab)
  (match tab
    [`(table ,exs ,i ,js)
     (redex-let WASMIndexTypes ([((func (tfi ...)) _ _ _ _ _ _) C])
       (derivation `(⊢-module-table ,C ,tab (,exs (,i ,(map (curry list-ref (term (tfi ...))) js))))
                   #f (list (first (build-derivations (valid-indices (tfi ...) ,js ,i))))))]
    [`(table ,exs ,i ,_ ,tfis)
     (derivation `(⊢-module-table ,C ,tab (,exs (,i ,tfis))) #f empty)]))

;; C mem -> derivation of ⊢-module-mem
#;(define (build-memory-derivation C mem)
  (match mem
    [`(memory ,exs ,i)
     (derivation `(⊢-module-mem ,C ,mem (,exs ,i)) #f empty)]
    [`(memory ,exs ,i ,im)
     (derivation `(⊢-module-mem ,C ,mem (,exs ,i)) #f empty)]))

;; C (listof func) -> derivation of ⊢-module-func-list or #f
#;(define (typecheck-funcs C funcs)
  (match funcs
    [`() (derivation `(⊢-module-func-list ,C () ()) #f empty)]
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
     (derivation `(⊢-module-func ,C ,func (,exs ,tfi)) #f empty)]))

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
                       "Const" empty)])
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
                                 "Nop" empty)])
          (if (empty? tis)
              deriv
              (derivation `(⊢ ,C ,es (,ticond -> ,ticond)) "Stack-Poly" (list deriv))))]

       [`(drop)
        (if (not (empty? tis))
            (let ([deriv (derivation `(⊢ ,C ,es (((,(last tis)) ,locals ,Γ ,φ) -> (() ,locals ,Γ ,φ)))
                                     "Drop" empty)])
              (if (= (length tis) 1)
                  deriv
                  (derivation `(⊢ ,C ,es (,ticond -> (,(drop-right tis 1) ,locals ,Γ ,φ)))
                              "Stack-Poly" (list deriv))))
            #f)]

       [`()
        (let ([deriv (derivation `(⊢ ,C () ((() ,locals ,Γ ,φ) -> (() ,locals ,Γ ,φ)))
                                 "Empty" empty)])
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

#;(typecheck-module
   '(module
        ((() (func ((((i32 a) (i32 b)) () empty)
                    ->
                    (((i32 c)) () (empty (= c (i32 1)))))
                   (local ()
                     ((i32 const 0)
                      (i32 const 1)
                      (i32 add))))))
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