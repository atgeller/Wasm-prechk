#lang racket

(require "stack.rkt")

;; program state: ((stack ...) (locals ...) gamma phi)
#|
(define (get-stack state)
  (match state
    [`(,stack ,locals ,gamma ,phi) stack]))

(define (get-locals state)
  (match state
    [`(,stack ,locals ,gamma ,phi) locals]))

(define (get-gamma state)
  (match state
    [`(,stack ,locals ,gamma ,phi) gamma]))

(define (get-phi state)
  (match state
    [`(,stack ,locals ,gamma ,phi) phi]))

(define (pop-stack1 stack [t #f])
  (match stack
    [(cons `(,t1 ,ivar) stack*)
     #:when (or (not t) (eq? t t1))
     (values stack* (t1 ivar))]
    ['(⊥) (let ([ivar (gensym)]) (values '(⊥) (if t `(,t ,gensym) `(i32 ,gensym))))]
    [_ #f]))

(define (pop-stack2 stack [t #f])
  (pop-stackn stack 2 (option-map t (list t t))))

(define (pop-stackn stack n [t_n #f])
  (if (= n 0)
      (values (get-stack stack) '())
      (let*-values ([(rest first) (pop-stack1 stack (option-map t_n (car t_n)))]
                    [(remaining popped) (pop-stackn rest (- n 1) (option-map t_n (cdr t_n)))])
        (values remaining (cons first popped)))))

#;(define (push-stackn stack tis)
  (append tis stack))

#;(define (push-stack1 stack ti)
  (cons ti stack))

(define (add-to-state state adds)
  (match `(,state ,adds)
    [`((,stack ,locals ,gamma ,phi) `(,stack-adds ,local-mods ,gamma-adds ,phi-adds))
     (let ([modified-locals (for/list ([i (in-range (length locals))])
                              (dict-ref local-mods i (list-ref locals i)))])
       `(,(append stack stack-adds) ,modified-locals ,(append gamma gamma-adds) ,(append phi phi-adds)))]))
|#

;; TODO: Refactor
(define (type? type)
  (match type
    ['i32 #t]
    ['i64 #t]
    ['f32 #t]
    ['f64 #t]
    [(? symbol?) (unification-type? type)]
    [_ #f]))

(define-syntax option-map
  (syntax-rules ()
    [(option-map pred result) (if pred result #f)]))

(define-syntax option-match
  (syntax-rules ()
    [(option-match pats ...) (match pats ... [#f #f])]))

(define (typecheck-instructions C instructions pre)
  (foldr (lambda (instruction intermediate_state)
           (let ([post_state (typecheck-e C instruction (cdr intermediate_state))])
             (unless post_state
               (error "Could not typecheck instruction ~a" instruction))
             post_state))
         instructions
         pre))

(define (typecheck-e e pre plain-deriv)
  (match-let ([`(,tis ,locals ,gamma ,phi) pre])
    (match e
      [`(,t const ,c)
       (let ([a (gensym)])
         `((,@tis `(,t ,a)) ,locals (,gamma (,t ,a)) (,phi (= ,a (,t ,c)))))]

      ;; TODO
      #;[`(,t ,(? unop? uop))
         (match-let ([`(,tis_0 ... (,t ,a1)) tis])
           (let ([a (gensym)])
             `((,@tis_0 `(,t ,a)) ,locals (,gamma (,t ,a)) (,phi (= ,a ((,t ,uop) ,a1))))))]

      ;; TODO
      #;[`(,t div-s/unsafe)
         (match-let ([`(,tis_0 ... (,t ,a1) (,t ,a2)) tis])
           (option-map (satisfies ,gamma ,phi (empty (not (= ,a2 (,t 0)))))
                       (let ([a (gensym)])
                         `((,@tis_0 `(,t ,a)) ,locals (,gamma (,t ,a)) (,phi (= ,a ((,t div-s) ,a1 ,a2)))))))]

      ;; TODO
      #;[`(,t div-u/unsafe)
         (match-let ([`(,tis_0 ... (,t ,a1) (,t ,a2)) tis])
           (option-map (term (satisfies ,gamma ,phi (empty (not (= ,a2 (,t 0))))))
                       (let ([a (gensym)])
                         `((,@tis_0 `(,t ,a)) ,locals (,gamma (,t ,a)) (,phi (= ,a ((,t div-u) ,a1 ,a2)))))))]

      ;; TODO
      #;[`(,t rem-s/unsafe)
         (match-let ([`(,tis_0 ... (,t ,a1) (,t ,a2)) tis])
           (option-map (satisfies ,gamma ,phi (empty (not (= ,a2 (,t 0)))))
                       (let ([a (gensym)])
                         `((,@tis_0 `(,t ,a)) ,locals (,gamma (,t ,a)) (,phi (= ,a ((,t rem-s) ,a1 ,a2)))))))]

      ;; TODO
      #;[`(,t rem-u/unsafe)
         (match-let ([`(,tis_0 ... (,t ,a1) (,t ,a2)) tis])
           (option-map (satisfies ,gamma ,phi (empty (not (= ,a2 (,t 0)))))
                       (let ([a (gensym)])
                         `((,@tis_0 `(,t ,a)) ,locals (,gamma (,t ,a)) (,phi (= ,a ((,t rem-u) ,a1 ,a2)))))))]

      ;; TODO
      #;[`(,t ,(? binop? bop))
         (match-let ([`(,tis_0 ... (,t ,a1) (,t ,a2)) tis])
           (let ([a (gensym)])
             `((,@tis_0 `(,t ,a)) ,locals (,gamma (,t ,a)) (,phi (= ,a ((,t ,bop) ,a1 ,a2))))))]

      ;; TODO
      #;[`(,t ,(? testop? top))
         (match-let ([`(,tis_0 ... (,t ,a1) (,t ,a2)) tis])
           (let ([a (gensym)])
             `((,@tis_0 `(,t ,a)) ,locals (,gamma (,t ,a)) (,phi (= ,a ((,t ,top) ,a1 ,a2))))))]

      ;; TODO
      #; [`(,t ,(? relop? rop))
          (match-let ([`(,tis_0 ... (,t ,a1) (,t ,a2)) tis])
            (let ([a (gensym)])
              `((,@tis_0 `(,t ,a)) ,locals (,gamma (,t ,a)) (,phi (= ,a ((,t ,rop) ,a1 ,a2))))))]

      [`(,t1 convert ,t2)
       (match-let ([`(,tis_0 ... (,t_2 ,a2)) tis])
         (let ([a1 (gensym)])
           `((,@tis_0 (,t1 ,a1)) ,locals (,gamma (,t1 ,a1)) (,phi (= ,a1 ((,t1 convert ,t2) ,a2))))))]

      [`(,t1 convert ,t2 ,sx)
       (match-let ([`(,tis_0 ... (,_ ,a2)) tis])
         (let ([a1 (gensym)])
           `((,@tis_0 (,t1 ,a1)) ,locals (,gamma (,t1 ,a1)) (,phi (= ,a1 ((,t1 convert ,t2 ,sx) ,a2))))))]

      [`(,t1 reinterpret ,t2)
       (match-let ([`(,tis_0 ... (,t2 ,a2)) tis])
         (let ([a1 (gensym)])
           `((,@tis_0 (,t1 ,a1)) ,locals (,gamma (,t1 ,a1)) (,phi (= ,a1 ((,t1 reinterpret ,t2) ,a2))))))]

      ;; TODO
      #;[`unreachable
         (let* ([post-tis (map (λ (t) `(,t ,(gensym))) (deriv-post plain-deriv))]
                [post-gamma (term (build-gamma (merge ,post-tis ,locals)))])
           ` (⊥ ,locals ,post-gamma ⊥))]

      [`nop pre]

      [`drop
       (match-let ([`(,tis_0 ... ,ti_1) tis])
         `(,tis_0 ,locals ,gamma ,phi))]

      [`select
       (match-let ([`(,tis_0 ... (,t ,a1) (,t ,a2) (i32 ,a)) tis])
         (let ([a3 (gensym)])
           `((,tis_0 (,t ,a3)) ,locals (,gamma (,t ,a3)) (,phi (if (= ,a3 (i32 0)) (= ,a3 ,a1) (= ,a3 ,a2))))))]

      [`(block ((,tis-pre ,locals-pre ,phi-pre) -> (,tis-post ,locals-post ,phi-post)) ,b-ins)
       ;; TODO
       #;(let ([tis (take-right tis (length tis-pre))])
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
               #f))
       `()]

      [`(loop ((,tis-pre ,locals-pre ,phi-pre) -> (,tis-post ,locals-post ,phi-post)) ,l-ins)
       ;; TODO
       #;(let ([tis (take-right tis (length tis-pre))])
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
               #f))
       `()]

      [`(if ((,tis-pre ,locals-pre ,phi-pre) -> (,tis-post ,locals-post ,phi-post)) ,then-ins else ,else-ins)
       ;; TODO
       #;(let ([tis (take-right tis (add1 (length tis-pre)))])
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
               #f))
       `()]

      ;; TODO
      #;[`(br ,j)
         (match-let* ([`(,l-tis ,l-locals ,l-phi) (term (context-label ,C ,j))]
                      [br-tis (take-right tis (length l-tis))])
           (option-map (term (satisfies ,gamma ,phi (substitute-ivars
                                                     ,@(ivar-pairs (append br-tis locals)
                                                                   (append l-tis l-locals))
                                                     ,l-phi)))
                       (let* ([post-tis (map (λ (t) `(,t ,(gensym))) (deriv-post plain-deriv))]
                              [post-gamma (term (build-gamma (merge ,post-tis ,locals)))])
                         (,post-tis ,locals ,post-gamma (empty ⊥)))))]

      ;; TODO
      #;[`(br-if ,j)
         (match-let* ([`(,l-tis ,l-locals ,l-phi) (term (context-label ,C ,j))]
                      [`(,br-tis ... (i32 ,ivar)) (take-right tis (add1 (length l-tis)))]
                      [tis_0 (drop-right tis (add1 (length l-tis)))])
           (option-map (term (satisfies ,gamma (,phi (not (= ,ivar (i32 0))))
                                        (substitute-ivars
                                         ,@(ivar-pairs (append br-tis locals)
                                                       (append l-tis l-locals))
                                         ,l-phi)))
                       ((,@tis_0 ,@br-tis) ,locals ,gamma (,phi (= ,ivar (i32 0))))))]

      ;; TODO
      #;[`(br-table ,js ...)
         (match-let* ([`((,l-tis ,l-locals ,l-phi) ...) (map (λ (j) (term (context-label ,C ,j))) js)] 
                      [`(,br-tis ... (i32 ,ivar)) (take-right tis (add1 (length (first l-tis))))])
           (option-map (term (satisfies-all ,gamma ,phi ,(map (λ (ll-tis ll-locals ll-phi)
                                                                (term (substitute-ivars ,@(ivar-pairs (append br-tis locals)
                                                                                                      (append ll-tis ll-locals))
                                                                                        ,ll-phi))
                                                                l-tis l-locals l-phi))))
                       (let* ([post-tis (map (λ (t) `(,t ,(gensym))) (deriv-post plain-deriv))]
                              [post-gamma (term (build-gamma (merge ,post-tis ,locals)))])
                         (,post-tis ,locals ,post-gamma (empty ⊥)))))]
        
      ;; TODO
      #;[`return
         (match-let ([`(,ret-tis () ,ret-phi) (term (context-return ,C))])
           (let ([tis_1 (take-right tis (length ret-tis))])
             (option-map (term (satisfies ,gamma ,phi (substitute-ivars ,@(ivar-pairs tis ret-tis) ,ret-phi)))
                         (let* ([post-tis (map (λ (t) `(,t ,(gensym))) (deriv-post plain-deriv))]
                                [post-gamma (term (build-gamma (merge ,post-tis ,locals)))])
                           (,post-tis ,locals ,post-gamma (empty ⊥))))))]

      ;; TODO
      #;[`(call ,j)
         (match-let ([`((,func-tis-pre () ,func-phi-pre) -> (,func-tis-post () ,func-phi-post)) (term (context-func ,C ,j))])
           (let ([tis_1 (take-right tis (length func-tis-pre))]
                 [tis_0 (drop-right tis (length func-tis-pre))])
             (if (term (satisfies ,gamma ,phi (substitute-ivars ,@(ivar-pairs tis_1 func-tis-pre) ,func-phi-pre)))
                 (let* ([post-tis (map (λ (ti) `(,(first ti) ,(gensym))) func-tis-post)]
                        [post-gamma (term (union ,gamma (build-gamma ,post-tis)))])
                   ((,@tis_0 ,@post-tis) ,locals ,post-gamma ,(term (union ,phi (substitute-ivars
                                                                                 ,@(ivar-pairs (append tis post-tis)
                                                                                               (append func-tis-pre func-tis-post))
                                                                                 ,func-phi-post))))))))]

      ;; TODO
      #;[`(call-indirect ((,ann-tis-pre () ,ann-phi-pre) -> (,ann-tis-post () ,ann-phi-post)))
         (let ([`(,tis_1 ... (i32 ,_)) (take-right tis (add1 (length ann-tis-pre)))]
               [tis_0 (take-right tis (add1 (length ann-tis-pre)))])
           (option-map (and (term (tfi-ok ((,ann-tis-pre () ,ann-phi-pre) -> (,ann-tis-post () ,ann-phi-post))))
                            (term (satisfies ,gamma ,phi (substitute-ivars ,@(ivar-pairs tis_1 ann-tis-pre) ,ann-phi-pre))))
                       (let* ([post-tis (map (λ (ti) `(,(first ti) ,(gensym))) ann-tis-post)]
                              [post-gamma (term (union ,gamma (build-gamma ,post-tis)))])
                         ((,@tis_0 ,@post-tis)
                          ,locals
                          ,post-gamma
                          ,(term (union ,phi (substitute-ivars
                                              ,@(ivar-pairs (append (drop-right tis 1) post-tis)
                                                            (append ann-tis-pre ann-tis-post))
                                              ,ann-phi-post)))))))]

      ;; TODO
      #;[`(call-indirect/unsafe ((,ann-tis-pre () ,ann-phi-pre) -> (,ann-tis-post () ,ann-phi-post)))
         (let ([`(,tis_1 ... (i32 ,_)) (take-right tis (add1 (length ann-tis-pre)))]
               [tfis (drop (term (context-table ,C)) 1)])
           (option-map (and (term (tfi-ok ((,ann-tis-pre () ,ann-phi-pre) -> (,ann-tis-post () ,ann-phi-post))))
                            (term (satisfies ,gamma ,phi (substitute-ivars ,@(ivar-pairs tis_1 ann-tis-pre) ,ann-phi-pre)))
                            (term (valid-table-call ((,ann-tis-pre () ,ann-phi-pre) -> (,ann-tis-post () ,ann-phi-post))
                                                    ,(second (last tis)) ,tfis ,gamma ,phi)))
                       (let* ([post-tis (map (λ (ti) `(,(first ti) ,(gensym))) ann-tis-post)]
                              [post-gamma (term (union ,gamma (build-gamma ,post-tis)))])
                         ((,@tis_0 ,@post-tis)
                          ,locals
                          ,post-gamma
                          ,(term (union ,phi (substitute-ivars
                                              ,@(ivar-pairs (append (drop-right tis 1) post-tis)
                                                            (append ann-tis-pre ann-tis-post))
                                              ,ann-phi-post)))))))]

      ;; TODO
      #;[`(get-local ,j)
         (let ([a (gensym)]
               [t (term (context-local ,C ,j))])
           ((,tis (,t ,a)) ,locals (,gamma (,t ,a)) (,phi (= ,a ,(second (list-ref locals j))))))]


      ;; TODO
      #;[`(set-local ,j)(let ([ti (last tis)])
                          (stack-polyize
                           (derivation `(⊢ ,C ((set-local ,j))
                                           (((,ti) ,locals ,gamma ,phi)
                                            ->
                                            (() ,(term (with-index ,locals ,j ,ti)) ,gamma ,phi)))
                                       "Set-Local"
                                       empty)
                           pre))]

      ;; TODO
      #;[`(tee-local ,j)
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

      ;; TODO
      #;[`(get-global ,j)
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

      ;; TODO
      #;[`(set-global ,j)
         (stack-polyize
          (derivation `(⊢ ,C ((set-global ,j))
                          (((,(last tis)) ,locals ,gamma ,phi)
                           ->
                           (() ,locals ,gamma ,phi)))
                      "Set-Global"
                      empty)
          pre)]

      ;; TODO
      #;[`(,t load/unsafe ,a ,o)
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

      ;; TODO
      #;[`(,t load/unsafe (,tp ,sx) ,a ,o)
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

      ;; TODO
      #;[`(,t store/unsafe ,a ,o)
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

      ;; TODO
      #;[`(,t store/unsafe ,tp ,a ,o)
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

      ;; TODO
      #;[`(,t load ,a ,o)
         (let ([ivar (gensym)])
           (stack-polyize
            (derivation `(⊢ ,C ((,t load ,a ,o))
                            (((,(last tis)) ,locals ,gamma ,phi)
                             ->
                             (((,t ,ivar)) ,locals (,gamma (,t ,ivar)) ,phi)))
                        "Load"
                        empty)
            pre))]

      ;; TODO
      #;[`(,t load (,tp ,sx) ,a ,o)
         (let ([ivar (gensym)])
           (stack-polyize
            (derivation `(⊢ ,C ((,t load (,tp ,sx) ,a ,o))
                            (((,(last tis)) ,locals ,gamma ,phi)
                             ->
                             (((,t ,ivar)) ,locals (,gamma (,t ,ivar)) ,phi)))
                        "Load-Packed"
                        empty)
            pre))]

      ;; TODO
      #;[`(,t store ,a ,o)
         (stack-polyize
          (derivation `(⊢ ,C ((,t store ,a ,o))
                          ((,(take-right tis 2) ,locals ,gamma ,phi)
                           ->
                           (() ,locals ,gamma ,phi)))
                      "Store"
                      empty)
          pre)]

      ;; TODO
      #;[`(,t store ,tp ,a ,o)
         (let ([tis (take-right tis 2)])
           (stack-polyize
            (derivation `(⊢ ,C ((,t store ,tp ,a ,o))
                            ((,tis ,locals ,gamma ,phi)
                             ->
                             (() ,locals ,gamma ,phi)))
                        "Store-Packed"
                        empty)
            pre))]

      ;; TODO
      #;[`current-memory
         (let ([a (gensym)])
           (stack-polyize
            (derivation `(⊢ ,C (current-memory)
                            ((() ,locals ,gamma ,phi)
                             ->
                             (((i32 ,a)) ,locals (,gamma (i32 ,a)) ,phi)))
                        "Current-Memory"
                        empty)
            pre))]

      ;; TODO
      #;[`grow-memory
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

#;(define (typecheck-ins C ins pre plain-deriv)
  
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