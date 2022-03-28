#lang racket

(require (for-syntax racket))

(define empty-stack
  (lambda ([expected 't])
    (error "Cannot pop from empty stack")))

(define (any-stack [expected 't])
  (cons
   (match expected
     ['t 'i32]
     [_ expected])
   any-stack))

(define (push-stack stack index_type)
  (lambda ([expected 't])
    (match expected
      [(? unification-type?) (cons index_type stack)]
      [_ #:when (eq? expected (car index_type)) (cons index_type stack)]
      [else #f])))

(define (list->stack list)
  '())

#;(define (pop-stack1 stack [expected 't])
    (match (stack expected)
      [(cons type stack) (cons type stack)]))

(define (unification-type? type)
    (or (equal? type 't) (string-prefix? (symbol->string type) "t_")))

(begin-for-syntax
  (define (unification-type-stx? type)
    (or (equal? type 't) (string-prefix? (symbol->string type) "t_"))))

(define stack empty-stack)
(define stack1 (push-stack stack '(i32 a_1)))
(define stack2 (push-stack stack1 '(i32 a_2)))
(define stack3 (push-stack stack2 '(i32 a_3)))

;; Example usage:
;(let-stack stack3 [(i32 a_3) (t_1 a_2) (t_2 a_1) rest] body)

(define (env-from-stack stack pattern)
  (for/fold ([matches (make-immutable-hash)]
             [rest stack])
            ([object (syntax->list pattern)]
             #:break (not (syntax->list object)))
    (match (syntax->datum object)
      [`(,expected-type ,index-var)
       (let* ([unified-type
               (if (unification-type? expected-type)
                   (dict-ref matches expected-type expected-type)
                   expected-type)]
              [stack-popped (rest unified-type)]
              [stack-top (car stack-popped)]
              [type-stack (car stack-top)]
              [index-var-stack (cadr stack-top)]
              [stack-rest (cdr stack-popped)]
              [matches* (dict-set matches index-var index-var-stack)]
              [matches** (if (unification-type? unified-type)
                             (dict-set matches* expected-type type-stack)
                             matches*)])
         (values matches** stack-rest))])))

(require racket/trace)
(trace-define-syntax
 (let-stack stx)
 (syntax-case stx ()
   [(let-stack stack pattern body)
    #`(let-values ([(env rest) (env-from-stack stack #'pattern)])
        (let* #,(for/fold ([acc '()]
                           [seen '()]
                           #:result acc)
                          ([object (syntax->list #'pattern)])
                  (match (syntax->datum object)
                    [`(,type ,index-var)
                     (let* ([env-type (if (unification-type-stx? type)
                                          (list type #`(dict-ref env '#,type))
                                          #f)]
                            [env-index-var (list index-var #`(dict-ref env '#,index-var))]
                            [acc* (if (and env-type (not (member type seen))) (cons env-type acc) acc)]
                            [acc** (cons env-index-var acc*)]
                            [seen* (cons type (cons index-var seen))])
                       (if (member index-var seen)
                           (error "Multiply passed index-var to let-stack ~a" index-var)
                           (values acc** seen*)))]
                    [(? symbol? rest-id) (values (cons (list rest-id #'rest) acc) seen)]))
          body))]))

(let-stack stack3 [(i32 a_3) (t a_2) (t a_1) rest] (displayln t))