#lang racket

(require redex "IndexTypes.rkt" "Solver.rkt")

(provide test-satisfaction extract-constraints parse-index index-var->z3-const integer->z3-bitvec parse-defs)

(define debug #t)

(define (index-var->z3-const var)
  (match-let ([(cons name type) var])
    `(declare-const ,name ,(match type
                             ['i32 '(_ BitVec 32)]
                             ['i64 '(_ BitVec 64)]
                             ['f32 '(_ FloatingPoint 8 24)]
                             ['f64 '(_ FloatingPoint 11 53)]))))

(define (ask-z3 vars constraints1 constraints2)
  (when debug
    (displayln vars)
    (displayln constraints1)
    (displayln constraints2))
  
  (solve (append (map index-var->z3-const vars)
                 `((define-fun satisfies () Bool
                     (=>
                      (and ,@constraints1)
                      (and ,@constraints2)))
                   (assert (not satisfies))))))

(define (redex_unop->z3_op t op x)
  (match op
    ['clz     'TODO]
    ['ctz     'TODO]
    ['popcnt  'TODO]
    ['neg     `(fp.neg ,x)]
    ['abs     `(fp.abs ,x)]
    ['ceil    `(fp.roundToIntegral RTP ,x)]
    ['floor   `(fp.roundToIntegral RTN ,x)]
    ['trunc   `(fp.roundToIntegral RTZ ,x)]
    ['nearest `(fp.roundToIntegral RNE ,x)]
    ['sqrt    `(fp.sqrt RNE ,x)]))

(define (redex_binop->z3_op t op x y)
  (match op
    ['add      (match t
                 [(or 'i32 'i64) `(bvadd ,x ,y)]
                 [(or 'f32 'f64) `(fp.add RNE ,x ,y)])]
    ['sub      (match t
                 [(or 'i32 'i64) `(bvsub ,x ,y)]
                 [(or 'f32 'f64) `(fp.sub RNE ,x ,y)])]
    ['mul      (match t
                 [(or 'i32 'i64) `(bvmul ,x ,y)]
                 [(or 'f32 'f64) `(fp.mul RNE ,x ,y)])]
    ['div-s    `(bvsdiv ,x ,y)]
    ['rem-s    `(bvsrem ,x ,y)]
    ['div-u    `(bvudiv ,x ,y)]
    ['rem-u    `(bvurem ,x ,y)]
    ['and      `(bvand ,x ,y)]
    ['or       `(bvor ,x ,y)]
    ['xor      `(bvxor ,x ,y)]
    ['shl      `(bvshl ,x ,y)]
    ['shr-s    `(bvashr ,x ,y)]
    ['shr-u    `(bvlshr ,x ,y)]
    ['rotl     `(ext_rotate_left ,x ,y)]
    ['rotr     `(ext_rotate_right ,x ,y)]
    ['div      `(fp.div RNE ,x ,y)]
    ['min      `(fp.min ,x ,y)]
    ['max      `(fp.max ,x ,y)]
    ['copysign `(ite (fp.isPositive ,y) (fp.abs ,x) (fp.neg (fp.abs ,x)))]))

(define (redex_testop->z3_op t op x)
  (match op
    ['eqz (match t
            [`i32 `(ite (= ,x \#x00000000)
                        \#x00000001
                        \#x00000000)]
            [`i64 `(ite (= ,x \#x0000000000000000)
                        \#x0000000000000001
                        \#x0000000000000000)])]))

(define (redex_relop->z3_op t op x y)
  (match op
    ['eq   (match t
             [(or 'i32 'i64) `(= ,x ,y)]
             [(or 'f32 'f64) `(fp.eq ,x ,y)])]
    ['ne   (match t
             [(or 'i32 'i64) `(not (= ,x ,y))]
             [(or 'f32 'f64) `(not (fp.eq ,x ,y))])]
    ['lt-s `(bvslt ,x ,y)]
    ['gt-s `(bvsgt ,x ,y)]
    ['le-s `(bvsle ,x ,y)]
    ['ge-s `(bvsge ,x ,y)]
    ['lt-u `(bvult ,x ,y)]
    ['gt-u `(bvugt ,x ,y)]
    ['le-u `(bvule ,x ,y)]
    ['ge-u `(bvuge ,x ,y)]
    ['lt   `(fp.lt ,x ,y)]
    ['gt   `(fp.gt ,x ,y)]
    ['le   `(fp.leq ,x ,y)]
    ['ge   `(fp.geq ,x ,y)]))

(define (integer->z3-bitvec x n)
  (string->symbol
   (string-append*
    "#x"
    (map (λ (b) (if (< b 16)
                    (format "0~x" b)
                    (format "~x" b)))
         (bytes->list (integer->integer-bytes x (/ n 8) #f #t))))))

(define (byte-bits b start stop)
  (if (> start stop)
      ""
      (string-append (byte-bits b start (sub1 stop))
                     (if (zero? (bitwise-and b (expt 2 (- 8 (add1 stop)))))
                         "0"
                         "1"))))

(define (bytes->z3-bitvec bytes start stop)
  (string->symbol
   (string-append*
    "#b"
    (map (λ (b n)
           (cond
             [(<= start (* 8 n) (* 8 (add1 n)) stop) (byte-bits b 0 7)]
             [(<= (* 8 n) start (* 8 (add1 n)) stop) (byte-bits b (- start (* 8 n)) 7)]
             [(<= start (* 8 n) stop (* 8 (add1 n))) (byte-bits b 0 (- stop (* 8 n)))]
             [(<= (* 8 n) start stop (* 8 (add1 n))) (byte-bits b (- start (* 8 n)) (- stop (* 8 n)))]
             [else ""]))
         (bytes->list bytes)
         (build-list (bytes-length bytes) values)))))

(define (parse-index x)
  (match x
    [(? symbol?) x]
    
    [`(,type ,n)
     #:when (and (redex-match? WASMIndexTypes t type)
                 (number? n))
     (match type
       ['i32 (integer->z3-bitvec n 32)]
       ['i64 (integer->z3-bitvec n 64)]
       ['f32 (let ([n-bytes (real->floating-point-bytes n 4 #t)])
               `(fp ,(bytes->z3-bitvec n-bytes 0 0)
                    ,(bytes->z3-bitvec n-bytes 1 8)
                    ,(bytes->z3-bitvec n-bytes 9 31)))]
       ['f64 (let ([n-bytes (real->floating-point-bytes n 4 #t)])
               `(fp ,(bytes->z3-bitvec n-bytes 0 0)
                    ,(bytes->z3-bitvec n-bytes 1 11)
                    ,(bytes->z3-bitvec n-bytes 12 63)))])]
    
    [`((,t ,u_op) ,x)
     #:when (redex-match? WASMIndexTypes unop u_op)
     (redex_unop->z3_op t u_op (parse-index x))]
    
    [`((,t ,b_op) ,x ,y)
     #:when (redex-match? WASMIndexTypes binop b_op)
     (redex_binop->z3_op t b_op (parse-index x) (parse-index y))]
    
    [`((,t ,t_op) ,x)
     #:when (redex-match? WASMIndexTypes testop t_op)
     (redex_testop->z3_op t t_op (parse-index x))]
    
    [`((,t ,r_op) ,x ,y)
     #:when (redex-match? WASMIndexTypes relop r_op)
     `(ite ,(redex_relop->z3_op t r_op (parse-index x) (parse-index y))
           \#x00000001
           \#x00000000)]
    
    [`((,to convert ,from) ,x)
     (let ([index (parse-index x)])
       (match (list from to)
         ['(i64 i32) `((_ extract 31 0) ,index)]
         ['(f32 f64) `((_ to_fp 11 53) RNE ,index)]
         ['(f64 f32) `((_ to_fp 8 24) RNE ,index)]))]
    
    [`((,to convert ,from ,sx) ,x)
     (let ([index (parse-index x)])
       (match (list from to sx)
         ['(i32 i64 signed)   `((_ sign_extend 32) ,index)]
         ['(i32 i64 unsigned) `((_ zero_extend 32) ,index)]
         ['(i32 f32 signed)   `((_ to_fp 8 24) RNE ,index)]
         ['(i32 f32 unsigned) `((_ to_fp_unsigned 8 24) RNE ,index)]
         ['(i32 f64 signed)   `((_ to_fp 11 53) RNE ,index)]
         ['(i32 f64 unsigned) `((_ to_fp_unsigned 11 53) RNE ,index)]
         ['(i64 f32 signed)   `((_ to_fp 8 24) RNE ,index)]
         ['(i64 f32 unsigned) `((_ to_fp_unsigned 8 24) RNE ,index)]
         ['(i64 f64 signed)   `((_ to_fp 11 53) RNE ,index)]
         ['(i64 f64 unsigned) `((_ to_fp_unsigned 11 53) RNE ,index)]
         ['(f32 i32 signed)   `((_ fp.to_sbv 32) RTZ ,index)]
         ['(f32 i32 unsigned) `((_ fp.to_ubv 32) RTZ ,index)]
         ['(f32 i64 signed)   `((_ fp.to_sbv 64) RTZ ,index)]
         ['(f32 i64 unsigned) `((_ fp.to_ubv 64) RTZ ,index)]
         ['(f64 i32 signed)   `((_ fp.to_sbv 32) RTZ ,index)]
         ['(f64 i32 unsigned) `((_ fp.to_ubv 32) RTZ ,index)]
         ['(f64 i64 signed)   `((_ fp.to_sbv 64) RTZ ,index)]
         ['(f64 i64 unsigned) `((_ fp.to_ubv 64) RTZ ,index)]))]
    
    [`((,to reinterpret ,from) ,x)
     (let ([index (parse-index x)])
       (match (list from to)
         ['(i32 f32) `((_ to_fp 8 24) ,index)]
         ['(i64 f64) `((_ to_fp 11 53) ,index)]
         ['(f32 i32) 'TODO]
         ['(f64 i64) 'TODO]))]))

(define (parse-proposition P)
  (match P
    [`(= ,x ,y)
     (let ([index1 (parse-index x)]
           [index2 (parse-index y)])
       `(= ,index1 ,index2))]
    [`(not ,P*)
     (let ([prop (parse-proposition P*)])
       `(not ,prop))]
    [`(and ,P1 ,P2)
     (let ([prop1 (parse-proposition P1)]
           [prop2 (parse-proposition P2)])
       `(and ,prop1 ,prop2))]
    [`(or ,P1 ,P2)
     (let ([prop1 (parse-proposition P1)]
           [prop2 (parse-proposition P2)])
       `(or ,prop1 ,prop2))]
    [`(if ,P? ,P1 ,P2)
     (let ([cond (parse-proposition P?)]
           [true (parse-proposition P1)]
           [false (parse-proposition P2)])
       `(ite ,cond ,true ,false))]
    [`(valid-address ,index ,offset ,width ,n)
     `(and (bvule (bvadd (bvadd (_ bv33 ,offset)
                                ((_ zero_extend 1) ,index))
                         (bvlshr (_ bv33 ,width) (_ bv33 3)))
                  (_ bv33 ,n))
           (or (bvugt (_ bv32 ,offset) (_ bv32 0))
               (bvugt ,index (_ bv32 0))))]
    [`⊥
     `false]))

(define (parse-defs gamma)
  (match gamma
    [`empty null]
    [`(,gamma* (,t ,ivar)) (cons (cons ivar t) (parse-defs gamma*))]))

(define (extract-constraints phi)
  (match phi
    [`empty null]
    [`(,phi* ,P) (cons (parse-proposition P) (extract-constraints phi*))]))

(define (context-to-constraints gamma phi_1 phi_2)
  (let* ([vars (parse-defs gamma)]
         [consts1 (extract-constraints phi_1)]
         [consts2 (extract-constraints phi_2)])
    (values vars consts1 consts2)))

(define (test-satisfaction gamma phi_1 phi_2)
  (let-values ([(vars constraints1 constraints2) (context-to-constraints gamma phi_1 phi_2)])
    (or (null? constraints2)
        (and (not (null? constraints1))
             (not (ask-z3 vars constraints1 constraints2))))))