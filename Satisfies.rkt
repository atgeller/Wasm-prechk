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

(define (lookup-gamma gamma x)
  (match gamma
    [`empty (error "Gamma lookup failed")]
    [`(,gamma* (,t ,y))
     (if (equal? x y)
         t
         (lookup-gamma gamma* x))]))

(define (redex_op->z3_op gamma expr)
  (match expr
    [`(clz ,x)            'TODO]
    [`(ctz ,x)            'TODO]
    [`(popcnt ,x)         'TODO]
    [`(neg ,x)            `(fp.neg ,x)]
    [`(abs ,x)            `(fp.abs ,x)]
    [`(ceil ,x)           `(fp.roundToIntegral RTP ,x)]
    [`(floor ,x)          `(fp.roundToIntegral RTN ,x)]
    [`(trunc ,x)          `(fp.roundToIntegral RTZ ,x)]
    [`(nearest ,x)        `(fp.roundToIntegral RNE ,x)]
    [`(sqrt ,x)           `(fp.sqrt RNE ,x)]
    [`(add ,x ,y)         (match (lookup-gamma x)
                            [(or 'i32 'i64) `(bvadd ,x ,y)]
                            [(or 'f32 'f64) `(fp.add RNE ,x ,y)])]
    [`(sub ,x ,y)         (match (lookup-gamma x)
                            [(or 'i32 'i64) `(bvsub ,x ,y)]
                            [(or 'f32 'f64) `(fp.sub RNE ,x ,y)])]
    [`(mul ,x ,y)         (match (lookup-gamma x)
                            [(or 'i32 'i64) `(bvmul ,x ,y)]
                            [(or 'f32 'f64) `(fp.mul RNE ,x ,y)])]
    [`(div-s ,x ,y)       `(bvsdiv ,x ,y)]
    [`(rem-s ,x ,y)       `(bvsrem ,x ,y)]
    [`(div-u ,x ,y)       `(bvudiv ,x ,y)]
    [`(rem-u ,x ,y)       `(bvurem ,x ,y)]
    [`(and ,x ,y)         `(bvand ,x ,y)]
    [`(or ,x ,y)          `(bvor ,x ,y)]
    [`(xor ,x ,y)         `(bvxor ,x ,y)]
    [`(shl ,x ,y)         `(bvshl ,x ,y)]
    [`(shr-s ,x ,y)       `(bvashr ,x ,y)]
    [`(shr-u ,x ,y)       `(bvlshr ,x ,y)]
    [`(rotl ,x ,y)        `(ext_rotate_left ,x ,y)]
    [`(rotr ,x ,y)        `(ext_rotate_right ,x ,y)]
    [`(div ,x ,y)         `(fp.div RNE ,x ,y)]
    [`(min ,x ,y)         `(fp.min ,x ,y)]
    [`(max ,x ,y)         `(fp.max ,x ,y)]
    [`(copysign ,x ,y)    `(ite (fp.isPositive ,y) (fp.abs ,x) (fp.neg (fp.abs ,x)))]
    [`(eqz ,x)            (match (lookup-gamma x)
                            [`i32 `(= ,x \#x00000000)]
                            [`i64 `(= ,x \#x0000000000000000)])]
    [`(eq ,x ,y)          (match (lookup-gamma x)
                            [(or 'i32 'i64) `(= ,x ,y)]
                            [(or 'f32 'f64) `(fp.eq ,x ,y)])]
    [`(ne ,x ,y)          (match (lookup-gamma x)
                            [(or 'i32 'i64) `(not (= ,x ,y))]
                            [(or 'f32 'f64) `(not (fp.eq ,x ,y))])]
    [`(lt-s ,x ,y)        `(bvslt ,x ,y)]
    [`(gt-s ,x ,y)        `(bvsgt ,x ,y)]
    [`(le-s ,x ,y)        `(bvsle ,x ,y)]
    [`(ge-s ,x ,y)        `(bvsge ,x ,y)]
    [`(lt-u ,x ,y)        `(bvult ,x ,y)]
    [`(gt-u ,x ,y)        `(bvugt ,x ,y)]
    [`(le-u ,x ,y)        `(bvule ,x ,y)]
    [`(ge-u ,x ,y)        `(bvuge ,x ,y)]
    [`(lt ,x ,y)          `(fp.lt ,x ,y)]
    [`(gt ,x ,y)          `(fp.gt ,x ,y)]
    [`(le ,x ,y)          `(fp.leq ,x ,y)]
    [`(ge ,x ,y)          `(fp.geq ,x ,y)]
    [`(convert ,x ,t)     (match (list (lookup-gamma x) t)
                            ['(i64 i32) `((_ extract 31 0) ,x)]
                            ['(f32 f64) `((_ to_fp 11 53) RNE ,x)]
                            ['(f64 f32) `((_ to_fp 8 24) RNE ,x)])]
    [`(convert ,x ,t ,sx) (match (list (lookup-gamma x) t sx)
                            ['(i32 i64 signed)   `((_ sign_extend 32) ,x)]
                            ['(i32 i64 unsigned) `((_ zero_extend 32) ,x)]
                            ['(i32 f32 signed)   `((_ to_fp 8 24) RNE ,x)]
                            ['(i32 f32 unsigned) `((_ to_fp_unsigned 8 24) RNE ,x)]
                            ['(i32 f64 signed)   `((_ to_fp 11 53) RNE ,x)]
                            ['(i32 f64 unsigned) `((_ to_fp_unsigned 11 53) RNE ,x)]
                            ['(i64 f32 signed)   `((_ to_fp 8 24) RNE ,x)]
                            ['(i64 f32 unsigned) `((_ to_fp_unsigned 8 24) RNE ,x)]
                            ['(i64 f64 signed)   `((_ to_fp 11 53) RNE ,x)]
                            ['(i64 f64 unsigned) `((_ to_fp_unsigned 11 53) RNE ,x)]
                            ['(f32 i32 signed)   `((_ fp.to_sbv 32) RTZ ,x)]
                            ['(f32 i32 unsigned) `((_ fp.to_ubv 32) RTZ ,x)]
                            ['(f32 i64 signed)   `((_ fp.to_sbv 64) RTZ ,x)]
                            ['(f32 i64 unsigned) `((_ fp.to_ubv 64) RTZ ,x)]
                            ['(f64 i32 signed)   `((_ fp.to_sbv 32) RTZ ,x)]
                            ['(f64 i32 unsigned) `((_ fp.to_ubv 32) RTZ ,x)]
                            ['(f64 i64 signed)   `((_ fp.to_sbv 64) RTZ ,x)]
                            ['(f64 i64 unsigned) `((_ fp.to_ubv 64) RTZ ,x)])]
    [`(reinterpret ,x ,t) (match (list (lookup-gamma x) t)
                            ['(i32 f32) `((_ to_fp 8 24) ,x)]
                            ['(i64 f64) `((_ to_fp 11 53) ,x)]
                            ['(f32 i32) 'TODO]
                            ['(f64 i64) 'TODO])]))

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

(define (parse-index gamma x)
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
    [`(,u_op ,x)
     #:when (redex-match? WASMIndexTypes unop u_op)
     (let ([index (parse-index gamma x)])
       (redex_op->z3_op gamma `(,u_op ,index)))]
    [`(,b_op ,x ,y)
     #:when (redex-match? WASMIndexTypes binop b_op)
     (let ([index1 (parse-index gamma x)]
           [index2 (parse-index gamma y)])
       (redex_op->z3_op gamma `(,b_op ,index1 ,index2)))]
    [`(,t_op ,x)
     #:when (redex-match? WASMIndexTypes testop t_op)
     (let ([index (parse-index gamma x)])
       `(ite ,(redex_op->z3_op gamma `(,t_op ,index)) \#x00000001 \#x00000000))]
    [`(,r_op ,x ,y)
     #:when (redex-match? WASMIndexTypes relop r_op)
     (let ([index1 (parse-index gamma x)]
           [index2 (parse-index gamma y)])
       `(ite ,(redex_op->z3_op gamma `(,r_op ,index1 ,index2)) \#x00000001 \#x00000000))]))

(define (parse-proposition gamma P)
  (match P
    [`(= ,x ,y)
     (let ([index1 (parse-index gamma x)]
           [index2 (parse-index gamma y)])
       `(= ,index1 ,index2))]
    [`(not ,P*)
     (let ([prop (parse-proposition gamma P*)])
       `(not ,prop))]
    [`(and ,P1 ,P2)
     (let ([prop1 (parse-proposition gamma P1)]
           [prop2 (parse-proposition gamma P2)])
       `(and ,prop1 ,prop2))]
    [`(or ,P1 ,P2)
     (let ([prop1 (parse-proposition gamma P1)]
           [prop2 (parse-proposition gamma P2)])
       `(or ,prop1 ,prop2))]
    [`(if ,P? ,P1 ,P2)
     (let ([cond (parse-proposition gamma P?)]
           [true (parse-proposition gamma P1)]
           [false (parse-proposition gamma P2)])
       `(ite ,cond ,true ,false))]
    [`⊥
     `false]))

(define (parse-defs gamma)
  (match gamma
    [`empty null]
    [`(,gamma* (,t ,ivar)) (cons (cons ivar t) (parse-defs gamma*))]))

(define (extract-constraints gamma phi)
  (match phi
    [`empty null]
    [`(,phi* ,P) (cons (parse-proposition gamma P) (extract-constraints gamma phi*))]))

(define (context-to-constraints gamma phi_1 phi_2)
  (let* ([vars (parse-defs gamma)]
         [consts1 (extract-constraints gamma phi_1)]
         [consts2 (extract-constraints gamma phi_2)])
    (values vars consts1 consts2)))

(define (test-satisfaction gamma phi_1 phi_2)
  (let-values ([(vars constraints1 constraints2) (context-to-constraints gamma phi_1 phi_2)])
    (or (null? constraints2)
        (and (not (null? constraints1))
             (not (ask-z3 vars constraints1 constraints2))))))