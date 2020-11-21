#lang racket

(require racket/runtime-path racket/path)

(provide solve z3)

; We assume that the solver can be placed in the bin folder in this directory.
(define-runtime-path bin (build-path "bin"))

(define z3
  (let ([bin-name
         (if (eq? (system-type 'os) 'windows)
             "z3.exe"
             "z3")])
    (make-parameter (or (find-executable-path bin-name) (build-path bin bin-name)))))

; Invokes Z3 on the given QF_BV formula, represented as a list 
; of symbols (see examples.rkt). It returns #f if the formula 
; is unsatisfiable or a map from constant names to values if the 
; formula is satisfiable.
(define (solve encoding)
  (unless (file-exists? (z3))
    (error 'solve "could not locate z3: ~v does not exist" (z3)))
  (define-values (process out in err) 
    (subprocess #f #f #f (z3) "-smt2" "-in"))
  (with-handlers ([exn:break? (lambda (e) 
                                (subprocess-kill process #t)
                                (error 'solve "user break"))])
    (write-encoding encoding in)
    ; uncomment this to see what is being sent to the solver
    (write-encoding encoding (current-output-port))
    (define sol (read-solution out))
    (subprocess-kill process #t)
    sol))

; Writes the given encoding to the specified port.
(define (write-encoding encoding port)
  ;(fprintf port "(set-logic QF_BV)\n")
  (for ([expr encoding])
    (fprintf port "~a\n" expr))
  (fprintf port "(check-sat)\n")
  (fprintf port "(get-model)\n")
  (flush-output port))

; Reads the SMT solution from the given input port.
; The solution consist of 'sat or 'unsat, followed by  
; followed by a suitably formatted s-expression.  The 
; output of this procedure is a hashtable from constant 
; identifiers to their values (if the solution is 'sat);
; a non-empty list of assertion identifiers that form an
; unsatisfiable core (if the solution is 'unsat and a 
; core was extracted); or #f (if the solution is 
; 'unsat and no core was extracted).
(define (read-solution port)
  (match (read port)
    [(== 'sat) (read port) #t]
    [(== 'unsat) (read port) #f] 
    [other (error 'smt-solution "unrecognized solver output: ~a" other)]))