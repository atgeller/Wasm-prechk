#lang racket

(provide (all-defined-out))

(define (erase mod)
  (match mod
    [`(module ,fs ,globs ,tabs ,mems)
     `(module ,(map erase-f fs)
              ,(map erase-glob globs)
              ,(map erase-tab tabs)
              ,mems)]))

(define (erase-f f)
  (match f
    [`(,exs (func ,tfi (import ,n1 ,n2))) `(,exs (func ,(erase-tfi tfi) (import ,n1 ,n2)))]
    [`(,exs (func ,tfi (local ,ts ,es))) `(,exs (func ,(erase-tfi tfi) (local ,ts ,(map erase-e es))))]))

(define (erase-glob glob)
  (match glob
    [`(,exs (global ,tg (import ,n1 ,n2))) `(,exs (global ,tg (import ,n1 ,n2)))]
    [`(,exs (global ,tg ,es)) `(,exs (global ,tg ,(map erase-e es)))]))

(define (erase-tab tab)
  (match tab
    [`(,exs (table ,n (import ,n1 ,n2) ,tfis ...)) `(,exs (table ,n (import ,n1 ,n2)))]
    [`(,exs (table ,n ,is ...)) `(,exs (table ,n ,@is))]))

(define (erase-tfi tfi)
  (match tfi
    [`((((,t1 ,_) ...) ,_ ,_ ,_) -> (((,t2 ,_) ...) ,_ ,_ ,_)) `(,t1 -> ,t2)]))

(define (erase-e e)
  (match e
    [`(call-indirect/unsafe ,tfi) `(call-indirect ,(erase-tfi tfi))]
    [`(,t load/unsafe ,a ,o) `(,t load ,a ,o)]
    [`(,t load/unsafe (,tp ,sx) ,a ,o) `(,t load (,tp ,sx) ,a ,o)]
    [`(,t store/unsafe ,a ,o) `(,t store ,a ,o)]
    [`(,t store/unsafe ,tp ,a ,o) `(,t store ,tp ,a ,o)]
    [`(if ,tfi ,es-then else ,es-else) `(if ,(erase-tfi tfi) ,(map erase-e es-then) else ,(map erase-e es-else))]
    [`(block ,tfi ,es) `(block ,(erase-tfi tfi) ,(map erase-e es))]
    [`(loop ,tfi ,es) `(block ,(erase-tfi tfi) ,(map erase-e es))]
    [_ e]))