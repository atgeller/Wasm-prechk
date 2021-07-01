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

(define (erase-tiann tiann)
  (match tiann
    [`(((,t ,_) ...) ,_ ,_) t]))

(define (erase-tfi tfi)
  (match tfi
    [`(,tiann1 -> ,tiann2) `(,(erase-tiann tiann1) -> ,(erase-tiann tiann2))]))

(define (erase-e e)
  (match e
    [`(,t div-s/unsafe) `(,t div-s)]
    [`(,t div-u/unsafe) `(,t div-u)]
    [`(,t rem-s/unsafe) `(,t rem-s)]
    [`(,t rem-u/unsafe) `(,t rem-u)]
    [`(call-indirect/unsafe ,tfi) `(call-indirect ,(erase-tfi tfi))]
    [`(,t load/unsafe ,a ,o) `(,t load ,a ,o)]
    [`(,t load/unsafe (,tp ,sx) ,a ,o) `(,t load (,tp ,sx) ,a ,o)]
    [`(,t store/unsafe ,a ,o) `(,t store ,a ,o)]
    [`(,t store/unsafe ,tp ,a ,o) `(,t store ,tp ,a ,o)]
    [`(if ,tfi ,es-then else ,es-else) `(if ,(erase-tfi tfi) ,(map erase-e es-then) else ,(map erase-e es-else))]
    [`(block ,tfi ,es) `(block ,(erase-tfi tfi) ,(map erase-e es))]
    [`(loop ,tfi ,es) `(block ,(erase-tfi tfi) ,(map erase-e es))]
    [_ e]))

(define (erase-C C)
  (match C
    [`((func ,tfi-f ...)
       (global ,tg ...)
       (table (,n-t ,tfi-t ...) ...)
       (memory ,n-m ...)
       (local ,t-l ...)
       (label ,tiann-lbl  ...)
       (return ,tiann-ret ...))
     `((func ,@(map erase-tfi tfi-f))
       (global ,@tg)
       (table ,@n-t)
       (memory ,@n-m)
       (local ,@t-l)
       (label ,@(map erase-tiann tiann-lbl))
       (return ,@(map erase-tiann tiann-ret)))]))