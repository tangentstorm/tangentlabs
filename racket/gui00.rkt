#lang racket/gui


(define f (new frame% [label "hello world"]))

(send f resize 500 300)
(send f move 800 0)
(send f show #t)
