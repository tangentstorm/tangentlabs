#lang br
(provide b-sum b-expr)

(define (b-sum . vals) (apply + vals))

(define (b-expr expr)
  (if (integer? expr) (inexact->exact expr) expr))