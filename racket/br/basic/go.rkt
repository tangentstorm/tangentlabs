#lang br
(require "struct.rkt" "line.rkt")
(provide b-end b-goto)

(define (b-end) (raise (end-program-signal)))

(define (b-goto num-expr)
  (raise (change-line-signal num-expr)))