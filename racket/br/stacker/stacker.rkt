#lang br/quicklang
; this file provides the reader for the stacker language
; from "beautiful racket"

(define (read-syntax path port)
  (define src-lines (port->lines port))
  (define src-datums (format-datums '(handle ~a) src-lines))
  (datum->syntax #f
     `(module stacker-mod "stacker.rkt"
        ,@src-datums
       #;,@(for/list ([datum (in-port read port)]) datum)      )))

(define-macro (stacker-module-begin HANDLE-EXPR ...)
  #'(#%module-begin
     HANDLE-EXPR ...
     (display (first stack))))


(define stack empty)
(define (pop-stack!)
  (define arg (first stack))
  (set! stack (rest stack))
  arg)
(define (push-stack! arg)
  (set! stack (cons arg stack)))

(define (handle [x #f])
  (cond [(number? x) (push-stack! x)]
        [(or (equal? + x) (equal? * x))
         (define res (x (pop-stack!) (pop-stack!)))
         (push-stack! res)]))

(provide read-syntax handle + * ; #%top-interaction
         (rename-out [stacker-module-begin #%module-begin]))