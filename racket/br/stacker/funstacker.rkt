#lang br/quicklang
; this file provides the reader for the stacker language
; from "beautiful racket"
; (functional programming version)

(define (read-syntax path port)
  (define src-datums (format-datums '~a (port->lines port)))
  (datum->syntax #f
     `(module funstacker-mod "funstacker.rkt"
        (handle-args ,@src-datums)
       #;,@(for/list ([datum (in-port read port)]) datum)      )))

(define-macro (module-begin HANDLE-EXPR)
  #'(#%module-begin
     (display (first HANDLE-EXPR))))

(define (handle-args . args)
  (for/fold ([stack empty]) ([arg (in-list args)] #:unless (void? arg))
     (cond
       [(number? arg) (cons arg stack)]
       [(or (equal? * arg) (equal? + arg))
            (cons (arg (first stack) (second stack))
                  (drop stack 2))] )))

(provide read-syntax handle-args + * ; #%top-interaction
         (rename-out [module-begin #%module-begin]))