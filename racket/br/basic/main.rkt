#lang br/quicklang
(require "parser.rkt" "tokenizer.rkt")
(module+ reader
  (provide read-syntax get-info))

(define (read-syntax path port)
  (strip-bindings
   #`(module basic-mod basic/expander
       #,(parse path (make-tokenizer port path)))))

(define (get-info port src-mod src-line src-col src-pos)
  (define (handle-query key default)
    (case key
      [(color-lexer)
       (dynamic-require 'basic/colorer 'basic-colorer)]
      [else default]))
  handle-query)
