#lang br/quicklang
(require "parser.rkt" "tokenizer.rkt")

(define (read-syntax path port)
  (strip-bindings
   #`(module basic-mod basic/expander
       #,(parse path (make-tokenizer port path)))))

(module+ reader
  (provide read-syntax))