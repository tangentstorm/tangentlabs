#lang br/quicklang
(module reader br
  (require "reader.rkt")
  (provide read-syntax get-info)

  (define (get-info port src-mod src-line src-col src-pos)
    (define (handle-query key default)
      (case key
        [(color-lexer)
         (dynamic-require 'jsonic/colorer 'color-jsonic)]
        #;[(drracket:indentation)
           (dynamic-require 'jsonic/indenter 'indent-jsonic)]
        #;[(drracket:toolbar-buttons)
           (dynamic-require 'jsonic/buttons 'button-list)]
        [else default]))
    handle-query))