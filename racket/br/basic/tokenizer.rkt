#lang br
; the "tokenizer" here is for the parser.
; the "lexer" is used by this tokenizer,
; but it's also used for the dr-racket integration.
(require "lexer.rkt" brag/support)

(define (make-tokenizer ip [path #f])
  (port-count-lines! ip)
  (lexer-file-path path)
  (λ () (basic-lexer ip)))

(provide make-tokenizer)
