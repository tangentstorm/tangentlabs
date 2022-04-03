#lang br/quicklang
(require "bf-parser.rkt")
(require brag/support)

(define (read-syntax path port)
  (define parse-tree (parse path (make-tokenizer port)))
  (datum->syntax
   #f
   `(module bf-mod "bf-expander.rkt"
      ,parse-tree)))

(define (make-tokenizer port)
  (define (next-token)
    (define bf-lexer
      (lexer
       [(char-set "><-.,+[]")  lexeme]
       [any-char (next-token)]))    
    (bf-lexer port))
  next-token)

(provide read-syntax)
