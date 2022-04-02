#lang br/quicklang
(require json)

(define-macro (jsonic-mb PARSE-TREE)
  #'(#%module-begin
     (define result-string PARSE-TREE)
     (define validated-jsexpr (string->jsexpr result-string))
     (display result-string)))

(define-macro (jsonic-char C) #'C)

(define-macro (jsonic-program P ...)
  #'(string-trim (string-append P ...)))

(define-macro (jsonic-sexp SX)
  (with-pattern ([SX-DAT (format-datum '~a #'SX)])
    #'(jsexpr->string SX-DAT)))

(provide (rename-out [jsonic-mb #%module-begin])
         jsonic-program jsonic-char jsonic-sexp)
