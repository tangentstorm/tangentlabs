#lang br
(require "struct.rkt")
(provide b-line raise-line-error)

(define-macro (b-line NUM STATEMENT ...)
  (with-pattern ([LINE-NUM (prefix-id "line-" #'NUM
                                      #:source #'NUM)])
    (syntax/loc caller-stx
      (define (LINE-NUM #:error [msg #f])
        (with-handlers
            ([line-error?
              (λ (le) (handle-line-error NUM le))])
          (when msg (raise-line-error msg))
          STATEMENT ...)))))

(define (raise-line-error str)
  (raise (line-error str)))

(define (handle-line-error num le)
  (error (format "error in line ~a: ~a"
                 num (line-error-msg le))))