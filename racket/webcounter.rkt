#lang web-server/insta
;; from http://docs.racket-lang.org/continue/

(define (start request)
  (show-counter 0 request))

(define (show-counter n request)
  (local [(define (response-generator embed/url)
            (response/xexpr
             `(html (head (title "counting example"))
                    (body
                     (a ((href , 