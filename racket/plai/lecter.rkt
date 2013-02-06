#lang plai
(require srfi/13) ;; strinng lib (http://srfi.schemers.org/srfi-13/srfi-13.html)


(define-type lecter
  [! (label string?)]
  [@ (label string?)])
     

(define (parse sexp)
  (let [(head (first sexp))]
    (match head
      [symbol (parse-symbol head)]
      [_ `(couldnt-parse: ,head)])))


(define (parse-symbol sym)
  (let* [(iden (symbol->string sym))
         (sigil (string-take iden 1))
         (label (string-drop iden 1))]
    (match sigil
      ["@" (@ label)]
      ["!" (! label)]
      [=> `(bad-symbol: ,sym)])))


;; ex: (a - b - c)  -> '((a - b) (b - c) (c - d))
(define (chain links)
  (match links
    [(list a to b) (list (list a to b))]
    [(list a to) (error "need one more token:" links)]
    [(list a) (error "need two more tokens:" links)]
    [(list a to b +tail ...) (cons (list a to b) (chain (cons b +tail)))]))
                              
