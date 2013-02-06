#lang racket
(require racklog rackunit)

(define %fact %empty-rel)
(%assert! %fact () [('a)] [('b)] [('c)])

(check-equal? '((x . a))
              (%which (x) (%fact x)))

(check-equal? '((x . b))
              (%more))


(define (facts)
  (map (compose cdr first)
                   (%find-all (x) (%fact x))))

(check-equal? '(a b c)
              (facts))
              
  

;; okay... now how can i retract only b?

(set! %fact (%rel () [('a)] [('c)]))
(check-equal? '(a c) (facts))


'(rule [mortal ?x] :-
       [human ?x])

'(fact [mortal fred])

'(fact [mortal $x ])
       

       



