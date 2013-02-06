#lang plai
(require "lecter.rkt")
(require rackunit)

(printf "Running tests...\n")

(check-equal? (parse '(@foo))
              (@ "foo"))

(check-equal? (parse '(!bar))
              (! "bar"))


(check-equal? (chain '(@a -> !b -> @c -> !d -> @e))
              '((@a -> !b) 
                (!b -> @c) 
                (@c -> !d) 
                (!d -> @e)))


(printf "Done with tests!")