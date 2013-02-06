#lang racket
(require racklog)

(define %knows
  (%rel ()
        [('Odysseus 'TeX)]
        [('Odysseus 'Racket)]
        [('Odysseus 'Prolog)]
        [('Odysseus 'Penelope)]
        [('Penelope 'TeX)]
        [('Penelope 'Prolog)]
        [('Penelope 'Odysseus)]
        [('Telemachus 'TeX)]
        [('Telemachus 'calculus)]))

(define %computer-literate
  (lambda (person)
    (%and (%knows person 'TeX)
          (%or (%knows person 'Racket)
               (%knows person 'Prolog)))))
