#lang br
(provide (struct-out end-program-signal)
         (struct-out change-line-signal))

(struct end-program-signal ())
(struct change-line-signal (val))