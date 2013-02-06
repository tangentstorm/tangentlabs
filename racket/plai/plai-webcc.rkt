#lang plai
(define the-receiver (box 'dummy-value))
(define receiver-prompt (box 'dummy-value))

(define (web-display n)
  (printf "Web output: ~a~n" n))

(define (web-read/k p k)
  (begin
    (set-box! receiver-prompt p)
    (set-box! the-receiver k)
    (resum(error 'web-read/k "run (resume) to enter number and simulate clicking Submit")))
  
(define (resume)
  (begin
    (display (unbox receiver-prompt)
             (unbox the-receiver) (read))))

