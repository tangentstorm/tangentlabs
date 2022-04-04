#lang racket

; https://projecteuler.net/problem=14
; (find the number between 1 and 1 million
; with the longest collatz path to 1)

(define (collatz x)
  (if (even? x) (/ x 2) (+ 1 (* 3 x))))

(define SIZE 1000000) ; size of search space

; I tried a vector at first, but we need to hold numbers
; much much bigger than 1 million because the numbers in the
; path go extremely high. (500x was too small)
;(define cache (make-vector (* 500 SIZE)))
;(define (cache-get k) (vector-ref cache k))
;(define (cache-set! k v) (begin (vector-set! cache k v) v))

; so, here's a sparse representation instead:
(define cache (make-hash))
(define (cache-get k) (hash-ref cache k 0))
(define (cache-set! k v) (hash-set! cache k v))

(define (collatz-path-length x)
  (if (equal? x 1) 1
      (let ([v (cache-get x)])
        (cond
          [(equal? v 0)
           (let* ([c (collatz x)]
                  [p (+ 1 (collatz-path-length c))])
             (cache-set! x p)
             p)]
          [else v]))))

(define max-val 1)
(define max-len 1)
(for ([i (in-range 1 SIZE)])
  (let ([c (collatz-path-length i)])
    (when (> c max-len)
        (begin
          (set! max-len c)
          (set! max-val i)))))

(printf
 "max length was ~a, starting at ~a" max-len max-val)
