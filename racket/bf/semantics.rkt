#lang racket

(require rackunit)
(provide (all-defined-out))

;; our state contains two pieces
(define-struct state (data ptr)
  #:mutable)

;; Creates a new state, with a byte array of 30000 zeros,
;; and the pointer at index 0.
(define (new-state)
  (make-state (make-vector 30000 0)
              0))

;; Increment the data pointer
(define (increment-ptr a-state)
  (set-state-ptr! a-state (add1 (state-ptr a-state))))

;; Decrement the data pointer
(define (decrement-ptr a-state)
  (set-state-ptr! a-state (sub1 (state-ptr a-state))))

;; increment the byte at the data pointer
(define (increment-byte a-state)
  (let ([v (state-data a-state)]
        [i (state-ptr a-state)])
        (vector-set! v i (add1 (vector-ref v i)))))

;; decrement the byte at the data pointer
(define (decrement-byte a-state)
  (let ([v (state-data a-state)]
        [i (state-ptr a-state)])
        (vector-set! v i (sub1 (vector-ref v i)))))

;; print the byte at the data pointer
(define (write-byte-to-stdout a-state)
  (let ([v (state-data a-state)]
        [i (state-ptr a-state)])
    (write-byte (vector-ref v i) (current-output-port))))

;; read a byte from stdin into the data pointer
(define (read-byte-from-stdin a-state)
  (let ([v (state-data a-state)]
        [i (state-ptr a-state)])
    (vector-set! v i (read-byte (current-input-port)))))

;; and the loop:
(define-syntax-rule (loop a-state body ...)
  (let loop ()
    (unless (= (vector-ref (state-data a-state)
                           (state-ptr a-state))
               0)
      body ...
      (loop))))


;;;;; test code ;;;;;;;;;;;;;;;;;;;;


;; simple exercises
(let ([s (new-state)])
  (increment-byte s)
  (check-equal? 1 (vector-ref (state-data s) 0))
  (increment-byte s)
  (check-equal? 2 (vector-ref (state-data s) 0))
  (decrement-byte s)
  (check-equal? 1 (vector-ref (state-data s) 0)))

;; pointer movement
(let ([s (new-state)])
  (increment-ptr s)
  (increment-byte s)
  (check-equal? 0 (vector-ref (state-data s) 0))
  (check-equal? 1 (vector-ref (state-data s) 1))
  (decrement-ptr s)
  (increment-byte s)
  (check-equal? 1 (vector-ref (state-data s) 0))
  (check-equal? 1 (vector-ref (state-data s) 1)))

