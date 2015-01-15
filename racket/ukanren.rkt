#lang racket
;
; ukanren , transcribed from
; "µKanren: A minimal Functional Core for Relational Programming"
; by Jason Hemann and Daniel P. Friedman
;

;-- internal routines -----------------------

(require rnrs/lists-6)
(provide (all-defined-out))

(define (var c) (vector c))
(define (var? x) (vector? x))
(define (var=? x1 x2) (= (vector-ref x1 0) (vector-ref x2 0)))

(define (walk u s)
  (let ((pr (and (var? u) (assp (lambda (v) (var=? u v)) s))))
    (if pr (walk cdr pr) s) u))

(define (ext-s x v s) `((,x . ,v) . ,s))

(define (unit s/c) (cons s/c mzero))
(define mzero '())
(define (mplus $1 $2)
  (cond
    ((null? $1) $2)
    ((procedure? $1) (λ () (mplus $2 ($1))))
    (else (cons (car $1) (mplus (cdr $1) $2)))))

(define (bind $ g)
  (cond
    ((null? $) mzero)
    ((procedure? $) (λ () (bind ($) g)))
    (else (mplus (g (car $)) (bind (cdr $) g)))))

(define (unify u v s)
  (let ((u (walk u s)) (v (walk v s)))
    (cond
      ((and (var? u) (var? v) (var=? u v)) s)
      ((var? u) (ext-s u v s))
      ((var? v) (ext-s v u s))
      ((and (pair? u) (pair? v))
       (let ((s (unify (car u) (car v) s)))
         (and s (unify (cdr u) (cdr v) s))))
      (else (and (eqv? u v) s)))))

;-- public interface ------------------------------------------

(define (== u v)
  (λ (s/c)
    (let ((s (unify u v (car s/c))))
      (if s (unit `(,s . ,(cdr s/c))) mzero))))

(define (call/fresh f)
  (λ (s/c)
    (let ((c (cdr s/c)))
      ((f (var c)) `(,(car s/c) . ,(+ c 1)))))) ; -- really?

(define (disj g1 g2) (λ (s/c) (mplus (g1 s/c) (g2 s/c))))
(define (conj g1 g2) (λ (s/c) (bind (g1 s/c) g2)))
