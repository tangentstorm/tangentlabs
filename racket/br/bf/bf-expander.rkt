#lang br/quicklang
(define-macro (bf-module-begin PARSE-TREE)
  #'(#%module-begin PARSE-TREE))

(define-macro (bf-program NODE ...)
  #'(void NODE ...))

(define-macro (bf-loop "[" NODE ... "]")
  #'(until (zero? (mem-get)) NODE ...))

(define-macro-cases bf-op
  [(bf-op ">") #'(gt)]
  [(bf-op "<") #'(lt)]
  [(bf-op "+") #'(inc)]
  [(bf-op "-") #'(dec)]
  [(bf-op ".") #'(dot)]
  [(bf-op ",") #'(com)])

(define mem (make-vector 30000 0))
(define ptr 0)
(define (mem-get) (vector-ref mem ptr))
(define (mem-set! x) (vector-set! mem ptr x))
(define (gt) (set! ptr (add1 ptr)))
(define (lt) (set! ptr (sub1 ptr)))
(define (inc) (mem-set! (add1 (mem-get))))
(define (dec) (mem-set! (sub1 (mem-get))))
(define (dot) (write-byte (mem-get)))
(define (com) (read-byte (mem-set! (read-byte))))

(provide [rename-out (bf-module-begin #%module-begin)]
         bf-program bf-loop bf-op)
