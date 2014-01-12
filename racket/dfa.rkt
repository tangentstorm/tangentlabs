#lang racket
(require rackunit)
(define-syntax-rule ($ .* ...) (define-syntax-rule .* ...))

($ (while p stmt ...) (let loop () (when p (begin stmt ...) (loop))))
($ (inc i) (set! i (+ 1 i)))
($ (: wrd dfn ...) (define wrd dfn ...))
($ (^ fun (arg ...) dfn ...) (: (fun arg ...) dfn ...))
(: len string-length)
(: ch@ string-ref)

; [str] → [prefix]
(^ f (s0 s1)
  (: i 0) (: res '())
  (while (and (eq? (ch@ s0 i) (ch@ s1 i)) 
              (< i (min (len s0) (len s1))))
         (inc i))
  (if (= i 0) (list s0 s1) (list (substring s0 0 i)
                                 (list (substring s0 i (len s0))
                                       (substring s1 i (len s1))))))

;-- test cases ---
(check-equal? (f "abc" "123") '("abc" "123"))
(check-equal? (f "abc" "a123") '("a" ("bc" "123")))
(define ≠ (lambda (a b) (not (eq? a b))))
(check ≠ 'abc 123)
