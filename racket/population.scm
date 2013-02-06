;
; population simulation
;


(define (random-gender)
  (if (= 0 (random 2)) 'm 'f))

; just using list for now so i can display more easily
(define-struct creature (age health gender dna))
(define (new-creature)
  (list 0 100 (random-gender) ()))

(define (build-population n) 
  (cond ((= n 0) ())
	(else (cons (new-creature)
		    (build-population (- n 1))))))

;-- run it ---
(display (build-population 5))
(newline)
