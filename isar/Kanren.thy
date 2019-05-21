theory Kanren
imports Main
begin

datatype MK
   = Goal     :: State => Stream
   | State    :: (Subst, Nat)
   | Stream   :: (Mature | Immature)
   | Mature   :: () | (State, Stream)
   | Immature :: Unit => Stream


text "
six basic operators:
  ==                             (term, term) -> goal
  call/fresh                     (var->goal)  -> goal
  disj                           (goal, goal) -> goal
  conj                           (goal, goal) -> goal
  define-relation                # macro
  call/initial-state             (nat, goal) -> Mature
----
  unify
  $append                         
  $append-map

  pull                           stream -> mature
  take                           (nat, goal) -> list
"

(define (≡ u v)
  (λ (s/c)
    (let ((s (unify u v (car s/c))))
       (if s (unit `(, s . , (cdr s/c))) mzero))))

(define ((== u v) s/c)
  (let ((s (car s/c)))
    (let ((s (unify (find u s) (find v s) s)))
      (if s (list `(,s . ,(cdr s/c))) `()))))

(define (unify u v s)
  (cond
    ((eqv? u v) s)
    ((var? u) (ext-s u v s))
    ((var? v) (unify v u s))
    ((and (pair? u) (pair? v))
      (let ((s (unify (find (car u) s) (find (car v) s) s)))
        (and s (unify (find (cdr u) s) (find (cdr v) s) s))))
    (else #f)))

(define (find u s)
  (let ((pr (and (var? u) (assv u s))))
    (if pr (find (cdr pr) s) u)))

(define (ext-s x u s)
  (cond
    ((occurs? x u s) #f)
    (else (cons `(,x . ,u) s))))

(define (occurs? x u s)
  (cond
    ((var? u) (eqv? x u))
    ((pair? u) (or (occurs? x (find (car u) s) s)
    (occurs? x (find (cdr u) s) s)))
    (else #f)))



end