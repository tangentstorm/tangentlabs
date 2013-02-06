parent(cathy, michal).
parent(bob, michal).
parent(Par, Child) :- parent(Par, Sib), sibling(Child, Sib).

brother(michal, steve).
brother(A, B) :- !, A \= B, brother(B, A).

sibling(A, B) :- A \= B, brother(A, B).



s  --> np, vp.
np -->  det, n.
det --> [the].
det --> [a].
np --> det, n.
vp --> v, np.
vp --> v.
n --> [cat].
n --> [dog].
v --> [ate].


