NB. floodfill demonstration

NB. helper routines
get =: 1 : '(<m) { y'
put =: 2 : 'n (<m) } y'
show =: [: (<"2) _ * 0 = ]
zero =: 0:"0
artwk =: ('.+O'&i.)
pretty =. artwk inv
grid =: <"2
NB. usage
1 1 put _ i. 3 3
1 1 get i. 3 3

(1 1 put _ i. 3 3) ; (1 1 get i. 3 3)

NB. here is a simple floodfill. it just expands
NB. a pattern of ones in all 4 directions
grow =: 1 0 _1 & ((|."0 1/) ([:+./+.) (|."0 2))"2

NB. a small display routine to show the effect at center and edges:
showg =: [: echo [: grid artwk inv 
showg m =: ((0 2 put 1), (2 2 put 1), (2 0 put 1),: (4 1 put 1)) 5 5 $ 0
showg grow m

NB. the problem is it floods past the sides. so we need to clip it.
NB. we can do that by surrounding the grid with a border and then removing it.
around =: 1 : '(_1 _1 |. [ {.!.x~ >:^:2 @ $ @ ,.)"2'
shrink =: }:"1 @: }."1 @: }:"2 @: }."2
clip =: 0 around :. shrink     NB. combine so we can use the &. conjunction 

echo 'clipping in action:'
showg grow&.clip m

echo 'and iterated over time:'
showg (grow&.clip)^:(<_)  m

NB. The last step is to constrain the growth so it only
NB. fills in the squares that meet the target condition.
NB. In the most basic case, we want to just flood 
NB. neighboring cells that have the same value as the
NB. starting cell(s). (Since our algorithm works in parallel
NB. there's no reason we have to limit ourselves to one
NB. starting point, but one is usually enough.)
NB.
NB. We have at least two options at this point: either we make
NB. floodfill a verb with the most common case hard-coded,
NB. or else we compose it out of a verb that checks the 
NB. spread conditions and an adverb that modifies this predicate
NB. to act as a flood fiil.
NB.
NB. Let's do both, for comparison. We'll start with the explicit
NB. verb and then factor out an adverb.

NB. ff0 : explicit floodfill implementation
NB. ------------------------------------------------
ff0 =: 4 : 0

  NB. here, we'll start with a single point.
  r =. (x put 1)@:zero y
  
  NB. given the coordinates of the starting cell, fetch the 
  NB. color we're replacing. We're only going to flood into
  NB. cells that are this color *and* adjacent to the flood
  NB. zone. since the flood zone is an array of booleans,
  NB. we don't actually want the the color at the start cell,
  NB. but rather an array of booleans, where 1=the color matches
  NB. the flood color, and 0 means it doesn't. This will have
  NB. extra data where the color appears but isn't connected
  NB. to the flood zone, but that's fine because we'll always
  NB. AND it to the flood zone at each step.
  mask =. y = (x get) y
  echo 'mask:'; pretty mask 
  
  NB. now we'll extend our floodstep by applying the mask.
  NB. it's a simple logical AND (*.)
  step =. mask *. (grow &. clip)

  NB. we can just use  step^:_ to loop until it stops changing.
  NB. we can use step^:(<_) to do the same but collect the
  NB. results along the way. That's probably the nicer way to
  NB. do it, but here's an explicit loop just for comparison:
  NB. here's the explicit versions
  i =. 0 [[ next =. r
  NB. whilst (s)kips the (t)est (so it's do... while ())
  whilst. (-. next -: r) do.
    r =. next 
    next =. step r
    echo i ; (pretty y + next)
    i =. i+1
  end.
  y + next return.
)
] img =: ({'.O'"_) (i.4 11) e. 35 3 7 16,(23+i.8)
echo '-- ready to fill--'
echo 'result:'; 0 0 ff0 &.artwk img

