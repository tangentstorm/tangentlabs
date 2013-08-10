: yards 36 * ;
: yards 36 * ;  ok
: feet 12  * ;
: feet 12  * ;  ok
: inches ;
: inches ;  ok
10 yards 2 feet + 9 inches + .


: 2b0 ( c b a -- n ) * + ;
\ ----------------------------
\ ( a - 4b ) / 6 + c
: 2b1 ( c a b -- n ) -4 * + 6 / + ;

\ a / (8b) 
: 2b2 ( a b -- n ) 8 * / ;

\ 0.5 ab / 100
: 2b3 ( a b -- n ) 0.5 * * 100 / ;

\ a ( 2a + 3 )
: 2b4 ( a a -- n ) 2 * 3 + * ;
\ : 2b5 ( c b a -- n ) -
\ 2b5 was : ( a - b ) / c
( it's impossible so far, because we're dealing only with ints
and i don't know how to say "to the negative one" yet... so
there's no way to reverse the order... the best I can do
is the reciprocal. )

: 2b5 ( c a b -- ) - swap / ;
