( large letter f )
: star   42 emit ;
: stars   0 do star loop ;
: margin   cr 30 spaces ;
: blip   margin star ;
: bar   margin 5 stars ;
: f   bar blip bar blip blip cr ;

: gift ." nice present" ;
: giver   ." stephanie" ;
: thanks   ." Dear " giver ." , thanks for the " gift  ." ." ;

: ten.less ( n-n )  10 - ;

    
    