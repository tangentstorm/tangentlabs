NB. Maximum value in an array according to a given verb.
NB. ----------------------------------------------------
NB. This approach uses an adverb to 
NB. modify the function.

NB. u umax y (adv.) max value in y according to verb u
NB. ----------------------------------------------------
umax =: 1 :'(u (i.>./) y) { y'



NB. derivation with example
NB. -----------------------------------------------------

] Y =. 1|.i.3 3

NB. 3 4 5
NB. 6 7 8
NB. 0 1 2

NB. Our base verb will be the 'row sum'. The goal is therefore to
NB. fetch the row with the largest sum. In this case: 6 7 8
 
U =. +/"1    NB. row sum : insert '+' between ('/') items in rank 1 ('"1')

] Y ;<,. U Y

NB. ┌─────┬──┐
NB. │3 4 5│12│
NB. │6 7 8│21│
NB. │0 1 2│ 3│
NB. └─────┴──┘
    

NB. first we find the index of the max value:

                   U Y             NB. → 12 21 3  (apply U to Y)
             >./   U Y             NB. → 21       insert >. (max) between items of U Y
   (U Y) i. (>./   U Y)            NB. → 1        find the index of result in (U Y)
        (i.  >./)  U Y             NB. → 1        simplify by rule: y f (g y) <--> (f g) y
     U ((i.  >./)@:) Y             NB. → 1        implicit conjunction with @:
    
NB. now extract the actual value
    
       (U ((i. >./)@:) Y) { Y      NB. → 6 7 8
U (1 :'(u ((i. >./)@:) y) { y') Y  NB. → 6 7 8   explicit conjunction.
U (1 :'(u  (i. >./) y)    { y') Y  NB. → 6 7 8   no longer need the @:
                                   NB. ■

NB. complete example:

+/"1 umax 1|.i.3 3                 NB. → 6 7 8
