NB. how can we sort an array by a function?

] Y =. 1|.i.3 3
NB. 3 4 5
NB. 6 7 8
NB. 0 1 2


] (; +/"1) Y
NB. ┌─────┬───────┐
NB. │3 4 5│12 21 3│
NB. │6 7 8│       │
NB. │0 1 2│       │
NB. └─────┴───────┘
 
V =. +/"1

NB. (u umaxi) y  -> index of max value in u y
NB. -----------------------------------------
umaxi =: (i. >./)@:
NB. -----------------------------------------
                   V Y           NB. -> 12 21 3 
             >./   V Y           NB. -> 21
   (V Y) i. (>./   V Y)          NB. -> 1
        (i.  >./)  V Y           NB. -> 1    y f (g y) <--> (f g) y
        (i.  >./)@:V Y           NB. -> 1    f g y <--> f@:g y

(+/"1 umaxi) Y                   NB. -> 1
((+/"1 umaxi) Y) { Y             NB. -> 6 7 8
umax =: 1 :'(u (i.>./) y) { y'
+/"1 umax Y                      NB. -> 6 7 8
