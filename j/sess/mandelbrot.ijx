
   NB. Mandelbrot set in J.
   NB.
   NB. I thought I was keeping a full log, but it turned out the
   NB. scrollback was cut short and the buffer was eaten up by 
   NB. lines where i was testing out minor formatting changes.

   'X.' {~ 2 <| 0&(([ + *:@])^:11~)"0 [ _0.5+|.|:(] j./ [: i: 1j4"_) i:1.5j65
..........................................XX......................
...............................XXXXXXXXXXXXXXXXXXXXX..............
XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX................
...............................XXXXXXXXXXXXXXXXXXXXX..............
..........................................XX......................

   NB. here's a high-res version:
   NB. screenshot:  http://imgur.com/gallery/NJR4hK2/new

load'viemat'
viewmat 2 <| 0&(([ + *:@])^:11~)"0 [ _0.5+|.|:(] j./ [: i: 1j768"_) i:1.5j1024
   

NB. (a little bit later)
NB. Hrm! just had an idea! I can use that (5>), which gets all
NB. the results, and use that to figure out at which iteration
NB. the value became greater than 2.

NB. If I do this, then I basically have a stack of these things through time.

   'x.' {~ |:"2 |:"3 [  2 <| 0&(([ + *:@])^:(<5)~)"0 [ _0.5+|.|:(] j./ [: i: 1j5"_) i:1.5j65
xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx
xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx
xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx
xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx
xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx
xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx

......xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx
..xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx
.xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx
.xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx
..xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx
......xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx

............xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx............
....xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx....
.xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx.
.xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx.
....xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx....
............xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx............

.............................xxxxxxxxxxxxxxxxxxxxx................
..................xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx..........
..xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx........
..xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx........
..................xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx..........
.............................xxxxxxxxxxxxxxxxxxxxx................

....................................xxxxxxxxx.....................
......................xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx............
........xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx...........
........xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx...........
......................xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx............
....................................xxxxxxxxx.....................


NB. I want to figure out how to get a 'core sample' of this 3d construct.
NB. I can simplify by trying to get a small cube:
cube =. i. 2 2 2

0 1
2 3

4 5
6 7
   
NB. So here, I want to extract each vertical column.
NB. That means ('0 4', '1 5', '2 6', '3 7')

   0 {"1 [ 0 {"1 cube
0 4
   0{"1 [ 1{"1 cube
1 5
   1{"1 [ 0{"1 cube
2 6
   1{"1 [ 1{"1 cube
3 7

NB. Hrm.. It occurs to me that I only have this problem because
NB. I re-arranged the 3d array. If I just applied my color function
NB. to level 1, I might be okay.

NB. so what's my color function?
NB. I want the number of the iteration where it first becomes 1.


load 'viewmat'
viewmat +/"1 [ 2 <| 0&(([ + *:@])^:(<10)~)"0 [ _0.5+|.|:(] j./ [: i: 1j480"_) i:1.5j640


viewmat +/"1 [ 2 <| 0&(([ + *:@])^:(<10)~)"0 [ _0.5+|.|:(] j./ [: i: 1j480"_) i:1.5j640

NB. everything to the right side of the middle '[' by '_0.5' is creating a little grid of complex numbers.
NB.
NB. the stuff from  the '0&' to the '"0'  to the left of that is performing the recursive mandelbrot set test.
NB. well it's the 'z' in the mandelbrot test...   mandelbrot c 0 = 0 ; mandelbrot c z = c + (mandelbrot z-1)^2
NB. where c is one of those complex points. 
NB.
NB. if that number ever gets bigger than 2 then you know it's not in the set.
NB. (the set is the shape in the middle.) that's what  2< does. ('|' is magnitude,
NB. and I'm not sure I actually need it now.)
NB.
NB. to make it colored, i did ^:(<10) instead of ^:10  ... 
NB. that made it calculate an array of 10 values. so i have 10 booleans for each cell
NB. +/"1  tells it to sum across the next to lowest level, so it's summing the 10 values for each cell.
NB.
NB. so... if 2< for the first time on the last step, the number will be 1...
NB. if it happens on the step before, the sum will  be 2, and so on.
NB.
NB. viewmat is just a tool that comes with j to view matrices in color.

