NB. rational trigonometry
NB. see youtube videos by user: njwildberger
NB. ex: https://www.youtube.com/watch?v=yekCUuBYSGs&index=20&list=PL3C58498718451C47
NB. -----------------------------------

spr =: dyad define
  NB. lines are vectors in the form (a,b,c=0) where 0 = +/(a,b,c)*(x,y,1)
  NB. line0 spr line1 returns the 'spread'(e.0 1), from rational trigonometry.
  'a0 b0 c0' =. 3{.x [ 'a1 b1 c1' =. 3{.y
  (*:(a0*b1)-(a1*b0)) % (+/*:a0,b0)*(+/*:a1,b1)
)

qdr =: dyad define
  +/*:x-y  NB. quadtrature (square of distance between points)
)
