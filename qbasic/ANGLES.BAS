0
SCREEN 12
radius = 75
originx = 640 \ 2
originy = 480 \ 2
started = 0
oldx = 0
oldy = 0
newx = 0
newy = 0
firstx = 0
firty = 0
col = 10
col2 = 2
t = 0
INPUT "Theta>", theta
IF theta = 0 THEN END
INPUT "Tilt>", tilt
CLS

CIRCLE (originx, originy), radius, col2
 t = t - (theta)
1
 t = t + (theta)
 newx = INT(COS((t + tilt) / 180 * 3.141592654#) * radius) + originx
 newy = INT(SIN((t + tilt) / 180 * 3.141592654#) * radius) + originy
 ' PRINT "("; newx; ","; newy; ")"
 IF started = 1 THEN
  LINE (oldx, oldy)-(newx, newy), col
 ELSE
  firstx = newx
  firsty = newy
  oldx = newx
  oldy = newy
  started = 1
  GOTO 1
 END IF
 oldx = newx
 oldy = newy

IF ((newx <> firstx) OR (newy <> firsty)) AND (INKEY$ = "") THEN 1

GOTO 0

