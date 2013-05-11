' program life : the game of life
'///////////////////////////////////////////
CONST maxrow = 25                ' max row
CONST maxcol = 80                ' max column
CONST maxage = 5
CONST dead = 0
DIM grid(maxrow + 1, maxcol + 1) ' the grid + border
DIM temp(maxrow + 1, maxcol + 1) ' temp grid + border
DIM numneighbors AS INTEGER
DIM row AS INTEGER
DIM col AS INTEGER
DIM char(maxage) AS STRING * 1
DIM pal(maxage) AS INTEGER

'///////////////////////////////////////////
Init:
'///////////////////////////////////////////
char(dead) = " ":  pal(dead) = 15 'empty space
FOR row = 1 TO maxage
  char(row) = "þ"
  pal(row) = row
NEXT row
GOTO MainProgram
   
'///////////////////////////////////////////
DRAWGRID:
'///////////////////////////////////////////
  FOR row = 1 TO maxrow
    FOR col = 1 TO maxcol
      LOCATE row, col
      COLOR pal(grid(row, col))
      PRINT char(grid(row, col));
    NEXT col
  NEXT row
RETURN

'///////////////////////////////////////////
SEEDGRID:
'///////////////////////////////////////////
  '************************************************
  '*** put loop in here to manually draw screen ***
  '************************************************
  FOR row = 0 TO maxrow + 1
    FOR col = 0 TO maxcol + 1
      grid(row, col) = dead
    NEXT col
  NEXT row
  FOR row = 1 TO maxrow
    FOR col = 1 TO maxcol
      grid(row, col) = INT(RND * 2)
    NEXT col
  NEXT row
RETURN

'///////////////////////////////////////////
GETNUMNEIGHBORS: '(row, col) : NumNeighbors
'///////////////////////////////////////////
  numneighbors = 0
  IF grid(row - 1, col - 1) <> dead THEN numneighbors = numneighbors + 1
  IF grid(row - 1, col) <> dead THEN numneighbors = numneighbors + 1
  IF grid(row - 1, col + 1) <> dead THEN numneighbors = numneighbors + 1
  IF grid(row, col - 1) <> dead THEN numneighbors = numneighbors + 1
  IF grid(row, col + 1) <> dead THEN numneighbors = numneighbors + 1
  IF grid(row + 1, col - 1) <> dead THEN numneighbors = numneighbors + 1
  IF grid(row + 1, col) <> dead THEN numneighbors = numneighbors + 1
  IF grid(row + 1, col + 1) <> dead THEN numneighbors = numneighbors + 1
RETURN


'///////////////////////////////////////////
ITERATE:
'///////////////////////////////////////////
  
  FOR row = 0 TO maxrow + 1
    FOR col = 0 TO maxcol + 1
      temp(row, col) = grid(row, col)
    NEXT col
  NEXT row

  FOR row = 1 TO maxrow
    FOR col = 1 TO maxcol
      GOSUB GETNUMNEIGHBORS
      IF grid(row, col) <> dead THEN
        SELECT CASE numneighbors
          CASE 2 TO 3
            temp(row, col) = temp(row, col) + 1
            IF temp(row, col) > maxage THEN temp(row, col) = maxage
          CASE ELSE
            temp(row, col) = dead
        END SELECT
      ELSE
        SELECT CASE numneighbors
          CASE 3 TO 3
            temp(row, col) = temp(row, col) + 1
            IF temp(row, col) > maxage THEN temp(row, col) = maxage
          CASE ELSE
            temp(row, col) = dead
        END SELECT
      END IF
    NEXT col
  NEXT row
 
  FOR row = 0 TO maxrow + 1
    FOR col = 0 TO maxcol + 1
      grid(row, col) = temp(row, col)
    NEXT col
  NEXT row

RETURN

'///////////////////////////////////////////
MainProgram:
'///////////////////////////////////////////

GOSUB SEEDGRID
DO
  GOSUB DRAWGRID
  GOSUB ITERATE
LOOP UNTIL INKEY$ = CHR$(27)
'end

