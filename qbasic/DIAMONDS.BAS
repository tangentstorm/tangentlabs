'Program Diamonds
' Takes something like :  "BANANA" or "DOG"
' and makes it into something like:
'               B
'              AAA            D
'             N N N          OOO
'            A  A  A        G G G
'           N   N   N        OOO
'          A    A    A        D
'           N   N   N
'            A  A  A
'             N N N
'              AAA
'               B
'----------------------------DIM
False = 0          'False
True = 1           'True
Quit = False       'Quit Flag for Loop
I = False          'Index for String Loop
Diamond$ = ""      'String to Display
GoOn$ = ""         'Dummy String for Continues
'----------------------------
DO WHILE Quit = False
  CLS
  COLOR 11
  PRINT "Program 'Diamonds' by 1992 Michal J. Wallace"
  COLOR 15
  PRINT "Please Enter A String to display."
  PRINT ">";
  COLOR 7
  INPUT "", Diamond$
  IF Diamond$ <> "" THEN GOSUB DoIt ELSE Quit = True
  COLOR 15
  PRINT
  PRINT
  PRINT "Press <Enter> to Continue."
  GoOn$ = INPUT$(1)
LOOP
END
'----------------------------
DoIt:
 COLOR 14
 FOR I = 1 TO LEN(Diamond$)
   LOCATE 5 + I, 40
   PRINT MID$(Diamond$, I, 1)
   LOCATE 5 + I, 40 + I - 1
   PRINT MID$(Diamond$, I, 1)
   LOCATE 5 + I, 40 - I + 1
   PRINT MID$(Diamond$, I, 1)
 NEXT I
 FOR I = LEN(Diamond$) TO 1 STEP -1
   LOCATE 2 * LEN(Diamond$) - I + 5, 40
   PRINT MID$(Diamond$, I, 1)
   LOCATE 2 * LEN(Diamond$) - I + 5, 40 + I - 1
   PRINT MID$(Diamond$, I, 1)
   LOCATE 2 * LEN(Diamond$) - I + 5, 40 - I + 1
   PRINT MID$(Diamond$, I, 1)
 NEXT I
RETURN

