'Program Roman Numerals
'By Michal Wallace
'---------------------------
Num = 1      'Integer Number
Num$ = ""    'String Version of Number
Roman$ = ""  'Roman Numeral of Num
I = 0        'Loop Index
M$ = ""      'Letter from String
O$ = ""      '
F$ = ""      '
T$ = ""      '
'------------
WHILE Num <> 0
  COLOR 15
  PRINT
  PRINT "Input an integer in the range of 0 to 9999."
  PRINT ">"; : COLOR 7: INPUT "", Num
  Num$ = STR$(Num)
  Roman$ = ""
  RESTORE
  FOR I = 1 TO LEN(Num$)
    IF I = 1 THEN
      O$ = "I"
      F$ = "V"
      T$ = "X"
    ELSE
    IF I = 2 THEN
      O$ = "X"
      F$ = "L"
      T$ = "C"
    ELSE
    IF I = 3 THEN
      O$ = "C"
      F$ = "D"
      T$ = "M"
    ELSE
      O$ = "M"
      F$ = "V"
      T$ = "m"
    END IF
    END IF
    END IF
    M$ = MID$(Num$, I, 1)
    IF M$ = "1" THEN Roman$ = Roman$ + O$
    IF M$ = "2" THEN Roman$ = Roman$ + O$ + O$
    IF M$ = "3" THEN Roman$ = Roman$ + O$ + O$ + O$
    IF M$ = "4" THEN Roman$ = Roman$ + O$ + F$
    IF M$ = "5" THEN Roman$ = Roman$ + F$
    IF M$ = "6" THEN Roman$ = Roman$ + F$ + O$
    IF M$ = "7" THEN Roman$ = Roman$ + F$ + O$ + O$
    IF M$ = "8" THEN Roman$ = Roman$ + F$ + O$ + O$ + O$
    IF M$ = "9" THEN Roman$ = Roman$ + O$ + T$
    IF M$ = "0" THEN
         Roman$ = Roman$ + T$
         I = I + 1
    END IF
  NEXT I
  COLOR 15: PRINT
  PRINT "The Roman Numeral for"; Num$; " is ";
  COLOR 7: PRINT Roman$; : COLOR 15: PRINT "."
WEND
END

