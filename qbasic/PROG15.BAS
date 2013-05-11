'-------------------
' Michal Wallace
'-------------------
' Basic Programs, #15
' Change
'-------------------
' Variables
'-------------------
 Counter = 0  ' Variable for Loop
 Nickels = 0  ' Number of Nickels  ( 2 to 7 )
 Dimes = 0    ' Number of Dimes    ( 1 to 8 )
 Quarters = 0 ' Number of Quarters ( 0 to 5 )
 Amount = 0   ' Total Amount of Money
'-------------------
' Program
'-------------------
PRINT
FOR Counter = 1 TO 4
  Nickels = INT(RND * 5) + 2
  Dimes = INT(RND * 7) + 1
  Quarters = INT(RND * 5)
  Amount = (.05 * Nickels) + (.1 * Dimes) + (.25 * Quarters)
  PRINT "-------------------------------------------------------"
  PRINT USING "\       \$$#.##\      \#"; "You found"; Amount; " on day"; Counter; "."
NEXT Counter
PRINT "-------------------------------------------------------"
'-------------------
END
'-------------------

