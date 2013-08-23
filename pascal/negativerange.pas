{$mode fpc}
program negativerange;

var
  ints : array[-10..10] of integer;
  i    : integer;
begin
  for i := -10 to 10 do ints[i] := i*i;
  for i := 10 downto -10 do writeln(i:3, ' :', ints[i]:4);
end.

{ output:

 10 : 100
  9 :  81
  8 :  64
  7 :  49
  6 :  36
  5 :  25
  4 :  16
  3 :   9
  2 :   4
  1 :   1
  0 :   0
 -1 :   1
 -2 :   4
 -3 :   9
 -4 :  16
 -5 :  25
 -6 :  36
 -7 :  49
 -8 :  64
 -9 :  81
-10 : 100

}
