{$mode objfpc}
program forky;
uses baseunix;

function tobit(n : longint):byte; begin result := ord(n>0) end;

var n : longint = 0;
begin
  n := n << 1 + tobit(fpfork);
  n := n << 1 + tobit(fpfork);
  writeln(n);
end.
{ output:

3
1
2
0

}
