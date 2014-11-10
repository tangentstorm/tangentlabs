// adapted from algorithms+ data structures = programs by niklaus wirth
program straightinsertion;
const
  s = 'the quick brown fox jumps over the lazy dog'; 
  n = length(s);
var
  a   : array[0..n] of char;
  i,j : byte;
  x   : char;
begin
  // first copy the string over to the array so we can use a[0]
  for i := 1 to n do a[i]:=s[i];
  // now the algorithm, from page 61
  for i := 2 to n do
  begin x := a[i]; a[0] := x; j := i - 1;
    while x{.key} < a[j]{.key} do
      begin a[j+1] := a[j]; j:= j-1
      end;
    a[j+1] := x
  end;
  // now show the results:
  for i := 1 to n do write(a[i]);
  writeln;
end.
// output:
//         abcdeeefghhijklmnoooopqrrsttuuvwxyz
