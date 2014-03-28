// q: can we create nested arrays of variants??
// a: yes, but only if we introduce a constructor function
{$mode objfpc}
program nested;
uses variants;

procedure p ( a : array of variant );
  begin
  end;

function f ( a : array of variant ) : variant;
  var v : array of variant; i : integer;
  begin
    setlength(v, length(a));
    for i := low(a) to high(a) do v[i] := a[i];
    result := v
  end;

begin
  // p ([ 1, [ 2, 3 ], 4 ]) fails because  [ 2, 3 ] has type (set of byte)
  f([ 1, f([ 2, 3 ]), 4 ])  // works as expected
end.
