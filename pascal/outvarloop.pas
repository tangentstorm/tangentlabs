// Q: can an 'out' parameter be used as a loop index?
// A: no, but you can use 'result' in a function.
//
// (i don't know why you'd actually want to do this,
// but it came up in the irc channel)

{$mode delphi}
program outvarloop;

function test_func : integer;
  begin
    for result := 0 to 3 do writeln('test_func:', result);
  end;

procedure test_proc(out result : integer);
  begin
    for result := 0 to 3 do writeln('test_proc:', result);
  end;

var x : integer;
begin
  writeln(test_func);
  test_proc(x); writeln(x);
end.