// q: can we create operators for classes?
// a: yes.
{$mode objfpc}
program classops;

type
  TOpped = class
    x : integer;
    constructor Create(anX : integer);
  end;


constructor TOpped.Create(anX : integer);
  begin
    inherited Create;
    x := anX;
  end;

operator + (a,b: TOpped): TOpped;
  begin
    result := TOpped.Create(a.x + b.x);
  end;


var a, b, c : TOpped;
begin
  a := TOpped.Create(1);
  b := TOpped.Create(2);
  c := a + b;
  WriteLn('a: ', a.x, ', b: ',  b.x, ', c: ', c.x);
  // note that without reference counting, this will likely
  // lead to memory leaks when intermediate values are created:
  c := a + b + a; // original c leaked, as does intermediate sum.
end.

{ -- output:
  a: 1, b: 2, c: 3
  --}
