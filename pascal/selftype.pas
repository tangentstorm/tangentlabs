// This is a technique suggested by sven barth on the
// fpc-pascal mailing list 9/12/2013 when someone asked
// how to return a generic type from a method. I just
// wanted to try it.
{$mode delphi}
program selftype;

type
  GObj<T> = class
    type TSelfType = GObj<T>;
  public 
    data : T;
    constructor Create( _data : T);
    function Clone : TSelfType;
  end;	 

constructor GObj<T>.Create( _data : T );
  begin
    self.data := _data
  end;

function GObj<T>.Clone : TSelfType;
  begin
    result := TSelfType.Create(self.data)
  end;

var a,b : GObj<integer>;
begin
  a := GObj<integer>.Create(12345);
  b := a.Clone;
  WriteLn(b.data)
end.
{output:
----------
12345
----------}
