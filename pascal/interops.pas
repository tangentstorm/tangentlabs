{ operator overloading for interfaces }
{$mode objfpc}
program interops;

type
  INum = interface
    function ToInt : Integer;
  end;
  TNum = class ( TInterfacedObject, INum )
    _value : integer;
    constructor Create(aValue : Integer);
    function ToInt : Integer;
  end;

operator >< ( a, b :  INum ) : Integer;
  begin result := a.ToInt * b.ToInt + b.ToInt;
  end;

operator + ( a, b :  INum ) : Integer;
  begin result := a.ToInt * b.ToInt;
  end;

operator explicit ( n : INum ) : Integer;
  begin result := n.ToInt;
  end;

constructor TNum.Create( aValue : Integer );
  begin _value := aValue
  end;

function TNum.ToInt : Integer;
  begin result := _value
  end;

function num(n : Integer) : INum;
  begin result := TNum.Create(n);
  end;

var a, b : INum;
begin
  a := TNum.Create(1);
  b := num(2);
  writeln('custom + operator: ', a + b);
  writeln('custom >< operator: ', a >< b );
  writeln('explicit cast to integer: ', integer(num(3)) );
end.
