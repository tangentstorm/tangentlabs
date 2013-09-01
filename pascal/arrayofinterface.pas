{$mode objfpc}{$H+}
program arrayofinterface;
uses variants;
  
type
  IStr = interface (IUnknown)
    function ToString : string;
  end;
  TStr = class( TInterfacedObject, IStr )
    private
      str : string;
    public
      constructor Create( s : string );
      function ToString : string; override;
    end;
  vars = array of variant;

constructor TStr.Create( s : string );
  begin
    self.str := s
  end;

function TStr.ToString : string;
  begin
    result := self.str
  end;

function MkVars( args : array of variant ) : vars;
  var i : cardinal;
  begin
    setlength(result, length(args));
    for i := 0 to length(args)-1 do
      result[i] := args[i]
  end;

function str(s : string) : IStr;
  begin
    result := TStr.Create(s)
  end;

var
  items	: Vars;
  item	: IStr;
begin
  items := MkVars([str('a'), str('b'), str('c')]);
  for item in items do writeln(item.ToString)
end.

{ output
------
a
b
c
------
}
