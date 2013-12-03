// Using multiple interfaces concurrently.
// In this case, two interfaces both expect a method called DoY.
// Since the signatures are the same, there's no conflict.
{$mode delphi}
program multiface;

type
  IXY = interface
    procedure DoX;
    procedure DoY;
  end;
  IYZ = interface
    procedure DoY;
    procedure DoZ;
  end;
  TXYZ = class (TInterfacedObject, IXY, IYZ)
  public
    procedure DoX;
    procedure DoY;
    procedure DoZ;
  end;
  
procedure TXYZ.DoX;
  begin
    WriteLn('X');
  end;
  
procedure TXYZ.DoY;
  begin
    WriteLn('Y');
  end;
  
procedure TXYZ.DoZ;
  begin
    WriteLn('Z');
  end;

var
  xy : IXY;
  yz : IYZ;
begin
  xy := TXYZ.Create;
  xy.DoX;
  xy.DoY;
  WriteLn('-');
  yz := TXYZ.Create;
  yz.DoY;
  yz.DoZ;
end.

{ output:
--------  
X
Y
-
Y
Z
--------}