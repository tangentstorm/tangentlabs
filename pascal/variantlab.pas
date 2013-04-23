{$mode objfpc}
program variantlab;
uses variants, typinfo;

type
  IObj = interface
    function ClassName : String;
  end; 
  TObj = class( TInterfacedObject, IObj )
    function ClassName : String;
  end;
  TABC = ( abc_a, abc_b, abc_c );

  { TObject.ClassName is a class method, and class
    methods can't be used in interfaces. }
function TObj.ClassName : string;
begin
  result := inherited ClassName;
end; { TObj.ClassName }
  
procedure inspect( s : string; v :  variant );
begin
  writeln( s, ' -> ', VarTypeAsText(VarType( v )), ' ', v )
end;
  
var
  v   : variant;
  o   : IObj;
  inf : PTypeInfo;
begin
  
  inspect( '1', 1 );
  inspect( '256', 256 );
  inspect( '1.0', 1.0 );
  inspect( '''hello''', 'hello');
  inspect( 'abc_a', abc_a );
  o := TObj.Create;
  inspect( '<TObj>', o );

//  write( VarTypeAsText(VarType( v )), ' ');
//  try writeln( o.ClassName )
//  except writeln( '??');
//  end;

end.
