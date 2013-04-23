{$mode objfpc}
program variant_tostring;
uses variants;

procedure show( v : variant );
begin
  writeln( v )
end;

var
  o : IUnknown;
begin
  show( 'abc' );
  show( 12345 );
  o :=  TInterfacedObject.Create;
  show( o ); // <- dies here
  writeln( 'done' );
end.

{ output :
  abc
  12345
  An unhandled exception occurred at $000000000045923A :
  EVariantError : Invalid variant type cast
    $000000000045923A
    $0000000000427889
    $0000000000411C07
    $0000000000400378
}