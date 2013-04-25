{$MODE OBJFPC}
program PlusEq;
type
  TFoo=class
    private
      FBar:integer;
    public
    property Bar:integer read FBar write FBar;
  end;
var
  foo:TFoo;
 
begin
  foo:=TFoo.Create;
  foo.Bar:=foo.Bar+1;
  foo.Bar+=1; { <- fails to compile: requires a variable }
  foo.Free;
end.
{ example pointed out by Payl on #fpc }
