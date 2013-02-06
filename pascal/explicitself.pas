{$mode objfpc}
program explicitself;
{ q : do we need to use "self" everywhere?}
{ a : nope, it's optional }

type
  C = class
  private
    x : Integer;
  public
    constructor new(i:integer);
  end;
  
  constructor C.new(i:integer);
  begin
    writeln('old self.x = ', x);
    x := i;
    writeln('new self.x = ', x);
  end;
  
var
  aC : C;
begin
  aC := C.new(2);
  writeln('done.');
end.