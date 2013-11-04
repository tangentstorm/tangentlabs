{$mode iso}
program implicit; { implicit function types? }

procedure callthunk(procedure thunk);
  begin
    thunk;
  end;

procedure hello;
  begin
    writeln('hello');
  end;
  
begin
  callthunk(hello)
end.

{ output:
---------
hello
--------}
