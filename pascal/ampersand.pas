// can you use the ampersand by itself as a variable in fpc2.7.1? (no)
// what about underscore? (yes)

{$mode delphi}
program ampersand;
  var &x,_ : integer;
begin
  &x:= 5;
  _:= 2;
  writeln(&x,' ', _);
end.

{ output:
5 2
}

// if i try to use & by itself i get:
// ampersand.pas(6,7) Fatal: Syntax error, "identifier" expected but "," found
