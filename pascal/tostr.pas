{$mode delphi}
program tostr;
uses variants;

procedure WriteVars(vars : array of variant);
  var v : variant;
  begin
    for v in vars do WriteLn( VarToStr( v ))
  end;

begin
  WriteVars([ 1, 2.0, 'three', @WriteVars, 4.567 ])
end.
