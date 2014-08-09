uses kbd;
begin
  writeln('this should ignore ^C but halt on ^G');
  repeat until readkey = ^G;
end.
