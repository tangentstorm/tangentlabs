{ Q : Is the underscore by itself a valid identifier?
  A : yes. }

program underscore;
var _ : string = '''_''';
begin
  writeln('_ = ', _, '.');
end.

{ output:
---------
_  = '_'
--------}
