program StringPlusInt;
uses variants;
var s,i : variant;
begin
  s := 'abc';
  i := 123;
  writeln(s+i);
end.
{ output:
  An unhandled exception occurred at $000000000045E048:
  EVariantError: Invalid variant type cast
    $000000000045E048
    $000000000045FD1E
}