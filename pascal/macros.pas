{ free pascal lets you define simple macros. (no parameters though) }
program macros;
  {$macro on}
  {$define w:=writeln}
begin
  w('hello world');
end.
