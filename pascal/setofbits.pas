// Q: can you create a set of booleans? (asked in IRC)
// A: yes.
program setofbits;
  var opt : boolean; options: set of boolean;
begin
  options := [true, false];
  for opt in options do writeln(opt);
end.

{ output:
  ------
  FALSE
  TRUE
}