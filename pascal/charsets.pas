program charsets;
var ch : char; cs : set of char;
begin
  for ch in ['A'..'z'] - ['[','\',']','^','_','`'] + ['0'..'9'] do write(ch);
  writeln;
end.
