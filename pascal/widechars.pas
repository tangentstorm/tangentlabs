// can char literals be used with widechars? (yes.)
program widechars;
  var ch : widechar;
begin
  ch := ^J;  // linefeed
  ch := #65; // 'A'
  ch := #$2200; { the 'forall' symbol }
  writeln(ch);
end.
{ output:
-------
?
-------}
