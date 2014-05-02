// can char literals be used with widechars? (yes.)
program widechars;
  var ch : widechar;
begin
  ch := ^J;  // linefeed
  ch := #65; // 'A'
  ch := #$2200; { the 'forall' symbol }
  writeln(utf8encode(ch));
  writeln(utf8encode(#$2208)); { the 'element of'  symbol }
  writeln('∨'); { the 'vel' ('logical or') symbol }
end.
{ output:
-------
∀
∈
∨
-------}
