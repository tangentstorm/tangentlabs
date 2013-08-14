// q: will two arrays declared in sequence be arranged in sequence
//    in ram, and if so, can you overflow from one to another?
//
// a: nope.

program overflow;
  type
    char8 = array[0..7] of char;
    charF = array[0..15] of char;
  var
    head, tail : char8;
    hexits     : charF = '0123456789ABCDEF';
    p	       : ^charF;
begin
  tail := '';
  head := '';
  move(hexits, head, 16);

  writeln('head: ', head);
  writeln('tail: ', tail);

  p := @head;
  writeln('16 chars, starting at @head: ', p^);
end.

{ output
-----------------------------
  head: 01234567
  tail:
  16 chars, starting at @head: 0123456789ABCDEF
-----------------------------}
