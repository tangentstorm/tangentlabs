// a little program i wrote sometime in jun 2013
// to test wrapping behavior when writing to last
// row/column of the display. I expected the cursor
// to wrap, but apparently it doesn't!
program eoltest;
uses kvm;

  procedure clreol;
    var i : byte;
    begin
      writeln;
      write( #27, '[?7l' ); for i := 1 to terminal.w do write('l');
      writeln;
      write( #27, '[?7h' ); for i := 1 to terminal.w do write('h');
      writeln;
    end;
  
begin
  bg('r');
  write('abc'); clreol; writeln;
  bg('k');
  write('abc'); clreol; writeln;
end.