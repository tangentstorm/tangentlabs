program tabfile;
  var c : cardinal; s : string; tab : char;
begin
  assign( input, 'tabfile.tab' );
  reset( input );
  while not eof do
    begin
      readln( c, tab, s );
      writeln( c, '->', s );
    end;
  close( input );
end.