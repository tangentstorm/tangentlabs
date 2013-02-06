program packsize;

  type
    textcell = packed record
		 fg, bg	: byte;
		 ch	: word;
	       end;

var cell : textcell;
begin
  writeln( 'the cell is ', sizeof( cell ), ' bytes.');
end.
