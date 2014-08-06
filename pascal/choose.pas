// A simple interactive demo using the old CRT unit.

{$mode delphi}
program choose;
uses crt;
  
function askYN( question : string ) : boolean;
  var done : boolean;
  begin
    repeat
      done := true;
      textattr := lightgreen;
      write(question, ' ');
      textattr:=green;
      write('[y/n]');
      case readkey of
	'y','Y'	: result := true;
	'n','N'	: result := false;
	else done := false;
      end;
      textattr:=white;
      writeln;
    until done;
  end;
  
var i : integer;
begin
  clrscr;
  if askYN('Want to do some counting today?') then
    begin
      writeln('excellent!');
      textattr:=yellow;
      for i := 1 to 100 do begin
	write(i : 3, ' ');
	if i mod 10 = 0 then writeln;
      end;
    end
  else begin textattr:=red; writeln('too bad.') end;
  normvideo; //reset color
end.
