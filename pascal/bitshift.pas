{$MODE OBJFPC}
program bitshift;
{ Q: how do the shift operators work? }

var
  b : byte     = $80;  // 1000 0000
  s : shortint = $80;
  i : byte;
begin  
  writeln(4 shl 1);  // => 8
  writeln(4 shr 1);  // => 2
  writeln(-4 shl 1); // => -8
  writeln(-4 shr 1); // => 9223372036854775806

  writeln(b);        //  128
  writeln(s);        // -128
  writeln(s shl 1);  // -256

  for i := 0 to 8 do begin
    writeln('byte(1 shl ', i, ')=', byte(1 shl i));
  end;
  writeln('---');
  for i := 0 to 8 do begin
    writeln('byte($FF shl ', i, ')=', byte($FF shl i));
  end;
  writeln('---');
  for i := 0 to 8 do begin
    writeln('byte($FF shr ', i, ')=', byte($FF shr i));
  end;
end. 