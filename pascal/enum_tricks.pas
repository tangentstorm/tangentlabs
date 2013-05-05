{ enumerated types, ranges, and sets }
program enum_tricks;
type
  Day	= (mon, tue, wed, thu, fri, sat, sun);
  TDays	= set of Day;
const
  weekdays = [ mon .. fri ]; 
  
procedure writedays( title : string; whichdays : TDays );
  var d : Day;
  begin
    writeln( title );
    for d in whichdays do write( '  ', d );
    writeln;
  end;

var mwf : TDays = [ mon, wed, fri ];
begin
  writedays( 'all days:', [low(day) .. high(day)]);
  writedays( 'weekdays:', weekdays );
  writedays( 'weekend:',  [ sat, sun ]);
  writedays( 'MWF:', mwf  );
  writedays( 'MWF + weekend :', mwf + [ sat, sun ]);
  writedays( 'weekdays but not MWF', weekdays - mwf );
end.

{ output :
  all days:
    mon  tue  wed  thu  fri  sat  sun
  weekdays:
    mon  tue  wed  thu  fri
  weekend:
    sat  sun
  MWF:
    mon  wed  fri
  MWF + weekend :
    mon  wed  fri  sat  sun
  weekdays but not MWF
    tue  thu
}
