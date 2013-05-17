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
    write( title, ' [' );
    for d in whichdays do write( ' ', d );
    writeln( ' ]');
  end;

  var mwf : TDays = [ mon, wed, fri ];
  var d,w,s  : set of day;
begin

  w := weekdays;              // weekdays
  s := mwf + [sat, sun];      // arbitrary set of days
  writedays( 's:', s);
  writedays( 'w:', w);
  writeln;
  writedays( ' w + s:',  w + s ); // union
  writedays( ' w * s:',  w * s ); // intersection
  writedays( ' w - s:',  w - s ); // difference
  writedays( ' s - w:',  s - w ); // difference
  writedays( 'w >< s:', w><s );   // symmetric difference
  writeln;
  writeln( '  w   <= s: ', w <= s );    // subset?
  writeln( '  mwf <= w: ', mwf <= w );  // subset?
  writeln( '  w   >= s: ', w >= s );    // superset?
  writeln( '  w    = s: ', w = s );     // equal
  writeln( '  w   <> s: ', w <> s );    // not-equal
  writeln( 'mon in mwf: ', mon in mwf); // element-of?
  writeln( 'tue in mwf: ', mon in mwf); // element-of?
  writeln;

end.

{ output :
  
  s: [ mon wed fri sat sun ]
  w: [ mon tue wed thu fri ]

  w + s: [ mon tue wed thu fri sat sun ]
  w * s: [ mon wed fri ]
  w - s: [ tue thu ]
  s - w: [ sat sun ]
  w >< s: [ tue thu sat sun ]

  w   <= s: FALSE
  mwf <= w: TRUE
  w   >= s: FALSE
  w    = s: FALSE
  w   <> s: TRUE
  mon in mwf: TRUE
  tue in mwf: TRUE

}
