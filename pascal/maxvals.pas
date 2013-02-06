program maxvals;
  const width = 20;
begin
  writeln;
  writeln( 'these change depending on compiler mode:' );
  writeln( '----------------------------------------' );
  writeln( 'maxint:           :', maxint : width );
  writeln( 'high( integer )   :', high( integer ) : width );
  writeln;
  writeln( 'constant, regardless of mode or target: ' );
  writeln( '----------------------------------------' );
  writeln( 'high( int32 )     :', high( int32 ) : width );
  writeln( 'high( int64 )     :', high( int64 ) : width );
  writeln;
  writeln( 'variable, depending on target cpu:' );
  writeln( '----------------------------------------' );
  writeln( 'sizeof( pointer ) :', sizeof( pointer ) : width );
  writeln;
  writeln( 'compile-time definitions:' );
  writeln( '----------------------------------------' );
  {$IFDEF cpu64} writeln( 'cpu64' ); {$ENDIF}
  {$IFDEF cpu32} writeln( 'cpu32' ); {$ENDIF}
  {$IFDEF cpu16} writeln( 'cpu16' ); {$ENDIF}
  writeln;
end.

