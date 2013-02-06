{$mode objfpc }
program arg_order;

  function arg( v : integer ) : integer;
  begin
    writeln( 'arg( ', v, ' );' );
    result := v;
  end;

  procedure call( a, b : integer );
  begin
    writeln( 'call( ', a, ', ', b, ' );' );
  end;

begin
  call( arg( 1 ), arg( 2 ));
end. { arg_order }
