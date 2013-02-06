  program array_literals;
    var a : array [ 0 .. 3 ] of char = ( 'a', 'b', 'c', 'd' );
        i : byte;
  begin
    for i := 0 to 3 do writeln( a[ i ] );
  end.
