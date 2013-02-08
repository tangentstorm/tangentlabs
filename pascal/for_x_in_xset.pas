{$mode objfpc}
{$coperators on}
program for_x_in_xset;

  type
    state  = 0..9;
    states = set of state;
  
  var
    f : states = [];
    a : state;


  procedure dump( s :  states );
  begin
    for a in s do write( a, ' ' );
    writeln;
  end;

  var
    step : byte = 0;
    done : boolean = false;
begin
  repeat
    case step of
      0	: ;
      1	: include( f, 1 );
      2	: f := f + [ 2 ];
      3	: f += [ 2 ]; { becasue of $coperators on }
      4	: f += [ 3, 4 ];
      5	: f -= [ 5 ];
      6	: f += [ 5 ];
      7	: f -= [ 5 ];
    otherwise done:= true
    end;

    write( 'step ', step, ': ' ); dump( f );
    inc( step );
  until done
end.
  