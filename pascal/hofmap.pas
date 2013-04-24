{ higher order functions : map() } 
{$mode objfpc}
program hofmap;

  type
    generic HOF<a,b> = class
    private
      type
        atob = function( _a : a ) : b;
        aofa = array of a;
        aofb = array of b;
    public
      class function map( f : atob; _aa : aofa ) : aofb;
    end;
    
  class function HOF.map( f : atob; _aa : aofa ) : aofb;
    var i : cardinal;
  begin
    SetLength( result, length( _aa ));
    for i := 0 to length( _aa ) - 1 do begin
      result[ i ] := f( _aa[ i ])
    end;
  end;
  
{ apparently, Ord isn't a real function. }
function myord( ch : char ): byte;
begin result := ord(ch);
end;
  
type
  CBHOF = specialize HOF<char, byte>;
var
  c : array of char;
  b : array of byte;
  i : cardinal;
begin
  setlength( c, 4 );
  c[0]:='a'; c[1]:='b'; c[2]:='c'; c[3]:='d';
  b := CBHOF.map( @myord, c );
  for i := 0 to length( b ) - 1 do writeln( b[ i ]);
end.
  
{ output
  ------
  97
  98
  99
  100
}
