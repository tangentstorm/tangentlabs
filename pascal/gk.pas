{$mode objfpc}
program gk;
begin
  writeln('[gk: this program does nothing]')
end.

{ The ideawas to see if we could use generics (g) + constants (k)
  together to make something like schemas from extended ISO pascal,
  but I couldn't find a way to do it. }
 
type generic GArray <Lo,Hi,T>
     = record
	 data : array [ lo .. hi ] of T;
       end;

{ Free pascal used to let you create variables/constants with the
  same name as a type, so I thought it might be possible to confuse
  the generics system to allow passing in constants as parameters.
  But as of 2.7.1, this overloading ability seems to have been
  removed. }
type one = integer;  const one =  1;
type ten = integer;  const ten = 10;
type TInts = specialize GArray<one, ten, integer>;
var ints : TInts;
begin
  writeln( 'low:', low( ints ), 'high:', high( ints ));
end.
