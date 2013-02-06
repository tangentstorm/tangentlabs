program generics_without_class;

{
| Question: can we use "generic" with "object" and "record"
| in addition to the more popular "class" ?
|
| Answer : Yes! Like so:
}

type
  generic GObj<T> = object
    value : T;
  end;

type
  generic GRec<T> = record
    value : T;
  end;

{
| Note that the `generic` keyword precedes the type identifier,
| not the 'object' or 'record' keyword
| Presumably, this alerts the parser to expect the <T>, which
| would otherwise be a syntax error.
}


{
| In fact, the above code works out of the box, whereas the
| class version requires setting $mode to `ObjFPC` (or `Delphi`)
}
// type
//   generic GClass<T> = class
//   end;

{
| To instantiate one, we first need the `specialize` keyword,
| which works with either the `type` or `variable` keyword:
}
type
  TNum = specialize GObj<Double>; 
var
  numObj : TNum;
  intObj : specialize GObj<Integer>;
  strRec : specialize GRec<String[ 255 ]>;
         
begin
  numObj.value := 0.123;
  intObj.value := 4321;
  strRec.value := 'abcd';
  writeln;
  writeln( 'num: ', numObj.value );
  writeln( 'int: ', intObj.value );
  writeln( 'str: ', strRec.value );
  writeln;
end.
