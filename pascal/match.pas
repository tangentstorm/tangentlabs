{-
  Another attempt to do type-based dispatch by way
  of try..except. It works once, but next time, it crashes. :/
-}
{$mode objfpc}{$macro on}
program match;
uses sysutils;

{ macros to make the syntax work }
  {$define match := try raise}
  {$define against := except}
  {$define when := on}

type
  TAnimal     = class end;
  TVegetable  = class end;
  TMineral    = class end;

procedure dispatch( obj : TObject );
  begin
    write('    ');
    match obj against
     when TAnimal do writeln('animal!');
     when TVegetable do writeln('vegetable!');
     when TMineral do writeln('mineral!');
    end
  end;

var
  objects : array[0..2] of TObject;
  i	  : byte;
begin
  objects[0] := TAnimal.Create;
  objects[1] := TVegetable.Create;
  objects[2] := TMineral.Create;

  writeln('--| first time works! ');
  dispatch( objects[ 0 ]);

  writeln('--| second time crashes. :( ');
  dispatch( objects[ 0 ]);

end.

{ output:

  --| first time works!
      animal!
  --| second time crashes. :(
  An unhandled exception occurred at $0000000000400229:
  Exception object An unhandled exception occurred at $0000000000402523:
  EAccessViolation: Access violation
    $0000000000402523

}