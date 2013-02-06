{ Q: can we dispatch on the class pointer of an object? }
{$mode objfpc}
program caseclass2;

  type
    Vegetable = class end;
    Mineral   = class end;
    Animal    = class end;
    CVeg = class of Vegetable;
    CMin = class of Mineral;
    CAni = class of Animal;

  function randObj : tobject;
  begin
    case random( 3 ) of
      0	: result := animal.create;
      1	: result := vegetable.create;
      2	: result := mineral.create;
      else result := tobject.create
    end
  end;

  procedure tab; begin write(#9) end;
  
  var obj : TObject;
  var i : integer;
begin
  randomize;
  for i := 1 to 10 do
  begin
    obj := randObj;

    { method 1 : case dispatch on classname string }
    case obj.classname of
      'Animal'	  : write('<animal>');
      'Vegetable' : write('<vegetable>');
      'Mineral'	  : write('<mineral>');
      else          write('<other>')
    end;

    tab;
    
    { method 2 : if statements }
    if obj.classtype = Animal then write('ANIMAL!')
    else if obj.classtype = Vegetable then write('VEGETABLE!')
    else if obj.classtype = Mineral then write('MINERAL!')
    else write('OTHER!');

    {-- failed attempts ---------------------}
    {$IFDEF THIS-DOESNT-WORK}

    case obj.classtype of
      CVeg : write('cVeg');
      CMin : write('cMin');
      CAni : write('cAni');
      else   wrineln('Other');
    end;
  
    if obj.classtype = CVeg then write('cVeg');
    {$ENDIF}
    
    writeln;
  end
end.
