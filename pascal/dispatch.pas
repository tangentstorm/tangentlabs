{
  experiment to test whether free pascal could do
  dynamic type dispatch on an argument. ( it doesn't )
}
{$mode objfpc}
program dispatch;

  type
    pet = class name : string end;
    dog = class ( pet ) end;
    cat = class ( pet ) end;
    monster = class
      procedure eat( p : pet );
      procedure eat( d : dog );
      procedure eat( c : cat );
    end;

  procedure monster.eat( p : pet );
  begin

    // case ( class of p ) of  <- nope :/

    if p is dog then self.eat( p as dog )
    else if p is cat then self.eat( p as cat )
    else writeln( 'monster no want that! raaar!' );
  end;

  procedure monster.eat( d : dog );
  begin
    writeln( d.name, ' taste good! yum!' );
  end;

  procedure monster.eat( c : cat );
  begin
    writeln( c.name, ' taste bad! yech!' );
  end;


var a, b : pet; m : monster;
begin
  a := dog.create; a.name := 'sparky';
  b := cat.create; b.name := 'felix';
  m := monster.create;
  m.eat( a );
  m.eat( b );
end.