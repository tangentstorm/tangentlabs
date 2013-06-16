{
  Experiment to test whether free pascal could do
  dynamic type dispatch on an argument.

  This isn't possible with the case statement,
  but you can manually check each possible type
  with the 'is' operator. It's not pretty,
  but it works.
}
{$mode objfpc}
program dispatch;

type
  pet = class (TObject)
    _name : string;
    property name:string read _name;
    constructor create( newName : string );
  end;
  dog = class ( pet ) end;
  cat = class ( pet ) end;
  hamster = class ( pet ) end;
  monster = class
    procedure eat( p : pet );
    procedure eat( d : dog );
    procedure eat( c : cat );
  end;

constructor pet.create( newName : string );
  begin
    _name := newName;
  end;

procedure monster.eat( p : pet );
  begin
    // case ( class of p ) of  <- nope :/
    { There doesn't seem to be any special syntax to
      detect a subtype and dispatch to it, but you
      can manually get the name or use the 'is'
      operator. Either way, if you want to dispatch
      to a type-specific function, you need to use the
      'as' operator to cast it. }
    case p.classtype.classname of
      'hamster'	: writeln('monster no eat hamster. hamster friend.');
      else if p is dog then self.eat( p as dog )
      else if p is cat then self.eat( p as cat )
      else writeln( 'monster no want that! raaar!' );
    end
  end;

procedure monster.eat( d : dog );
  begin
    writeln( d.name, ' taste good! yum!' );
  end;

procedure monster.eat( c : cat );
  begin
    writeln( c.name, ' taste bad! yech!' );
  end;

var a, b, c, d : pet; m : monster;
begin
  a := dog.create( 'sparky' );
  b := cat.create( 'felix' );
  c := hamster.create( 'fluffy' );
  d := pet.create( 'some other thing ');
  m := monster.create;
  m.eat( a ); m.eat( b ); m.eat( c ); m.eat( d );
end.
{ output:
  ------
  sparky taste good! yum!
  felix taste bad! yech!
  monster no eat hamster. hamster friend.
  monster no want that! raaar!
}
