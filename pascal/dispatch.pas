{--------------------------------------------------------------
  TastyPets : Experiments in type-based dispatch.
 --------------------------------------------------------------}
{$mode objfpc}
program tastypets;

{--------------------------------------------------------------
  We begin by collecting a variety of small animals to
  use in our scientific testing.
 --------------------------------------------------------------}
type
  TPet = class (TObject)
    _name : string;
    property name:string read _name;
    constructor create( newName : string );
  end;

constructor TPet.create( newName : string );
  begin
    _name := newName;
  end;

type
  TPuppyDog = class ( TPet ) end;
  TKittyCat = class ( TPet ) end;
  THamster = class ( TPet ) end;
  TFrog = class ( TPet ) end;

{--------------------------------------------------------------
  We then proceed to serve an example of each type
  to various monsters, and carefully note their
  reactions.
 --------------------------------------------------------------}
var dog, cat, hamster, frog : TPet;
procedure PrepareBuffet;
  begin
    dog := TPuppyDog.Create('Sparky');
    cat := TKittyCat.Create('Quaxo');
    hamster := THamster.Create('Goldie');
    frog := TFrog.Create('Mr Jumpy');
  end;

type
  TReaction = ( kYUCK,  kYUM, kNOEAT, kRAAR );
  TMonster = class
    function Taste( p : TPet ) : TReaction; virtual; abstract;
    function TasteTest : boolean; virtual; abstract;
  end;

{--------------------------------------------------------------
  The goal of our research is to find a monster
  that reacts to pets in the following ways:
--------------------------------------------------------------}
type
  TGoalMonster = class (TMonster)
    function Taste( p : TPet ) : TReaction;
      override; // we need this for TMonster
      overload; // wrnhhhhh
    function Taste( d : TPuppyDog ) : TReaction;
    function Taste( c : TKittyCat ) : TReaction;
    function Taste( h : THamster )  : TReaction;
    function TasteTest : boolean; override;
  end;

// the monster should love to eat puppy dogs
function TGoalMonster.Taste( d : TPuppyDog ) : TReaction;
  begin
    writeln( d.name, ' taste good! yum!' );
    result := kYUM;
  end;
  
// it should hate to eat kitty cats
function TGoalMonster.Taste( c : TKittyCat ) : TReaction;
  begin
    writeln( c.name, ' taste bad! yuck!' );
    result := kYUCK;
  end;
  
// it should never eat hamsters
function TGoalMonster.Taste( h : THamster ) : TReaction;
  begin
    writeln( 'no eat ', h.name, '! ', h.name, ' my friend!' );
    result := kNOEAT;
  end;
  
// anything else should throw it into a rage:
function TGoalMonster.Taste( p : TPet ) : TReaction;
  begin
    writeln('no want ', p.name, '! raaar!');
    result := kRAAR;
  end;

// To summarize:
function TGoalMonster.TasteTest : boolean;
  begin
    result := (Taste(dog) = kYUM)
      and (Taste(cat) = kYUCK)
      and (Taste(hamster) = kNOEAT)
      and (Taste(frog) = kRAAR)
  end;
  
{ Unfortunately, TGoalMonster didn't work as expected.
  It was unable to distinguish the various types of
  animal, so every potential meal simply enraged the
  monster. It eventually starved to death, after nearly
  destroying the entire lab.
  
 Thankfully, we were able to salvage enough of its
 genetic material to create some working prototypes. }

{--------------------------------------------------------------
  Our first successful attempt involved adding a CASE
  statement to the creature's brain.
--------------------------------------------------------------}
 
type
  TCaseMonster = class( TGoalMonster )
    function Taste( pet : TPet ) : TReaction; override;
  end;

function TCaseMonster.Taste( pet : TPet ) : TReaction;
  begin
    // case ( class of p ) of  <- nope :/
    { There doesn't seem to be any special syntax to
      detect a subtype and dispatch to it, but you
      can manually get the name or use the 'is'
      operator. Either way, if you want to dispatch
      to a type-specific function, you need to use the
      'as' operator to cast it. }
    case pet.ClassType.ClassName of
      'TPuppyDog' : result := self.Taste( pet as TPuppyDog );
      'TKittyCat' : result := self.Taste( pet as TKittyCat );
      'THamster'  : result := self.Taste( pet as THamster );
    else
      result := inherited Taste(pet)
    end
  end;
  
  
{--------------------------------------------------------------
  Our next attempt involved using a swarm of helper viruses
  to make each animal's flavor more distinctive.
--------------------------------------------------------------}
type
  THelpMonster = class( TGoalMonster )
    function Taste( pet : TPet ) : TReaction; override;
  end;
  TStrongerFlavor = class helper for TPet
    function GetEatenBy( m : THelpMonster ) : TReaction; overload;
  end;
  TPuppyDogFlavor = class helper(TStrongerFlavor) for TPuppyDog
    function GetEatenBy( m : THelpMonster ) : TReaction; overload;
  end;
  
{ unfortunately, the animals would only adapt the 'rage' flavor: }
function TStrongerFlavor.GetEatenBy( m : THelpMonster ) : TReaction;
  begin
    writeln( name, ' enrages the monster.');
    result := kRAAR
  end;
  
{ Attempting to customize the virus for the individual animals proved
  fruitless. We could have modified their brains using our earlier
  CASE statement technology, but this would have just made THelpMonster
  a more expensive version of TCaseMonster. }
function TPuppyDogFlavor.GetEatenBy( m : THelpMonster ) : TReaction;
  begin
    result := kYUM
  end;

function THelpMonster.Taste( pet : TPet ) : TReaction;
  begin
    result := pet.GetEatenBy(self);
  end;
  

{-- test runner -----------------------------------------------}

procedure Test(m:TMonster);
  begin
    writeln('-------------------------------');
    writeln('testing ', m.ClassType.ClassName );
    writeln('-------------------------------');
    if m.TasteTest then
      begin
        writeln('result: PASSED!');
        m.Free
      end
    else
      begin
        writeln('result: FAILED!');
        m.Destroy // Tragic, yes, but it keeps our children safe.
      end;
    writeln;
  end;
  
begin
  PrepareBuffet;
  Test(TGoalMonster.Create);
  Test(TCaseMonster.Create);
  Test(THelpMonster.Create);
end.
{ output:
  
  -------------------------------
  testing TGoalMonster
  -------------------------------
  no want Sparky! raaar!
  result: FAILED!
  
  -------------------------------
  testing TCaseMonster
  -------------------------------
  Sparky taste good! yum!
  Quaxo taste bad! yuck!
  no eat Goldie! Goldie my friend!
  no want Mr Jumpy! raaar!
  result: PASSED!

  -------------------------------
  testing THelpMonster
  -------------------------------
  Sparky enrages the monster.
  result: FAILED!
}
