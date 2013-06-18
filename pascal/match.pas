{-
  Type-based dispatch macros for free pascal.
  ------------------------------------------------
  Copyright 2013 Michal J Wallace.
  Avaliable for use under the MIT/X11 License.
  ------------------------------------------------

  The present file introduces a set of macros that
  provide a clean, user-friendly syntax for type
  dispatch:

    given instance match
      when TClassA do something;
      when b : TClassB do SomethingElse
    end;

  ------------------------------------------------
  Explanation
  ------------------------------------------------

  The traditional approach to this problem in pascal
  was to use a case statement with a variant record
  (a record whose fields change based on a special
  tag field).
  
  Variant records are still supported in the borland-
  style dialects, but you can't use the syntax with
  classes. If you want a case statement for classes,
  you have to make a tag field in your base class
  and manually set the value in each descendant class.

  Or, you can do a bunch of:

     if instance is TClassA then
       with instance as TClassA do
         something
     else if instance is TClassB then ...
  
  The macros implemented here translates to:

     try
       raise Clone(instance)
     except
       on TClassA     do something
       on b : TClassB do somethingElse(b)

  The cloning procedure is necessary because exception
  objects are garbage collected, and we don't want that.

-}
{$mode objfpc}{$macro on}
program match;
uses sysutils;

{-- dispatch system -----------------------------------}
  
  function Clone(obj : TObject) : TObject;
    var givenClass : TClass; o,p : pointer;
    begin
      givenClass := obj.ClassType;
      p := GivenClass.NewInstance;
      result := GivenClass.InitInstance(p);
      move(PPointer(obj)^, PPointer(result)^, GivenClass.InstanceSize);
    end;

{ macros to make the syntax work }
  {$define given := try raise Clone( }
  {$define match := ) except }
  {$define when	 := on}


{-- example ---------------------------------------------}

type
  TAnimal     = class species : string;
    constructor Create( _species : string );
  end;
  TVegetable  = class
    brand : string;
    constructor Create( _brand : string );
  end;
  TMineral    = class
    name : string;
    constructor Create( _name : string );
  end;


{-- implementation -- }

constructor TAnimal.Create( _species : string );
  begin
    species := _species
  end;

constructor TVegetable.Create( _brand : string );
  begin
    brand := _brand
  end;

constructor TMineral.Create( _name : string );
  begin
    name := _name
  end;

type
  TObjects = array of TObject;
var
  objects : TObjects;
  i	  : byte;
begin
  randomize;
  objects := TObjects.Create(
	       TAnimal.Create('Dinornis novaezealandiae'),
	       TAnimal.Create('Pterodactylus antiquus'),
	       TAnimal.Create('Glyptodon clavipes'),
	       TVegetable.Create('Green Giant'),
	       TVegetable.Create('Birds Eye'),
	       TMineral.Create('quartz'),
	       TMineral.Create('pyrite'),
	       TMineral.Create('gypsum'));
  for i := 1 to 10 do
    given
      objects[ random(high(objects)) ]
    match
      when animal : TAnimal do
        writeln('animal of species /', animal.species, '/' );
      when veggie : TVegetable do
        writeln('vegetable branded "', veggie.brand, '"');
      when min : TMineral do
        writeln('mineral (', min.name, ')');
    end
end.

{ example output:

  animal of species /Glyptodon clavipes/
  mineral (pyrite)
  vegetable branded "Green Giant"
  animal of species /Pterodactylus antiquus/
  animal of species /Pterodactylus antiquus/
  animal of species /Dinornis novaezealandiae/
  mineral (pyrite)
  animal of species /Pterodactylus antiquus/
  vegetable branded "Birds Eye"
  animal of species /Pterodactylus antiquus/
}
