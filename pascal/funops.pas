{$mode objfpc}{$i xpc}
program funops;
uses xpc, variants, cw, chk, sysutils;

type
  TVal = variant;
  IWord = interface end;
  INoun = interface( IWord )  // literals
    function ToInt : Integer;
    function ToStr : string;
  end;
  IName = interface( IWord )  // identifiers
    function n : TStr;
    function v : TVal;
  end;
  IVerb = interface( IWord )
    function go( x : INoun; y : INoun = nil ) : INoun;
  end;
  IAdverb = interface( IWord )
    function go( x : IWord ) : IWord; overload;
  end;
  IConjunction = interface( IWord )
    function uv( u : IVerb; v : IVerb ) : IVerb; overload;
    function un( u : IVerb; n : INoun ) : IVerb; overload;
    function mv( m : INoun; v : IVerb ) : IVerb; overload;
    function mn( m : INoun; n : IVerb ) : IVerb; overload;
  end;
  TVerb = function ( x : INoun; y : INoun = nil ) : INoun of object;
  TConj = function ( x : IVerb; y : IVerb = nil ) : IWord of object;

  TCore = class
    function IDL( x : INoun; y : INoun = nil ) : INoun;
    function IDR( x : INoun; y : INoun = nil ) : INoun;
    function ints( x : INoun; y : INoun = nil ) : INoun;
    function add( x : INoun; y : INoun = nil ) : INoun;
    function sub( x : INoun; y : INoun = nil ) : INoun;
    function mul( x : INoun; y : INoun = nil ) : INoun;
  end;

  TBaseConj = class (TInterfacedObject, IVerb)
    _u,_v : TVerb;
    constructor Create( u, v : TVerb );
    destructor Destroy; override;
    function go( x : INoun; y : INoun = nil ) : INoun; virtual; abstract;
  end;

  TMonoDyadConj = class (TBaseConj)
    function go( x : INoun; y : INoun = nil ) : INoun; override;
  end;

  TAtopConj = class (TBaseConj)
    function go( x : INoun; y : INoun = nil ) : INoun; override;
  end;

  THook = class (TBaseConj)
    function go( x : INoun; y : INoun = nil ) : INoun; override;
  end;

  TFork = class  (TInterfacedObject, IVerb)
    _u, _v, _w : TVerb;
    constructor Create( u, v, w : TVerb );
    destructor Destroy; override;
    function go( x : INoun; y : INoun = nil ) : INoun;
  end;

  TNoun = class (TInterfacedObject, INoun)
    _var : variant;
    constructor Create( aVar : variant );
    destructor Destroy; override;
    function ToInt : integer;
    function ToStr : string;
  end;



constructor TNoun.Create( aVar : variant );
  begin _var := aVar
  end;

destructor TNoun.Destroy;
  begin _var := nil
  end;
  
function TNoun.ToInt : integer;
  begin result := _var
  end;

function TNoun.ToStr : string;
  begin result := _var
  end;
function noun(x :variant) : INoun;
  begin result := TNoun.Create(x)
  end;

operator := ( n : INoun ) : string;
  begin result := n.tostr;
  end;

operator := ( i : integer ) : INoun;
  begin result := noun(i)
  end;

operator := ( n : INoun ) : integer;
  begin result := n.toint;
  end;


{ conjunctions (verb combinators) }

constructor TBaseConj.Create( u, v : TVerb );
  begin _u := u; _v := v;
  end;

destructor TBaseConj.Destroy;
  begin _u := nil; _v := nil;
  end;

{ compose a monad and dyad to create new ambivalent verb }
function TMonoDyadConj.go( x : INoun; y : INoun = nil ) : INoun;
  begin if y = nil then result := _u(x) else result := _v(x, y)
  end;

{ compose two verbs }
function TAtopConj.go( x : INoun; y : INoun = nil ) : INoun;
  begin
    if y = nil
      then result := _u(x)
      else result := _v(x, y)
  end;


{ hooks and forks }

constructor TFork.Create( u, v, w : TVerb );
  begin _u := u; _v := v; _w := w;
  end;

destructor TFork.Destroy;
  begin _u := nil; _v := nil; _w := nil
  end;

function TFork.go( x : INoun; y : INoun = nil ) : INoun;
  begin result := _v(_u(x,y), _w(x,y))
  end;

function THook.go( x : INoun; y : INoun = nil ) : INoun;
  begin result := _v(_u(x,y), x)
  end;
  

{ core verbs }

{ left identity }
function TCore.IDL( x : INoun; y : INoun = nil ) : INoun;
  begin result := x
  end;

{ right identity }
function TCore.IDR( x : INoun; y : INoun = nil ) : INoun;
  begin if y = nil then result:= x else result := y
  end;

{ integers }
function TCore.ints( x : INoun; y : INoun = nil ) : INoun;
  var i,n : integer; a : array of integer;
  begin n:= x.toInt; setlength(a, abs(n));
  if n > 0
    then for i:= 0 to n-1 do a[i] := i
    else for i:= abs(n) downto 1 do a[abs(n)-i] := i;
    result := TNoun.Create(a)
  end;

{ addition }  
function TCore.add( x : INoun; y : INoun = nil ) : INoun;
  begin
    if y = nil
      then raise Exception.Create(' not yet implemented: x+nil. x was: '+ x.tostr)
      else result := noun(integer(x) + integer(y))
  end;

{ subtraction }
function TCore.sub( x : INoun; y : INoun = nil ) : INoun;
  begin
    if y = nil
      then raise Exception.Create(' not yet implemented: x-nil. x was: '+ x.tostr)
      else result := noun(integer(x) - integer(y))
  end;

{ multiplication }
function TCore.mul( x : INoun; y : INoun = nil ) : INoun;
  begin result := noun(integer(x) * integer(y))
  end;
  
type TVars = array of variant;
function vars( vs : array of variant ) : TVars;
  var i : integer;
  begin
    setlength(result, length(vs));
    if length(vs) > 0 then for i := 0 to length(vs)-1 do result[i] := vs[i];
  end;


{ constructors }

function MonadDyad( m, n :  TVerb ) : TVerb;
  begin result := @IVerb(TMonoDyadConj.Create(m, n)).go;
  end;

function Atop( m, n :  TVerb ) : TVerb;
  begin result := @IVerb(TAtopConj.Create(m, n)).go;
  end;

function Fork( u,v,w : TVerb ) : TVerb;
  begin result := @IVerb(TFork.Create(u,v,w)).go;
  end;

function Hook( u,v : TVerb ) : TVerb;
  begin result := @IVerb(THook.Create(u,v)).go;
  end;

var { primitive verbs and combinators }
  add, sub, mul, idl, idr, ints : TVerb;
var { local variabls }
  core : TCore;
  h, f : TVerb;
begin
  core := TCore.Create;
  idl := @core.idl; idr := @core.idr;
  add := @core.add; sub := @core.sub;
  mul := @core.mul;

  chk.equal(1, noun(1));
  chk.equal('2', noun(2).tostr );
  chk.equal(3, idl( 3, 4 ));
  chk.equal(4, idr( 3, 4 ));
  chk.equal(5, add( 2, 3 ));
  chk.equal(6, mul( 2, 3 ));
  chk.equal(7, fork( idl, idl, idl )( 7 ));
  chk.equal(8, sub( 10, 2 ));

  h := hook( idl, add );
  f := fork( add, mul, sub );

  chk.equal( 8, h( 4  ));
  chk.equal(21, f( 5, 2 ));
  core.free;
end.
