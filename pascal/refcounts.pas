{$mode objfpc}
program refcounts;

  type
    IRef = interface
      procedure Boop;
    end;
    TObj = class (IRef)
      constructor Create( name : string );
      // these are the IUnknown methods to implement :
      function QueryInterface(constref guid : TGuid; out obj ):LongInt; cdecl;
      function _AddRef: longint; cdecl;
      function _Release: longint; cdecl;
      procedure Boop;
    private
      _count : integer;
      _name  : string;
    end;
    
    constructor TObj.Create( name : string );
    begin
      _name := name
    end;
    
    function TObj.QueryInterface(constref guid : TGuid; out obj ):LongInt; cdecl;
    begin
      result := 0;
    end;

    function TObj._AddRef : longint; cdecl;
    begin
      inc( _count );
      WriteLn( 'AddRef: ', _name, '.count = ', _count );
      result := 0;
    end;

    function TObj._Release : longint; cdecl;
    begin
      dec( _count );
      WriteLn( 'Release: ', _name, '.count = ', _count );
      result := 0;
    end;

    procedure TObj.Boop;
    begin
      WriteLn( '<Boop>' );
    end;

    procedure DoSomething( whatever :  IRef );
    begin
      writeln(': --> DoSomething (normal parameter)');
      whatever.boop;
      writeln(':     reassigning local reference to new instance:');
      whatever := TObj.Create( 'C' );
      writeln(': <-- DoSomething');
    end;

    procedure WithConst( const whatever :  IRef );
    begin
      writeln(': --> WithConst');
      whatever.boop;
      writeln(': <-- WithConst');
    end;

    procedure WithVar( var whatever :  IRef );
    begin
      writeln(': --> WithVar');
      whatever.boop;
      writeln(':     reassigning local reference to new instance:');
      whatever := TObj.Create( 'B' );
      writeln(': <-- WithVar');
    end;

var ref : IRef;
begin
  writeln(': --> main');
  writeln(':     Constructing instance.');
  ref := TObj.Create( 'A' );

  writeln(':     Calling DoSomething.');
  DoSomething(ref);
  writeln(':     Back.');

  writeln(':     Calling WithVar.');
  WithVar(ref);
  writeln(':     Back.');

  writeln(':     Calling WithConst.');
  WithConst(ref);
  writeln(':     Back.');

  with IRef(TObj.Create('anonymous1')) do boop;
  DoSomething(TObj.Create('anonymous2'));
  
  writeln(': <-- main');

end.

{ output:
  : --> main
  :     Constructing instance.
  AddRef: A.count = 1
  :     Calling DoSomething.
  AddRef: A.count = 2
  : --> DoSomething (normal parameter)
  <Boop>
  :     reassigning local reference to new instance:
  AddRef: C.count = 1
  Release: A.count = 1
  : <-- DoSomething
  Release: C.count = 0
  :     Back.
  :     Calling WithVar.
  : --> WithVar
  <Boop>
  :     reassigning local reference to new instance:
  AddRef: B.count = 1
  Release: A.count = 0
  : <-- WithVar
  :     Back.
  :     Calling WithConst.
  : --> WithConst
  <Boop>
  : <-- WithConst
  :     Back.
  AddRef: anonymous1.count = 1
  AddRef: anonymous1.count = 2
  <Boop>
  AddRef: anonymous2.count = 1
  : --> DoSomething (normal parameter)
  <Boop>
  :     reassigning local reference to new instance:
  AddRef: C.count = 1
  Release: anonymous2.count = 0
  : <-- DoSomething
  Release: C.count = 0
  : <-- main
  Release: anonymous1.count = 1
  Release: anonymous1.count = 0
  Release: B.count = 0
}
