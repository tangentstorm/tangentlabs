{$mode objfpc}
program refcounts;

  type
    IRef = interface
      procedure Boop;
    end; 
    TObj= class (IRef)
      // these are the IUnknown methods to implement :
      function QueryInterface(constref guid : TGuid; out obj ):LongInt; cdecl;
      function _AddRef: longint; cdecl;
      function _Release: longint; cdecl;
      procedure Boop;
    private					 
      count						 : integer;
    end;						 

    function TObj.QueryInterface(constref guid : TGuid; out obj ):LongInt; cdecl;
    begin
      result := 0;
    end;

    function TObj._AddRef : longint; cdecl;
    begin
      inc( count );
      WriteLn( 'AddRef: Count =', count );
      result := count;
    end;

    function TObj._Release : longint; cdecl;
    begin
      dec( count );
      WriteLn( 'Release: Count =', count );
      result := count;
    end;

    procedure TObj.Boop;
    begin
      WriteLn( 'The computer says "boop". Can you say "boop"?' );
    end;

    procedure DoSomething( whatever :  IRef );
    begin
      writeln(': --> DoSomething');
      whatever.boop;
      writeln(': <-- DoSomething');
    end;

var ref : IRef;
begin
  writeln(': --> main');
  writeln(':     Calling Constructor.');
  ref := TObj.Create;
  writeln(':     Calling DoSomething.');
  DoSomething(ref);
  writeln(': <-- main');
end.
  
{ output:
    : --> main
    :     Calling Constructor.
    AddRef: Count =1
    :     Calling DoSomething.
    AddRef: Count =2
    : --> DoSomething
    The computer says "boop". Can you say "boop"?
    : <-- DoSomething
    Release: Count =1
    : <-- main
    Release: Count =0
}
