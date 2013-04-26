{$mode objfpc}
unit jparse;
interface uses jscan;
 
type
  JNode	  = class
    _children : array of JNode;
    _token    : JToken;
    constructor Create( token : jToken );
    procedure AddChild( node : JNode );
    function GetText : String;
    destructor Destroy; override;
    property text : String read GetText;
  end;
  JParser = class
    _scanner : JScanner;
    _root    : JNode;
    constructor Create;
    function Next : JNode;
    property root : JNode read _root;
  end;

implementation

  constructor JNode.Create( token : jToken );
  begin
    SetLength( _children, 0 );
    _token := Token;
  end;

  destructor JNode.Destroy;
    var child : JNode;
  begin
    for child in _children do child.Free;
    _children := Nil;
    _token.Free;
  end;

  procedure JNode.AddChild( node : JNode );
  begin
  end;

  function JNode.GetText : string;
  begin
    result := _token.value;
  end;

  constructor JParser.Create;
  begin
    _scanner := JScanner.Create;
  end;

  function JParser.Next : JNode;
    var token : JToken;
  begin
    token := JToken.Create;
    repeat until _scanner.Next( token ).kind <> jtWhiteSpace;
    result := JNode.Create( token );
  end;

end.
