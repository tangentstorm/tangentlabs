{ just experimenting with streaming components }
{$mode objfpc}{$H+}
program streamy;
uses classes, lresources;
  
type
  TStreamyComponent = class (TComponent)
    private
      _ID   : integer;
      _name : string;
    published
      property ID : integer read _ID write _ID;
      property name : string read _name write _name;
    end;


type
  TLoadFactory = class
    procedure LoadTStreamy(	      
		      aReader	      : TReader;
		const aClassname      : String;
		  var aComponentClass : TComponentClass );
  end;
  procedure TLoadFactory.LoadTStreamy(
		      aReader	      : TReader;
		const aClassname      : String;
		  var aComponentClass : TComponentClass );
  begin
    writeln('about to read:', aClassName );
    aComponentClass := TStreamyComponent;
  end; { just }
    
						    
var
  LoadFActory	       : TLoadFactory;
  OnFindComponentClass : TFindComponentClassEvent; 
  stream	       : TStringStream;
  before	       : TStreamyComponent;
  after 	       : TComponent;
  name		       : string = '';
  data		       : string = '';
begin
  OnFindComponentClass := @LoadFactory.LoadTStreamy;
  before := TStreamyComponent.Create(nil);
  stream := TStringStream.Create(data);

  registerClass(TStreamyComponent);
  
  write('enter a name:');
  readln(name); before.name := name;
  writeln('okie doke. serializing:');
  before.id := 1;
  stream.writecomponent(before);

  before.id := 2;
  WriteComponentAsTextToStream(stream, before);
  writeln('freeing component');
  before.free;

  writeln('data string:');
  writeln(stream.datastring);
  stream.seek(0, soFromBeginning);
  writeln('loading component from the stream');

  before := stream.ReadComponent(nil) as TStreamyComponent;
  writeln('hello again, ', before.name, '. id =', before.id );

  ReadComponentFromTextStream(stream, after, OnFindComponentClass);
  with after as TStreamyComponent do
    writeln('hello again, ', name, '. id =', id );
end.

  