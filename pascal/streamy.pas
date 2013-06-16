{ just experimenting with streaming components }
{$mode objfpc}
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

var
  stream : TStringStream;
  compy	 : TStreamyComponent;
  name	 : string = '';
  data	 : string = '';
begin
  compy := TStreamyComponent.Create(nil);
  stream := TStringStream.Create(data);

  registerClass(TStreamyComponent);
  
  write('enter a name:');
  readln(name); compy.name := name;
  writeln('okie doke. serializing:');
  compy.id := 1;
  stream.writecomponent(compy);

  compy.id := 2;
  stream.writecomponent(compy);
  writeln('freeing component');
  compy.free;

  writeln('data string:');
  writeln(stream.datastring);
  stream.seek(0, soFromBeginning);
  writeln('loading component from the stream');

  compy := stream.ReadComponent(nil) as TStreamyComponent;
  writeln('hello again, ', compy.name, '. id =', compy.id );

  compy := stream.ReadComponent(nil) as TStreamyComponent;
  writeln('hello again, ', compy.name, '. id =', compy.id );
end.

  