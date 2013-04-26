{$i xpc.inc}
program ja2pas;
uses xpc, jparse;

procedure Visit( node : JNode );
begin
  write( node.text );
  node.free;
end;

begin
  FileParam;
  with JParser.Create do
    while not eof do visit( Next );
end.
