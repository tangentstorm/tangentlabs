{ Q : what happens when you write a record to stdout? }
{ A : not possible. freepascal does offer a TStream feature though }
program writerecord;

type
  TMsg	 = class( TObject ) { class and object both fail too }
    fname : string[ 32 ];
    lname : string[ 32 ];
    age   : integer;
  end;	 
  
var
  msg : TMsg; 
begin
  msg.fname := 'fred';
  msg.lname := 'tempy';
  msg.age := 76;

{  write( msg );}
  writeln( msg.tostring ); 
  
end.