{
  adapted from http://www.freepascal.org/docs-html/rtl/typinfo/getproplist.html
  and http://www.blong.com/Conferences/BorConUK98/DelphiRTTI/CB140.htm#HowDoWeGetRTTI
}
{$mode delphi}
program rttidemo;
uses typinfo, classes;


  Const TypeNames : Array [TTYpeKind] of string[15] =
    ('Unknown','Integer','Char','Enumeration',
     'Float','Set','Method','ShortString','LongString',
     'AnsiString','WideString','Variant','Array','Record',
     'Interface','Class','Object','WideChar','Bool','Int64','QWord',
     'DynamicArray','RawInterface',

     'procedure', 'ustring','uchar', 'helper', 'file','classref','pointer'
     );

type
  TWhatever = class
    protected
      _int : integer;
      _OnChange : TNotifyEvent;
      procedure SetInt(value : integer);
    published
      property int : integer read _int write SetInt;
      property OnChange : TNotifyEvent write _OnChange;
    end;

procedure TWhatever.SetInt(value : integer);
  begin
    _int := value;
    if assigned(_OnChange) then _OnChange(self);
  end;

var
  obj : TWhatever;
  PT  : PTypeData;
  PI  : PTypeInfo;
  I,J : Longint;
  PP  : PPropList;

begin
  obj := TWhatever.Create;
  PI:=TypeInfo(TWhatever);
  PT:=GetTypeData(PI);
  Writeln('count : ',PT^.PropCount);
  GetMem (PP,PT^.PropCount*SizeOf(Pointer));
  J:=GetPropList(PI,tkAny,PP);
  Writeln('Ordinal property Count : ',J);
  for I:=0 to J-1 do
    with PP^[i]^ do begin
      write('Property ',i+1:3,': ', name:30);
      writeln('  Type: ',TypeNames[typinfo.PropType(obj,Name)]);
    end;
  FreeMem(PP);
  obj.Free;
end.
