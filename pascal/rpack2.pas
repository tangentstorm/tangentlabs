{$IFDEF PACK1}  {$packrecords  1}      {$MESSAGE PACKRECORDS=1}       {$ENDIF}
{$IFDEF PACK2}  {$packrecords  2}      {$MESSAGE PACKRECORDS=2}       {$ENDIF}
{$IFDEF PACK4}  {$packrecords  4}      {$MESSAGE PACKRECORDS=4}       {$ENDIF}
{$IFDEF PACK8}  {$packrecords  8}      {$MESSAGE PACKRECORDS=8}       {$ENDIF}
{$IFDEF PACK16} {$packrecords 16}      {$MESSAGE PACKRECORDS=16}      {$ENDIF}
{$IFDEF PACKD}  {$packrecords DEFAULT} {$MESSAGE PACKRECORDS=DEFAULT} {$ENDIF}
{$IFDEF PACKC}  {$packrecords C}       {$MESSAGE PACKRECORDS=C}       {$ENDIF}
{$IFDEF PACKN}  {$packrecords NORMAL}  {$MESSAGE PACKRECORDS=NORMAL}    {$ENDIF}

{$mode objfpc}
program PackRecords;


type generic TWriter<T> = class
  type TFile = file of T;
  class procedure dump(typename : string); 
end;

class procedure TWriter.dump(typename : string);
  var r : T; f : TFile;
begin
  Assign( f, 'rpack2.' + typename + '.dat' );
  ReWrite( f );
  r.cc := $CCCCCCCC;
  { 6 chars * 6 = 36 }
  r.s1 := 's1s1s1' + 's1s1s1' + 's1s1s1' + 's1s1s1' + 's1s1s1' + 's1s1s1' ;
  { 6 chars * 4 = 24 }
  r.s2 := 'S2S2S2' + 'S2S2S2' + 'S2S2S2' + 'S2S2S2' ;
  Write( f, r );
  Close( f );
end;
  

type
  TRecC12 = record
	      cc : cardinal;
	      s1 : string[36];
	      s2 : string[24];
	    end; 
  TRecC21 = record
	      cc : cardinal;
	      s2 : string[24];
	      s1 : string[36];
	    end; 
  TRec1C2 = record
	      s1 : string[36];
	      cc : cardinal;
	      s2 : string[24];
	    end; 

type
  TWriteC12 = specialize TWriter<TRecC12>;
  TWriteC21 = specialize TWriter<TRecC21>;
  TWrite1C2 = specialize TWriter<TRec1C2>;

begin
  TWriteC12.dump('a-c12');
  TWriteC21.dump('b-c21');
  TWrite1C2.dump('c-1c2');
end.

{ run via ./rpack2.sh see rpack2.log for output }
  