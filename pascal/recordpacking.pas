{$PACKRECORDS 16}
program PackRecords;
type
  TRec	= record
	    s1 : string[1];
	    s2 : string[2];
	    s3 : string[3];
	    s4 : string[4];
	    s5 : string[5];
	    s6 : string[6];
	    s7 : string[7];
	    s8 : string[8];
	  end; 
  TFile	= file of TRec;
var
  r : TRec;
  f : TFile;
begin
  r.s1 := '1';
  r.s2 := '22';
  r.s3 := '333';
  r.s4 := '4444';
  r.s5 := '55555';
  r.s6 := '666666';
  r.s7 := '7777777';
  r.s8 := '88888888';
  Assign( f, 'recordpacking.dat' );
  ReWrite( f );
  Write( f, r );
  Close( f );
end.

{ output of hexdump -C recordpacking.dat :
  
  00000000  01 31 02 32 32 03 33 33  33 04 34 34 34 34 05 35  |.1.22.333.4444.5|
  00000010  35 35 35 35 06 36 36 36  36 36 36 07 37 37 37 37  |5555.666666.7777|
  00000020  37 37 37 08 38 38 38 38  38 38 38 38              |777.88888888|
  0000002c
}
