program endian;
uses sysutils;

  type
    TAsBytes  = array[0..7] of byte;
    TAsWords  = array[0..3] of word;
    TAsRecord = record a,b,c,d,e,f,g,h : byte end;

  var
    x : QWord;
    w : TAsWords absolute x;
    y : TAsBytes absolute x;
    z : TAsRecord absolute x;
begin
  writeln('sizeof x:', sizeof( x ), ' ',
	  'bytearray:', sizeof( TAsBytes ), ' ',
	  'words:', sizeof( TAsWords ), ' ',
	  'record:', sizeof( TAsRecord ));

  x := $0011223344556677;
  writeln('x = ', IntToHex( x, 16 ), ' (native)' );
  writeln('  = ', IntToHex( NToLE( x ), 16 ), ' (little endian)' );
  writeln('  = ', IntToHex( NToBE( x ), 16 ), ' (big endian)' );
  writeln('w = ',
	  IntToHex( w[ 0 ], 4 ), IntToHex( w[ 1 ], 4 ),
	  IntToHex( w[ 2 ], 4 ), IntToHex( w[ 3 ], 4 ),
	  ' (word array order)' );
  writeln('y = ',
	  IntToHex( y[ 0 ], 2 ), IntToHex( y[ 1 ], 2 ),
	  IntToHex( y[ 2 ], 2 ), IntToHex( y[ 3 ], 2 ),
	  IntToHex( y[ 4 ], 2 ), IntToHex( y[ 5 ], 2 ),
	  IntToHex( y[ 6 ], 2 ), IntToHex( y[ 7 ], 2 ),
	  ' (byte array order)' );
  writeln('z = ',
	  IntToHex( z.a, 2 ), IntToHex( z.b, 2 ),
	  IntToHex( z.c, 2 ), IntToHex( z.d, 2 ),
	  IntToHex( z.e, 2 ), IntToHex( z.f, 2 ),
	  IntToHex( z.g, 2 ), IntToHex( z.h, 2 ),
	  ' (record order)' );
end.

{

OUTPUT:
  
  x = 0011223344556677 (native)
    = 0011223344556677 (little endian)
    = 7766554433221100 (big endian)
  w = 6677445522330011 (word array order)
  y = 7766554433221100 (byte array order)
  z = 7766554433221100 (record order)

}
