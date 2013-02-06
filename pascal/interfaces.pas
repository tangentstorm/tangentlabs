{$mode objfpc}
unit interfaces;
{ Prototype for a generic stream interface, with an
  example implementation using files.

  This unit also demonstrates the idea of limiting
  the interface section to public interfaces while
  moving class details to the implementation section.
}
interface uses sysutils;

  type
    generic stream<a> = interface
      function next( out value : a ) : boolean; { true = success }
      function next : a; { throws exception on failure }
    end;

    text =  specialize stream<char>;
    function open( path : string ) : text;

implementation

  type generic filestream<a> = class( tinterfacedobject,
				     specialize stream<a> )
   private f : file; errcode : int64;
   public
    constructor open( path : string );
    function next( out value : a ) : boolean;
    function next : a;
  end;

  constructor filestream.open( path : string );
  begin
    assign( self.f, path );
    reset( self.f );
  end; { filestream.open }

  function filestream.next( out value : a ) : boolean;
  begin
    if eof( self.f ) then result := false
    else begin
      result := true;
      {  if doing for real, would check the ioresult }
      blockread( self.f, value, sizeof( value ), self.errcode )
    end
  end;

  function filestream.next : a;
  begin
    if not self.next( result ) then begin
      {  if doing for real, would check the error code }
      raise Exception.create( 'end of file' )
    end
  end;

  type charstream = specialize filestream<char>;
 
  function open( path : string ) : text;
  begin
    result := charstream.open( path )
  end;

end.
