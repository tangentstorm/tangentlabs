{$mode objfpc}
program recurse;

  procedure fw( s : string;  b : byte = 0 );
  begin
    if b <= length( s ) then begin
      write( s[ b ]);
      fw( s, b+1 )
    end
  end;

  procedure bw( s : string );
    procedure bw_aux( b	: byte );
    begin
      if b > 0 then begin
	write( s[ b ]);
	bw_aux( b - 1 )
      end
    end;
  begin
    bw_aux( length( s ))
  end;

const str = 'abcdefg';
begin
  fw( str ); writeln;
  bw( str ); writeln;
end.
