{$mode objfpc}{$i xpc.inc}
program clipdemo;
  uses xpc, kvm, kbd, stri;

type
  TVec2	 = record
	     x, y : word
	   end;	  
  TPoint = TVec2;
  TRect	 = record
	     x, y, w, h	: word
	   end;
var
   clip	 : TRect = ( x : 5; y : 5; w : 10; h : 10 );
   trans : TVec2 = ( x : 0; y : 0 );
   scale : TVec2 = ( x : 5; y : 1 );

procedure WriteStr( s : string );
  var i : word; x, y : word;
  begin
    for i := 1 to length(s) do
      begin
	x := wherex - trans.x;
	y := wherey - trans.y;
	if (x >= clip.x) and
	  (x <= clip.x + clip.w) and
	  (y >= clip.y) and
	  (y <= clip.y + clip.h)
	then kvm.work.emit(s[i])
	else pass // kvm.work.emit('.')
      end
  end;

const cellw = 10; cellh = 1;
procedure drawgrid; 
  var
    draw  : TPoint;
    x, y  : integer;
  begin
    for y := 0 to 15 do for x := 0 to 15 do
      begin
	bg('k'); fg('w');
	draw.x := x; draw.y := y;
	draw.x += trans.x; draw.y += trans.y;
	draw.x *= scale.x; draw.y *= scale.y;
	gotoxy( draw.x, draw.y );
	WriteStr( lpad(hex(y * 16 + x), 2, '0') + ':');
	fg( x ); bg( y ); WriteStr('x' );
      end;
    bg('k'); fg('w'); 
    // writeln('wherex:', whereX, 'whereY:', whereY);
    writeln;
  end;

procedure drawframe;
  var y : word;
  begin
    gotoxy( clip.x, clip.y ); write('+', chntimes('-', clip.w-1 ), '+');
    for y := 1 to clip.h - 1 do begin
      gotoxy( clip.x, clip.y + y ); write('|');
      gotoxy( clip.x+ clip.w, clip.y + y ); write('|');
    end;
    gotoxy( clip.x, clip.y + clip.h ); write('+', chntimes('-', clip.w-1 ), '+');
  end;

var done : boolean = false;
begin
  kvm.ClrScr;
  repeat
    drawgrid;
    drawframe;
    case readkey of
      kbd.RIGHT : begin clrscr; clip.x := min( clip.x + 1, kvm.width - clip.w )  end;
      kbd.LEFT  : begin clrscr; if clip.x <= 1 then clip.x := 0 else dec(clip.x) end;
      kbd.UP    : begin clrscr; if clip.y <= 1 then clip.y := 0 else dec(clip.y) end;
      kbd.DOWN  : begin clrscr; clip.y := min( clip.y + 1, kvm.height - clip.h ) end;
      ^C, kbd.ESC : done := true;
      else pass
    end
  until done;
end.
