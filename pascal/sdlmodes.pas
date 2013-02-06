{$mode objfpc}
PROGRAM sdlmodes;
USES sdl, crt;

  PROCEDURE gsl_pickmode;
  VAR modes : ppsdl_rect;
      i : integer;
  BEGIN
    modes := sdl_listmodes( nil, sdl_fullscreen + sdl_hwsurface );
    if modes = nil then
      writeln('no modes available.')
    else begin
      writeln
    end
  END;

BEGIN
  //sdl_init(sdl_init_video);
  gsl_pickmode;
  readkey;
  //sdl_quit;
END.
