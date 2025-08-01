{ successfully renders a purple window on ubuntu with no x/wayland }
program sdl3test;
uses SDL3, sysutils;
var win:PSDL_Window=nil; ren:PSDL_Renderer = nil;
    done : boolean = false;
    e : PSDL_Event = nil;
begin
  new(e);
  if not SDL_Init(SDL_INIT_VIDEO) then begin
    WriteLn('Unable to init SDL3');
    Exit;
  end;
  win := SDL_CreateWindow('Fullscreen', 0,0, SDL_WINDOW_FULLSCREEN);
  ren := SDL_CreateRenderer(win, nil);
  
  WriteLn('SDL3 Initialized with Video');
  WriteLn('win: ', HexStr(win));
  WriteLn('ren: ', HexStr(ren));
  while not done do begin
    SDL_PollEvent(e);
    if (e^.type_ = SDL_EVENT_KEY_DOWN) and (e^.key.key = SDLK_ESCAPE)
      then done := true;
    SDL_SetRenderDrawColor(ren, 128, 0, 128, 255);
    SDL_RenderClear(ren);
    SDL_RenderPresent(ren);
    SDL_Delay(16);
  end;
  SDL_DestroyRenderer(ren);
  SDL_DestroyWindow(win);
  SDL_Quit;
end.
