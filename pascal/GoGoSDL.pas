{$mode objfpc} {$inline on} {$modeswitch autoderef+}

PROGRAM GoGoSDL; USES SDL, CRT;

  CONST
    kScrW = 400;
    kScrH = 300;

  TYPE KeyboardEvent = SDL.TSDL_KeyboardEvent;

  PROCEDURE set_rect ( VAR surf : psdl_rect; x, y, w, h : INTEGER );
    INLINE;
  BEGIN
    new( surf );
    surf.x := x;
    surf.y := y;
    surf.w := w;
    surf.h := h;
  END; { set_rect }
  
  TYPE Image = OBJECT
    surf : psdl_surface;
    PROCEDURE init ( path : pChar );
    PROCEDURE blit( to_surface : psdl_surface; src_rect, dst_rect : psdl_rect );
    PROCEDURE done( );
  END { Image };
  
  PROCEDURE Image.init ( path : pChar );
  BEGIN
    surf := sdl_loadbmp( path );
    IF surf = NIL THEN BEGIN HALT END;
  END { Image.init };
  
  PROCEDURE Image.blit( to_surface : psdl_surface; src_rect, dst_rect : psdl_rect );
  BEGIN 
    sdl_blitsurface( self.surf, src_rect, to_surface, dst_rect );
  END { Image.blit };
  
  PROCEDURE Image.done( );
  BEGIN
    sdl_freesurface( self.surf );
  END { Image.done };
    
  
  PROCEDURE new_rect( VAR surf : psdl_rect; x, y, w, h : INTEGER );
    INLINE;
  BEGIN
    new( surf );
    set_rect( surf, x, y, w, h );      
  END; { new_rect }
  
  FUNCTION gsl_setup( w, h : INTEGER ) : psdl_surface;
  BEGIN
    sdl_init( SDL_INIT_VIDEO );
    result := sdl_setvideomode( w, h, 32, SDL_SWSURFACE ); { + SDL_NOFRAME ); }
    IF result = NIL THEN BEGIN HALT END;
  END { gsl_setup };

  
  TYPE UIEvent = OBJECT END;
  TYPE MouseEvent = OBJECT( UIEvent )
  PUBLIC 
    x, y : INTEGER;
    CONSTRUCTOR mouseup( ex , ey : INTEGER );
    CONSTRUCTOR mousedown( ex , ey : INTEGER );
  PUBLIC 
    screen_x, screen_y, client_x, client_y : INTEGER;
    ctrl_key, shift_key, alt_key, meta_key : BOOLEAN;
    button, buttons : INTEGER;
    // TODO : fill in remaining dom event types
    { 
      readonly attribute                 EventTarget     relatedTarget;
      PROCEDURE initMouseEvent
         DOMString typeArg, 
         boolean canBubbleArg, 
         boolean cancelableArg, 
         views::AbstractView viewArg, 
         long detailArg, 
         long screenXArg, 
         long screenYArg, 
         long clientXArg, 
         long clientYArg, 
         boolean ctrlKeyArg, 
         boolean altKeyArg, 
         boolean shiftKeyArg, 
         boolean metaKeyArg, 
         unsigned short buttonArg,
         in EventTarget relatedTargetArg);
      // Introduced in DOM Level 3:
      DEF getModifierState(in DOMString keyArg) : BIT;
    }
  END;
  
  CONSTRUCTOR MouseEvent.mouseup( ex , ey : INTEGER );
  BEGIN 
    x := ex;
    y := ey;
  END { MouseEvent.mouseup };
  
  CONSTRUCTOR MouseEvent.mousedown( ex , ey : INTEGER );
  BEGIN
    mouseup( ex, ey );
  END { MouseEvent.mouseup };
  
  PROCEDURE main(  );
  VAR
    img              : Image;
    screen           : psdl_surface;
    srcRect, dstRect : psdl_rect;
    evt              : psdl_event;
    user_quit        : BOOLEAN;
    
    PROCEDURE setup( w, h : INTEGER );
    BEGIN
      screen := gsl_setup( w, h );
      img.init( 'blueguy.bmp' );      
      new_rect( srcRect, 0, 0, w, h );
      new_rect( dstRect, 0, 0, w, h );
      NEW( evt );
    END { initialize };

    PROCEDURE slide_img( );
    BEGIN
      
      dstRect.x += 1;
      IF dstRect.x > KScrW THEN BEGIN
        dstRect.x := -KScrW;
      END;
      
      // dec( srcRect.w );
      // dec( srcRect.h );
      // inc( dstRect.x );
      // inc( dstRect.y );
      // dec( dstRect.w );
      // dec( dstRect.h );
      // IF srcRect.w < kScrW DIV 2 THEN BEGIN
      //   set_rect( srcRect, 0, 0, kScrW, kScrH );
      //   set_rect( dstRect, 0, 0, kScrW, kScrH );
      // END;
      // dec( srcRect.w );
    END;
    
    PROCEDURE on_sdl_key( key : KeyboardEvent );
    BEGIN
      CASE Key.keysym.sym OF
        27 : user_quit := TRUE;
      END;
    END; { on_sdl_key }

    // DOM Level 3 Event Model:
  
    PROCEDURE on_click( e :  MouseEvent );
    BEGIN
      
    END; { on_click }

    PROCEDURE on_dbl_click( e :  MouseEvent );
    BEGIN
    END; { on_dbl_click }
      
    PROCEDURE on_mouse_down( e :  MouseEvent );
    BEGIN
      WriteLn('mousedown: (', e.x, ', ', e.y, ').' );
    END; { on_mouse_down }
    
    PROCEDURE on_mouse_enter( e :  MouseEvent );
    BEGIN
    END; { on_mouse_enter }
  
    PROCEDURE on_mouse_leave( e :  MouseEvent );
    BEGIN
    END; { on_mouse_leave }
  
    PROCEDURE on_mouse_move( e :  MouseEvent );
    BEGIN
    END; { on_mouse_move }
  
    PROCEDURE on_mouse_over( e :  MouseEvent );
    BEGIN
    END; { on_mouse_over }
    
    PROCEDURE on_mouse_out( e :  MouseEvent );
    BEGIN
    END; { on_mouse_out }
    
    PROCEDURE on_mouse_up( e :  MouseEvent );
    BEGIN
    END; { on_mouse_up }
    
    // my handlers for sdl events
    
    PROCEDURE on_sdl_mousebutton( sdl_evt : tsdl_mousebuttonevent );
    VAR
      evt : MouseEvent;
    BEGIN
      CASE sdl_evt.state OF
        SDL_PRESSED : BEGIN
                        evt.mousedown( sdl_evt.x, sdl_evt.y );
                        on_mouse_down( evt );
                      END;
        SDL_RELEASED: BEGIN
                        evt.mouseup( sdl_evt.x, sdl_evt.y );
                        on_mouse_up( evt );
                      END;
      END
    END;
    
    PROCEDURE update( );
    BEGIN
      slide_img( );      
    END; { update }
    
    PROCEDURE render( );
    BEGIN
      img.blit( screen, srcRect, dstRect );
      sdl_flip( screen );
    END { render };

    PROCEDURE shutdown( );
    BEGIN
      sdl_freesurface( screen );
      img.done( );
      dispose( srcRect );
      dispose( dstRect );
      sdl_quit( );
    END { shutdown };

  BEGIN
    setup( kScrW, kScrH );
    user_quit := FALSE;
    REPEAT
      update( );
      render( );
      IF SDL_POLLEVENT( evt )=1 THEN BEGIN
        CASE evt.type_ OF       
          SDL_KEYUP  :
            on_sdl_key( evt.key );
          SDL_MOUSEBUTTONDOWN,
          SDL_MOUSEBUTTONUP :
            on_sdl_mousebutton( evt.button );
          SDL_QUITEV :
            user_quit := TRUE;
        END;                     
      END;
    UNTIL user_quit;
    shutdown( );
  END { main };
  
BEGIN
  main( );
END { GoGoSDL }.
