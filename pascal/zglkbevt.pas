{ Raw Keyboard Event Callbacks in ZenGL.
--------------------------------------------------------------------

This example shows how your program can receive keyboard events
one at a time.
  
Note that for games, you would not normally use these callback
hooks, but instead check individual keys on each frame using
key_Up, key_Press, etc by registering a callback on SYS_UPDATE.

But occasionally, you really do want the codes immediately,
so here's how to do it.

Example:
  
Suppose the user has a dvorak keyboard layout, so that
the qwerty "asdf" keys are mapped to "aoeu".
  
If the user types dvorak-"o" by holding shift and
pressing the querty-"s" key, ZenGL will trigger
the following sequence:

  KeyPress( $FC );  // scancode for (right-hand) shift key
  KeyPress( $1F );  // scancode for qwerty-'s'
  if <<text-mode>> then
     KeyChar( 'O' ); 
  KeyRelease( $1F);  // release qwerty-'s'
  KeyRelease( $FC ); // release shift key

The <<text-mode>> state is enabled by calling key_BeginReadText,
and disabled by calling key_EndReadText.

--------------------------------------------------------------------
Created Mar 28, 2013 by Michal J Wallace

This is free and unencumbered software released into the public domain.

Anyone is free to copy, modify, publish, use, compile, sell, or
distribute this software, either in source code form or as a compiled
binary, for any purpose, commercial or non-commercial, and by any
means.

In jurisdictions that recognize copyright laws, the author or authors
of this software dedicate any and all copyright interest in the
software to the public domain. We make this dedication for the benefit
of the public at large and to the detriment of our heirs and
successors. We intend this dedication to be an overt act of
relinquishment in perpetuity of all present and future rights to this
software under copyright law.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY CLAIM, DAMAGES OR
OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE,
ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
OTHER DEALINGS IN THE SOFTWARE.

For more information, please refer to <http://unlicense.org/>
--------------------------------------------------------------------}

program zglkbevt;
  uses
    zgl_main,
    zgl_window,
    zgl_screen,
    zgl_keyboard, // only needed for keysText function
    sysutils;
  
  procedure OnKeyPress( KeyCode : Byte );		   
  begin    
    writeln( 'KeyPress: $', IntToHex( KeyCode, 2 ), '  -> ', keysText );
  end;
  
  procedure OnKeyRelease( KeyCode : Byte );
  begin
    writeln( 'KeyRelease: $', IntToHex( KeyCode, 2 ), '  -> ', keysText );
  end;

  procedure OnLoad;
  begin
    key_beginReadText({initial buffer value :=} '',
		      {arbitrary buffer limit := } 16 );
  end;

  procedure OnKeyChar( Symbol : UTF8String );
  begin
    writeln( '  KeyChar: ', Symbol );
  end;
  
begin
  wnd_SetCaption('zengl keyboard events');
  scr_SetOptions(300, 200, refresh_default, {fullscreen=}false, {vsync:=}true);

  zgl_reg( INPUT_KEY_RELEASE, @OnKeyRelease );
  zgl_reg( INPUT_KEY_PRESS, @OnKeyPress );
  
  zgl_reg( SYS_LOAD,   @OnLoad);
  zgl_reg( INPUT_KEY_CHAR, @OnKeyChar );
  
  zgl_init;
end.
