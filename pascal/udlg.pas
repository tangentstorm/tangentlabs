{ wrapper functions to invoke the 'dialog' command for freebsd/linux

  http://invisible-island.net/dialog/

  this unit is in the public domain.

  example usage:

  program dlg;
  uses udlg;
  begin
    writeln(udlg.menu('hello', 20, 50, 18, ['a','apple','b','banana']));
  end.

}
{$WARNING Parameters to dlg commands are not sanitized. do not use in real code! (TODO)}
{$h+}{$mode delphi}{ dialog example }
unit udlg;
interface uses unix, sysutils;

  var tmpfile : string = 'x.txt';
  function dialog(cmd, argfmt : string; argv : array of const) : string;
  function menu(title : string; h,w,mh : byte; options: array of string) : string;
  function fselect(path : string; h,w : byte) : string;

implementation
  
function readln(var f : textfile) : string;
  begin
    system.readln(f, result);
  end;
  
function contentsof(path : string) : string;
  var f : textfile;
  begin
    result := '';
    assign(f,path); reset(f);
    while not eof(f) do appendstr(result, readln(f));
  end;

function strjoin(chunks : array of string; sep : string = '') : string;
  var i : integer;
  begin
    result := '';
    for i := low(chunks) to high(chunks)-1 do result += chunks[i] + sep;
    result += chunks[high(chunks)];
  end;

function dialog(cmd, argfmt : string; argv : array of const) : string;
  var args : string;
  begin
    args := format(argfmt, argv);
    fpsystem(format('dialog --%s %s 2> %s ', [cmd, args, tmpfile]));
    result := contentsof(tmpfile);
  end;

function menu(title : string; h,w,mh : byte; options: array of string) : string;
  begin
    result := dialog('menu', '"%s" %d %d %d %s',
		     [title, h, w, mh, strjoin(options, ' ')])
  end;

function fselect(path : string; h,w : byte) : string;
  begin
    result := dialog('fselect', '"%s" %d %d', [h, w])
  end;

begin
end.