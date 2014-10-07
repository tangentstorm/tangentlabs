// demo of extending sqlite with a custom function.
// this is just using the raw sqlite3 API rather
// than the nice object oriented interfaces because
// none of them seem to support creating functions yet
// and i just wanted to see how to do it under the hood.
//
// references:
// http://www.sqlite.org/c3ref/create_function.html
{$mode objfpc}
program sqlitefunc;
uses ctypes, sqlite3;

function callback(user: pointer; cols: cint; values, name: ppchar): cint; cdecl;
  begin
    writeln('! callback triggered');
    writeln('  values:', values^);
    result := 0;
  end;

var
  dbName : PChar = ':memory:';
  dbh	 : PSQLite3;
  err	 : CInt;
  msg	 : PChar;
begin
  writeLn('--creating in-memory database');
  sqlite3_open(dbName, @dbh);
  err := sqlite3_exec(dbh, 'select 2+2 as iv', @callback, nil, @msg);
  writeln('> error code: ', err);
  sqlite3_close(dbh);
  writeLn('--all done.');
end.
