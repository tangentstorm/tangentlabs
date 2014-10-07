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

// this gets called for every row in the result
function callback(user: pointer; cols: cint; values, name: ppchar): cint; cdecl;
  begin
    writeln('! callback triggered');
    writeln('  key: ', name^);
    writeln('  val: ', values^);
    result := 0;
  end;

procedure myXFunc(ctx: psqlite3_context; N: cint; V: ppsqlite3_value); cdecl;
  var i : byte; val : pChar;
  begin
    writeln('! xFunc triggered');
    writeln('  arg count: ', N);
    if n > 0 then begin
      writeln('  arg values: ');
      for i := 0 to n-1 do begin
	val := sqlite3_value_text(v[i]);
	writeln('    ', i, ':', val);
      end
    end;
    sqlite3_result_text(ctx, 'hello there!', -1, nil);
  end;


var
  dbName : PChar = ':memory:';
  dbh	 : PSQLite3;
  err	 : CInt;
  msg,sql: PChar;
  
begin
  writeLn('--opening new in-memory database');
  sqlite3_open(dbName, @dbh);

  // execute a query to make sure everything's set up ok.
  sql := 'select 2+2 as iv union values(''four'')';
  err := sqlite3_exec(dbh, sql, @callback, nil, @msg);
  assert(err = 0);

  // add the function
  sqlite3_create_function(dbh, 'sayhello', 1, SQLITE_UTF8,
			  {userData} nil,
			  {xFunc}  @myXFunc,
			  {xStep}  nil,
			  {xFinal} nil);

  // and now invoke it
  sql := 'select sayhello(123)';
  err := sqlite3_exec(dbh, sql, @callback, nil, @msg);
  assert(err = 0);
  
  sqlite3_close(dbh);
  writeLn('--all done.');
end.
