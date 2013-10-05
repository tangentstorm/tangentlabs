// program to test the sqldb system from the fcl-db package.
// (using sqlite as an example)
//
// if setting up the objects here seems verbose, it's
// because normally you would use these components from
// lazarus, and the configuration would all be done
// through the UI.
program sqldb_demo;
uses db, sqldb, sqlite3conn, classes;

var
  dbc : TSQLConnection;
  trx : TSQLTransaction;
  cur : TSQLQuery;

begin

  dbc := TSqlite3Connection.Create(Nil);
  dbc.DatabaseName := 'gen/sqldb_demo.sdb';
  dbc.open;

  trx := TSqlTransaction.Create(dbc);
  trx.database := dbc;

  trx.StartTransaction;
  dbc.ExecuteDirect('drop table if exists xs');
  dbc.ExecuteDirect('create table xs (id integer primary key, x varchar)');
  dbc.ExecuteDirect('insert into xs (x) values (''abc'')');
  dbc.ExecuteDirect('insert into xs (x) values (''123'')');
  dbc.ExecuteDirect('insert into xs (x) values (''xyz'')');
  trx.Commit;
  
  cur := TSqlQuery.Create(dbc);
  cur.database := dbc;
  cur.transaction := trx;
  cur.sql := TStringList.Create;
  cur.sql.add('select * from xs');
  cur.open;

  writeln('executing query.');
  writeln('-- results ------------------------');
  while not cur.eof do
    begin
      writeln('id:', cur.FieldByName('id').asInteger,
	      ' x:', cur.FieldByName('x').asString);
      cur.next;
    end;

  dbc.Free;
end.
{ output:

  executing query.
  -- results ------------------------
  id:1 x:abc
  id:2 x:123
  id:3 x:xyz
}
