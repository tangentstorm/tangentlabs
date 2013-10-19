{
  This unit demonstrates a helper related bug in fpc.

  Moving the declaration from the implementation
  to the interface section causes the helper to
  disappear.

  cf. http://bugs.freepascal.org/view.php?id=25210

  # this works:
  $ fpc uhelperbug.pas
  Free Pascal Compiler version 2.7.1 [2013/10/18] for x86_64
  Copyright (c) 1993-2013 by Florian Klaempfl and others
  Target OS: FreeBSD for x86-64
  Compiling uhelperbug.pas
  uhelperbug.pas(61,5) Note: Local variable "rs" is assigned but never used
  92 lines compiled, 0.3 sec
  1 note(s) issued

  $ fpc -dPUBLIC_HELPER uhelperbug.pas
  Free Pascal Compiler version 2.7.1 [2013/10/18] for x86_64
  Copyright (c) 1993-2013 by Florian Klaempfl and others
  Target OS: FreeBSD for x86-64
  Compiling uhelperbug.pas
  uhelperbug.pas(65,12) Error: identifier idents no member "query"
  uhelperbug.pas(67) Fatal: There were 1 errors compiling module, stopping
  Fatal: Compilation aborted

}
{$mode delphi}{$i xpc.inc}
unit uhelperbug;
interface
uses db, sqldb, sqlite3conn,
  classes; // for TStringList

{$IFDEF PUBLIC_HELPER}
type
  TDbHelper = class helper for TSqlConnection
    function Query(sql: string) : TSQLQuery;
  end;
{$ENDIF}

  function connect(const path : string) : TSqlConnection;

implementation


{$IFNDEF PUBLIC_HELPER}
type
  TDbHelper = class helper for TSqlConnection
    function Query(sql: string) : TSQLQuery;
  end;
{$ENDIF}


//-----------------------------------------------------------------------

//- - [ TDbHelper ] - - - - - - - - - - - - - - - - - - - - - - - - - - -

function TDbHelper.Query(sql : string) : TSQLQuery;
  begin
    result := TSQLQuery.Create(self);
    result.database := self;
    result.sql := TStringList.Create;
    result.sql.add(sql);
    result.Transaction := self.Transaction;
    result.Open;
  end;

//- - [ misc routines ] - - - - - - - - - - - - - - - - - - - - - - - - -

function connect(const path : string) : TSqlConnection;
  begin
    result := TSqlite3Connection.Create(Nil);
    result.DatabaseName := path;
    result.Transaction := TSqlTransaction.Create(result);
    result.Open;
  end;

//-----------------------------------------------------------------------
var
  db : TSqlConnection;
  rs : TSqlQuery;
begin
  db := connect('database.sdb');
  rs := db.query('select * from sqlite_master');
end.
