load 'data/ddsqlite'

api =. ''conew'jddsqlite'
dbc =. ddcon__api 'database=:memory:;nocreate=0'
'create table test (id integer primary key, name char(32))' ddsql__api dbc
'insert into test (name) values (''michal'')' ddsql__api dbc
'insert into test (name) values (''sabren'')' ddsql__api dbc

NB. fetch as rows:
cur =. 'select * from test' ddsel__api dbc
] all =. ddfet__api cur, _1
NB. ┌─┬──────┐
NB. │1│michal│
NB. ├─┼──────┤
NB. │2│sabren│
NB. └─┴──────┘

NB. fetch as columns:
cur =. 'select * from test' ddsel__api dbc
] 'id name' =. ddfch__api cur, _1
NB. ┌─┬──────┐
NB. │1│michal│
NB. │2│sabren│
NB. └─┴──────┘
