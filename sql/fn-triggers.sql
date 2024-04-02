
-- attempt to create triggers for the tree database.
-- it's too hard and messy like this.

-- :io (io table)
create table ":io" (ts default current_timestamp, msg);


-- :f (functions)
create table ":fn" (
  i integer primary key,
  fn text, x, y, z, rt,
  doc text);

insert into ":fn" (fn,x,rt,doc)
  values ('tr.new-va','va','tr','create new tree from value id');
create trigger "!tr.new-va" before insert on ":fn" when new.fn='tr.new-va'
begin
  select raise(abort, 'todo: tr.new-va');
end;

insert into ":fn" (fn,x,y,rt,doc)
  values ('tr.new-nv','n','v','tr','create new tree from name, value');
create trigger "!tr.new-nv" before insert on ":fn" when new.fn='tr.new-nv'
begin
  insert into ":io"(msg) values ('tr.new-nv');
  select raise(abort,'todo: tr.new-nv');
end;

insert into ":fn" (fn,x,y,doc) values ('tr.app','pi','n','append item to tree');
create trigger ":tr.app" before insert on ":fn" when new.fn='tr.app'
begin
  select raise(abort,'todo: tr.app');
end;

create trigger "!unknown" before insert on ":fn"
   when not exists(select fn from ":fn" where ":fn".fn=new.fn)
begin
  insert into ":io"(msg) values ('unknown fn: '||new.fn);
  select raise(fail, 'unknown fn');
end;

create table ds (d,x);
select coalesce(max(x)+1,0) as depth from foo;


create table if not exists call(fn,x,y);
drop trigger if exists 'fn:chars';
create trigger 'fn:chars' before insert on call when new.fn='chars'
begin
  insert into ds
    select json_group_array(substr(s.v,i.value,1))
    from (select new.x as v) s
    join generate_series(1,length(s.v)) i;
  select raise(ignore);
end;

create view tos as  select v from ds order by rowid desc limit 1;
insert into call(fn,x) values ('chars','abc'); select * from ds;



insert into call(fn) values ('len'); select * from ds;
