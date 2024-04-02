-- test of define from https://github.com/nalgeon/sqlean/
.load ./define

create virtual table range using define(
  (select value i from generate_series(0,:n-1)));

select define ('odd',':n % 2 = 1');
select define ('co','case when odd(:n) then (:n*3)+1 else :n/2 end');

select co(i) from range(10);
