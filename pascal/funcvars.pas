{$mode objfpc}
program funcvars; // Jun 18 2013 mjw

{ question: given a variable that points to a function,
  can you evaluate the function simply by using the variable's
  name without parentheses?
  
  answer: yes. that is why you must prefix the function
  with @ if you don't want to evaluate it. }

type
  TMsgFn = function : string;
  TData	 = record
	     msg : TMsgFn;
	   end;
  TCtxFn = function : TData;

function getMessage : string;
  begin
    result := 'hello world'
  end;
  
function getContext : TData;
  begin
    result.msg := @getMessage
  end;
  
var context : TCtxFn = @getContext;
begin
  with context do writeln( msg )
end.

{ output:

  hello world
}
