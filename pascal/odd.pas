{$MODE OBJFPC}
program oddness;
{ Q: does pascal have odd() like oberon? }
{ A: yep                                 }

begin  
  writeln(odd(1));  // => TRUE
  writeln(odd(2));  // => FALSE
end. 