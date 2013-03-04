// Object pascal program to demonstrate sharing ram
// between pascal and a virtual machine written in
// pascal.
program vmvars;
  var
    // here the vm's ram is represented as an array
    ram	 : array[ 0 .. 16383 ] of int32; // 64Kb / 4

    // here we use the absolute keyword to give a name
    // to a specific cell in the array
    here : int32 absolute ram[2];

begin
  ram[2] :=  0; writeln(ram[2]:2, ' ', here:2);  //   0   0
  here   := 75; writeln(ram[2]:2, ' ', here:2);  //  75  75
end.
