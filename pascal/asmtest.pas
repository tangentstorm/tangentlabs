// demonstration of mixing pascal and (x86-64) assembly language

{$asmmode intel}
program asmtest;
uses sysutils;

var
  data : array [ $0 .. $f ] of uint64; // arbitrary chunk of ram
  p    : pointer; // pointer to the data
  i    : byte;    // loop counter

begin

  // set up a marker value (if it gets printed, something is wrong)
  for i := $0 to $f do data[i] := $0123456789abcdef;
  
  // populate some registers:
  p := @data[0];
  asm
    mov r8, $0101010101010101
    mov r9, $1010101010101010
    mov r10, p
  end;

  // now populate our data
  for i := 0 to $f do
    asm
      mov [r10], r8           // p^ := number in r8
      add r8, r9              // r8 += number in r9
      add r10, sizeof(uint64) // increment the pointer by 8
    end;

  // show the output
  for i := $0 to $f do writeln( i : 2, ': ', inttohex(data[i], 16));
end.

{ output:
----------------------------
 0: 0101010101010101
 1: 1111111111111111
 2: 2121212121212121
 3: 3131313131313131
 4: 4141414141414141
 5: 5151515151515151
 6: 6161616161616161
 7: 7171717171717171
 8: 8181818181818181
 9: 9191919191919191
10: A1A1A1A1A1A1A1A1
11: B1B1B1B1B1B1B1B1
12: C1C1C1C1C1C1C1C1
13: D1D1D1D1D1D1D1D1
14: E1E1E1E1E1E1E1E1
15: F1F1F1F1F1F1F1F1
----------------------------
}
