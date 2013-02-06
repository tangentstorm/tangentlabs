{$MODE OBJFPC}
program SetRepresentations;

type
  prime  = (two, three, five, seven, eleven);
  primes = set of prime;

begin
  writeln(five);          // actually prints 'five'!
  writeln(ord(five));     // actually prints '2'
  // writeln(five = 2);   // this would throw an error
  writeln(ord(five) = 2); // prints 'TRUE'
  writeln(Byte(five) = 2); // prints 'TRUE'
end. 