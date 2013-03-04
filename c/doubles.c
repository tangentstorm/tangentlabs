// You should never really use doubles for currency, but
// if somebody insisted you had to, how bad would it be?
//
// gcc 4.7.prints the following sequence without rounding
// errors on my machine. (4.7.2-2ubuntu1)
#include <stdio.h>

void main() {
  double i = 0.00;
  while (i < 1.0) {
    printf("%f\n", i);
    i += 0.01;
  }
}
