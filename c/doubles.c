// You should never really use doubles for currency, but
// if somebody insisted you had to, (a professor, say),
// how bad would it be?
//
// gcc 4.7.prints the following sequence without rounding
// errors on my machine. (4.7.2-2ubuntu1)
#include <stdio.h>

void main() {
  double j, i;
  char str[64];
  i = 0.00;
  while (i < 1.0) {
    sprintf(str, "%f", i);    // render double as string
    sscanf(str, "%lf", &j);   // parse it back in again
    printf("%f %f\n", i, j);  // print both side by side
    i += 0.001;
  }
}
