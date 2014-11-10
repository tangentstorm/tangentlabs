#include <math.h>
#include <stdio.h>

int main() {
  int c=0;
  for (int i0=0;i0<(1<<6);i0++)
  for (int i1=0;i1<(1<<6);i1++)
  for (int i2=0;i2<(1<<6);i2++)
  for (int i3=0;i3<(1<<6);i3++)
  for (int i4=0;i4<(1<<6);i4++)
  for (int i5=0;i5<(1<<6);i5++) if (!((i0+i1+i2+i3+i4+i5)%(1<<6))) c++;
  printf("there are %i cases where 6 6-bit numbers summed (mod 1<<6) to 0", c);
}

/* output
---------
there are 1073741824 cases where 6 6-bit numbers summed (mod 1<<6) to 0
real    7m26.177s
user    7m25.259s
sys     0m0.001s
*/
