#include <math.h>
#include <stdio.h>

#define maxv 64
#define mask 63

int main() {
  long c=0,t=0;
  for (long i0=0;        i0<maxv; i0++)
  for (long i1=0, s1=i0; i1<maxv; i1++,s1++)
  for (long i2=0, s2=s1; i2<maxv; i2++,s2++)
  for (long i3=0, s3=s2; i3<maxv; i3++,s3++)
  for (long i4=0, s4=s3; i4<maxv; i4++,s4++)
  for (long i5=0, s5=s4; i5<maxv; i5++,s5++) { t++; if (!(s5 & mask)) c++; }
  printf("in %li/%li cases, 6 6-bit numbers summed (& 63) to 0", c, t);
}

/* output
---------
in 1073741824/68719476736 cases, 6 6-bit numbers summed (& 63) to 0
real    4m34.963s
user    4m33.293s
sys     0m0.000s
*/
