// geordi (c++ bot) said this way of using ++ was undefined. 
// looks like he was right.
#include<iostream>
using namespace std;
int main() { int g0=0; int gn=4;
  cout << (g0?g0:(g0=gn++)) << ',' << (g0?g0:(g0=++gn)) << endl;
  cout << g0 << ',' << gn << endl; }

/* output when compiling with clang++:
--------------------------------------
4,4
4,5

** output when compiling with g++:
--------------------------------------
5,5
5,5


clang and g++ both agree when i make them
both gn++ or ++gn, but it seems that's
just a coincidence, rather than defined
behavior.

*/
