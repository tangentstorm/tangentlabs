// Q: do constructors get called implicitly?
// A: yes.

#include <iostream>
using namespace std;

class ConstructMe {
public:
  ConstructMe() { cout << "yay!" << endl; }
  void method() { cout << "okay." << endl; }
};


int main () {
  ConstructMe cm;
  cm.method();
}

/* -- output --
yay!
okay.
*/
