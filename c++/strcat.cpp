// string concatenation.

#include <iostream>
#include <sstream>
#include <string>
using namespace std;

int main() {

  // catenating strings:
  // cout << "a" + "b";         // nope. lits are (char*), not string.
  cout << ("x" "y")  << endl;   // implicit catenation.
  cout << "a" << "b" << endl;   // using the stream

  string res = "";
  cout << res + "a" + "b";      // okay because res is a string
  cout << endl;

  // numbers
  // --------------------------------------------------
  // this should work after #include <string> in c++11
  // but my clang++ version doesn't seem to support it.
  //cout << res + "hello world" + to_string(5) + "\n";

  // but we can use a string stream instead:
  std::stringstream ss; ss << 'a' <<"bc" << 123;
  cout << ss.str() << endl;

  return 0;
}
