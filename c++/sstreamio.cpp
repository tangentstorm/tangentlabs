#include <sstream>
#include <iostream>
#include <string>

using namespace std;

int main() {
  stringstream ss;
  ss << "hello world" << endl << "how you been?";
  string line;
  getline(ss, line);
  cout << "01:" << line << endl;
  getline(ss, line);
  cout << "02:" << line << endl;
}
