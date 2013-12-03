#include <iostream.h>

using namespace std;

int main() {
  int res = 0;
  
  cout << "number: ";
  cin >> res;

  while (cin.fail()) {
    string bad;
    cin.clear(); // clear error flags
    cin >> bad;
    cerr << "Sorry, '" << bad << "' is not a valid number." << endl;
    cout << "try again: ";
    cin >> res;
  }

  cout << "Okay. Your number is " << res << endl;

  return 0;
}
