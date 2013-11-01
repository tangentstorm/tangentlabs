// algorithms to reverse a string

#include <iostream>

using namespace std;

string rev_copy (string s) {
  int len = s.length();
  string r; r.reserve(len);
  for (int i = len; --i >= 0;) r += s[i];
  return r;
}

string rev_inplace (string s) {
  int len = s.length()-1;
  int mid = len / 2;
  for (int i = 0; i <= mid; i++) {
    char tmp = s[i];
    s[i] = s[len-i];
    s[len-i] = tmp;
  }
  return s;
}

int main() {
  string s = "!dlrow olleh";
  cout << "original    : " << s << endl;
  cout << "rev_copy    : " << rev_copy(s) << endl;
  cout << "rev_inplace : " << rev_inplace(s) << endl;
  return 0;
}
