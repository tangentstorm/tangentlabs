#include <string>

int main() {

  std::string word;
  int i;

  std::cout << "enter 3 words: ";
  for ( i = 0; i < 3; ++i ) {
    std::cin >> word;
    std::cout << word << "\n";
  }
}
