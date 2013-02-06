#include <iostream>
#include <string>

std::string color;

int main()
{
  std::cout << "choose: ( red | blu | grn ) ?: ";
  std::cin >> color;
  if ( color == "red" ) { std::cout << "RED!"; }
  else if ( color == "blu" ) { std::cout << "BLU!"; }
  else if ( color == "grn" ) { std::cout << "GRN!"; }
  std::cout << "\n";
}
