/*
 * based on example code by @jesyspa ( see paramcount.cpp )
 *
 */
#include <iostream>

template<typename T> 
struct param_count;

template<typename R>
struct param_count<R()> {
  static constexpr std::string value() { return "ZERO"; }
};

template<typename R, typename A1>
struct param_count<R(A1)> {
  static constexpr std::string value() { return "ONE"; }
};

template<typename R, typename A1, typename A2>
struct param_count<R(A1, A2)> {
  static constexpr std::string value() { return "TWO"; }
};

template<typename R, typename ...ARGS> 
struct param_count<R(ARGS...)> {
  static constexpr std::string value() { return "MANY"; }
};

void f(int);
void g(int, int);
void h(int, int, int);

int main() {
   // should print ZERO ONE TWO MANY :
   std::cout
     << param_count<decltype(main)>::value() << " " 
     << param_count<decltype(f)>::value() << " " 
     << param_count<decltype(g)>::value() << " "
     << param_count<decltype(h)>::value() << "\n" ;
}
