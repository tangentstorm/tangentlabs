/*
 * I asked on #learnprogramming whether c++ templates could change
 * the way things compiled based on the parameter count of a function.
 *
 * jesyspa supplied the following example code:
 *
 */
#include <iostream>

template<typename T>
struct param_count;

template<typename R, typename F, typename... REST>
struct param_count<R(F, REST...)> {
   static constexpr unsigned int value = 1 + param_count<R(REST...)>::value;
};

template<typename R>
struct param_count<R()> {
   static constexpr unsigned int value = 0;
};

void f(int, int);

int main() {
   std::cout << param_count<decltype(main)>::value << " " << param_count<decltype(f)>::value;
}
