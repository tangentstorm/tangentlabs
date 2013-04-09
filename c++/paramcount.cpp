/*
 * I asked on #learnprogramming whether c++ templates could change
 * the way things compiled based on the parameter count of a function.
 *
 * @jesyspa supplied the following example code:
 *
 */
#include <iostream>

template<typename T>
struct param_count;

// This originally used a two-part recursive template (!!)
// to add up the number of ARGS, but he simplified it by
// calling sizeof here.
template<typename R, typename...ARGS>
struct param_count<R(ARGS...)> {
   static constexpr unsigned int value = sizeof...(ARGS);
};

void f(int, int);

int main() {
   std::cout << param_count<decltype(main)>::value << " " << param_count<decltype(f)>::value;
}
