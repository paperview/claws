// The driver for the Loops example. It does I/O, so it sits outside the
// claws subset and stock clang compiles it with code.hpp unchanged.
#include <cstdio>

#include "code.hpp"

int main() {
  std::printf("replicate(7, 4) has %zu values\n", replicate(7, 4).to_vector().size());
  std::printf("triangle(10) = %u\n", triangle(10));
  std::printf("triangle(100000) = %u (wrapped)\n", triangle(100000));
  std::printf("cells(30, 40) = %u\n", cells(30, 40));
  return 0;
}
