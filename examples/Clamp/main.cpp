// The driver for the Clamp example. It does I/O, so it sits outside the
// claws subset and stock clang compiles it with code.hpp unchanged.
#include <cstdio>

#include "code.hpp"

int main() {
  Range r{10, 20};
  r = widen(r, 25);
  std::printf("range [%u, %u], span %u\n", r.lo, r.hi, span(r));
  std::printf("clamp(3) = %u, clamp(99) = %u\n", clamp(3, r.lo, r.hi), clamp(99, r.lo, r.hi));
  return 0;
}
