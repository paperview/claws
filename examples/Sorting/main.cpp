// The driver for the Sorting example. It does I/O, so it sits outside the
// claws subset and stock clang compiles it with code.hpp unchanged.
#include <cstdio>

#include "code.hpp"

static void print(const char *label, const list<uint32_t> &xs) {
  std::printf("%s:", label);
  for (uint32_t x : xs.to_vector()) {
    std::printf(" %u", x);
  }
  std::printf("\n");
}

int main() {
  list<uint32_t> xs = list<uint32_t>::from({5, 3, 9, 1, 3, 4000000000u});
  print("input     ", xs);
  print("ascending ", sort(Order::Ascending, xs));
  print("descending", sort(Order::Descending, xs));
  std::printf("sum %u, sorted sum %u\n", sum(xs), sum(sort(Order::Ascending, xs)));
  return 0;
}
