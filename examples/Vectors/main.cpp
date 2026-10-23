// The driver for the Vectors example. It does I/O, so it sits outside the
// claws subset and stock clang compiles it with code.hpp unchanged.
#include <cstdio>

#include "code.hpp"

static void print(const char *label, const vec<uint32_t> &v) {
  std::printf("%s:", label);
  for (uint32_t x : v.to_vector()) {
    std::printf(" %u", x);
  }
  std::printf("\n");
}

int main() {
  vec<uint32_t> xs = vec<uint32_t>::from({12, 7, 30, 7, 19, 44, 30});
  print("xs        ", xs);
  std::printf("max_index  : %u (value %u)\n", max_index(xs), xs[max_index(xs)]);
  print("evens     ", evens(xs));
  print("histogram ", histogram(xs, 10, 4));
  vec<uint32_t> ys = xs;
  fill(ys, 5);
  print("fill(5)   ", ys);
  print("xs again  ", xs);
  return 0;
}
