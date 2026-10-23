// The driver for the Bits example. It does I/O, so it sits outside the
// claws subset and stock clang compiles it with code.hpp unchanged.
#include <cstdio>

#include "code.hpp"

int main() {
  std::printf("ceil_div(10, 3) = %u, ceil_div(9, 3) = %u\n", ceil_div(10, 3), ceil_div(9, 3));
  std::printf("bucket(57, 10, 4) = %u, bucket(12, 10, 4) = %u\n", bucket(57, 10, 4), bucket(12, 10, 4));
  std::printf("mean(10, 0) = %u, mean(10, 4) = %u\n", mean(10, 0), mean(10, 4));
  Halves h = unpack(pack(0xABCD, 0x1234));
  std::printf("unpack(pack(0xABCD, 0x1234)) = 0x%X 0x%X\n", h.hi, h.lo);
  std::printf("rotl(0x80000001, 4) = 0x%08X, spin(1, 33) = %u\n", rotl(0x80000001u, 4), spin(1, 33));
  return 0;
}
