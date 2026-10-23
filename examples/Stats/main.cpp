// The driver for the Stats example. It does I/O, so it sits outside the
// claws subset and stock clang compiles it with code.hpp unchanged.
#include <cstdio>

#include "code.hpp"

static const char *name(Band b) {
  switch (b) {
  case Band::Below: return "below";
  case Band::Inside: return "inside";
  case Band::Above: return "above";
  }
  return "?";
}

int main() {
  Stats s = summarize(list<uint32_t>::from({12, 7, 30, 7, 19}));
  std::printf("count %u, total %u, min %u, max %u\n", s.count, s.total, s.min, s.max);
  const uint32_t probes[] = {3, 7, 25, 31};
  for (uint32_t x : probes) {
    std::printf("%u is %s\n", x, name(band(s, x)));
  }
  return 0;
}
