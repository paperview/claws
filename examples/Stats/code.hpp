// The claws subset part of the Stats example: running statistics over a
// list, written in the mutating style C++ usually has.
#pragma once

#include <cstdint>

#include <claws/list.hpp>

using claws::list;

struct Stats {
  uint32_t count;
  uint32_t total;  // wraps, as uint32_t does
  uint32_t min;
  uint32_t max;
};

inline Stats no_stats() {
  return Stats{0, 0, 0xFFFFFFFFu, 0};
}

// s with x recorded.
inline Stats record(Stats s, uint32_t x) {
  s.count += 1;
  s.total += x;
  if (x < s.min) {
    s.min = x;
  }
  if (x > s.max) {
    s.max = x;
  }
  return s;
}

inline Stats summarize(list<uint32_t> xs) {
  return xs.match(
      [] { return no_stats(); },
      [](uint32_t h, list<uint32_t> t) { return record(summarize(t), h); });
}

enum class Band { Below, Inside, Above };

// Where x falls against the range s has seen.
inline Band band(Stats s, uint32_t x) {
  Band b = Band::Inside;
  if (x < s.min) {
    b = Band::Below;
  }
  if (x > s.max) {
    b = Band::Above;
  }
  return b;
}
