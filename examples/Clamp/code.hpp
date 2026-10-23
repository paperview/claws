// The claws subset part of the Clamp example. claws-lean translates this
// file to Code.lean, and LAWS.lean states what it must satisfy.
#pragma once

#include <cstdint>

inline uint32_t min(uint32_t a, uint32_t b) {
  return a < b ? a : b;
}

inline uint32_t max(uint32_t a, uint32_t b) {
  return a < b ? b : a;
}

// x moved into [lo, hi]. Meaningful only when lo <= hi.
inline uint32_t clamp(uint32_t x, uint32_t lo, uint32_t hi) {
  if (x < lo) {
    return lo;
  }
  if (x > hi) {
    return hi;
  }
  return x;
}

// The closed interval [lo, hi].
struct Range {
  uint32_t lo;
  uint32_t hi;
};

inline bool contains(Range r, uint32_t x) {
  return r.lo <= x && x <= r.hi;
}

// How far hi is above lo.
inline uint32_t span(Range r) {
  return r.hi - r.lo;
}

// The smallest range that holds both r and x.
inline Range widen(Range r, uint32_t x) {
  const uint32_t lo = min(r.lo, x);
  const uint32_t hi = max(r.hi, x);
  return Range{lo, hi};
}
