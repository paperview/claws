// The claws subset part of the Bits example: division, shifts and the
// preconditions that make them defined.
#pragma once

#include <cstdint>

#include <claws/expects.hpp>

// a / b, rounded up.
inline uint32_t ceil_div(uint32_t a, uint32_t b) {
  claws::expects(b != 0);
  uint32_t q = a / b;
  if (a % b != 0) {
    q += 1;
  }
  return q;
}

// The histogram bucket of x, for n buckets of the given width. Values past
// the last bucket land in it.
inline uint32_t bucket(uint32_t x, uint32_t width, uint32_t n) {
  claws::expects(width != 0);
  claws::expects(n != 0);
  uint32_t b = x / width;
  if (b >= n) {
    b = n - 1;
  }
  return b;
}

// The mean of total over count, or 0 when there is nothing to average.
// No precondition: the check is in the code.
inline uint32_t mean(uint32_t total, uint32_t count) {
  return count == 0 ? 0 : total / count;
}

struct Halves {
  uint32_t hi;
  uint32_t lo;
};

inline uint32_t pack(uint32_t hi, uint32_t lo) {
  return (hi << 16) | (lo & 0xFFFFu);
}

inline Halves unpack(uint32_t p) {
  return Halves{p >> 16, p & 0xFFFFu};
}

// x rotated left by k. Both shifts need an amount below 32, which is why
// k may be neither 0 nor 32 or more.
inline uint32_t rotl(uint32_t x, uint32_t k) {
  claws::expects(k != 0);
  claws::expects(k < 32);
  return (x << k) | (x >> (32 - k));
}

// x rotated left one bit at a time, n times.
inline uint32_t spin(uint32_t x, uint32_t n) {
  for (uint32_t i = 0; i < n; ++i) {
    x = rotl(x, 1);
  }
  return x;
}
