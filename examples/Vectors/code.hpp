// The claws subset part of the Vectors example: reading, writing and
// growing claws::vec, with every index proven in bounds.
#pragma once

#include <cstdint>

#include <claws/expects.hpp>
#include <claws/vec.hpp>

using claws::vec;

// The index of the largest element; the first one, if several tie.
inline uint32_t max_index(const vec<uint32_t>& v) {
  claws::expects(v.size() != 0);
  uint32_t best = 0;
  for (uint32_t i = 1; i < v.size(); ++i) {
    if (v[i] > v[best]) {
      best = i;
    }
  }
  return best;
}

// Sets every element of v to x.
inline void fill(vec<uint32_t>& v, uint32_t x) {
  for (uint32_t i = 0; i < v.size(); ++i) {
    v[i] = x;
  }
}

// The even elements of xs, in order.
inline vec<uint32_t> evens(const vec<uint32_t>& xs) {
  vec<uint32_t> out{};
  for (uint32_t i = 0; i < xs.size(); ++i) {
    if (xs[i] % 2 == 0) {
      out.push(xs[i]);
    }
  }
  return out;
}

// The bucket of x among n buckets of the given width (from the Bits
// example).
inline uint32_t bucket(uint32_t x, uint32_t width, uint32_t n) {
  claws::expects(width != 0);
  claws::expects(n != 0);
  uint32_t b = x / width;
  if (b >= n) {
    b = n - 1;
  }
  return b;
}

// How many values of xs fall in each of n buckets of the given width.
inline vec<uint32_t> histogram(const vec<uint32_t>& xs, uint32_t width, uint32_t n) {
  claws::expects(width != 0);
  claws::expects(n != 0);
  vec<uint32_t> counts(n, 0);
  for (uint32_t i = 0; i < xs.size(); ++i) {
    counts[bucket(xs[i], width, n)] += 1;
  }
  return counts;
}
