// The claws subset part of the Loops example: counting loops that build a
// list, accumulate a sum, and nest.
#pragma once

#include <cstdint>

#include <claws/list.hpp>

using claws::cons;
using claws::list;

// n copies of x.
inline list<uint32_t> replicate(uint32_t x, uint32_t n) {
  list<uint32_t> xs{};
  for (uint32_t i = 0; i < n; ++i) {
    xs = cons(x, xs);
  }
  return xs;
}

// 0 + 1 + ... + (n - 1), wrapping.
inline uint32_t triangle(uint32_t n) {
  uint32_t s = 0;
  for (uint32_t i = 0; i < n; ++i) {
    s += i;
  }
  return s;
}

// w * h, counted one cell at a time.
inline uint32_t cells(uint32_t w, uint32_t h) {
  uint32_t c = 0;
  for (uint32_t y = 0; y < h; ++y) {
    for (uint32_t x = 0; x < w; ++x) {
      c += 1;
    }
  }
  return c;
}
