// The claws subset part of the Sorting example: insertion sort over
// claws::list, in either order.
#pragma once

#include <cstdint>

#include <claws/list.hpp>

using claws::cons;
using claws::list;

enum class Order { Ascending, Descending };

// Whether a may come before b in order o.
inline bool in_order(Order o, uint32_t a, uint32_t b) {
  switch (o) {
  case Order::Ascending:
    return a <= b;
  case Order::Descending:
    return b <= a;
  }
}

// xs with x placed before the first element it may come before.
inline list<uint32_t> insert(Order o, uint32_t x, list<uint32_t> xs) {
  return xs.match(
      [&] { return cons(x, list<uint32_t>{}); },
      [&](uint32_t h, list<uint32_t> t) {
        if (in_order(o, x, h)) {
          return cons(x, cons(h, t));
        }
        return cons(h, insert(o, x, t));
      });
}

inline list<uint32_t> sort(Order o, list<uint32_t> xs) {
  return xs.match(
      [&] { return list<uint32_t>{}; },
      [&](uint32_t h, list<uint32_t> t) { return insert(o, h, sort(o, t)); });
}

// The wrapping sum of xs.
inline uint32_t sum(list<uint32_t> xs) {
  return xs.match(
      [] { return 0u; },
      [](uint32_t h, list<uint32_t> t) { return h + sum(t); });
}
