// claws::vec<T>: a growable array with value semantics. claws-lean
// translates it to Lean's `Array T`, so this file is trusted: it must
// behave as that model does.
//
// In the claws subset:
//
//   vec<T>{}          the empty array        #[]
//   vec<T>(n, fill)   n copies of fill       Array.replicate n.toNat fill
//   v.size()          its length             BitVec.ofNat 32 v.size
//   v[i]              read element i         v[i.toNat]!
//   v[i] = x          write element i        v.setIfInBounds i.toNat x
//   v.push(x)         append x               v.push x
//
// Reading or writing v[i] obliges the code to prove i < v.size(), and
// push to prove v.size() < 2^32 - 1, so that size() always fits a
// uint32_t. Both are part of the function's safety obligation. At run time
// a violation traps, which protects calls from code outside the subset.
//
// Copying a vec copies its elements, as copying a Lean array does: no two
// vecs share storage. Pass a large vec as `const vec<T>&` or `vec<T>&`
// rather than by value to avoid the copy.
#pragma once

#include <cstdint>
#include <initializer_list>
#include <type_traits>
#include <vector>

namespace claws {

template <class T>
class vec {
  static_assert(!std::is_same_v<T, bool>,
                "vec<bool> is unavailable: std::vector<bool> has no element references. Use vec<uint32_t>.");

public:
  vec() = default;
  vec(uint32_t n, const T &fill) : items_(n, fill) {}

  uint32_t size() const { return static_cast<uint32_t>(items_.size()); }

  T &operator[](uint32_t i) {
    check(i < items_.size());
    return items_[i];
  }

  const T &operator[](uint32_t i) const {
    check(i < items_.size());
    return items_[i];
  }

  void push(const T &x) {
    check(items_.size() < 0xFFFFFFFFu);
    items_.push_back(x);
  }

  // For drivers: build a vec from values, and copy one out.
  static vec from(std::initializer_list<T> values) {
    vec out;
    out.items_.assign(values.begin(), values.end());
    return out;
  }

  const std::vector<T> &to_vector() const { return items_; }

private:
  static void check(bool ok) {
    if (!ok) {
      __builtin_trap();
    }
  }

  std::vector<T> items_;
};

} // namespace claws
