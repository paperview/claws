// claws::expects(condition): a precondition. claws-lean reads the leading
// `claws::expects` statements of a function as its precondition `f.pre`.
// Every call from claws code must be proven to satisfy it, and the
// function's own safety is proven assuming it.
//
// At run time a failed precondition traps. Inside claws code that can
// never happen, since it is proven; the check protects calls from code
// outside the subset, which claws does not check.
#pragma once

namespace claws {

inline void expects(bool ok) {
  if (!ok) {
    __builtin_trap();
  }
}

} // namespace claws
