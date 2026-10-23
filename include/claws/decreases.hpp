// claws::decreases(measure): the measure of a `while` loop. It must be
// the first statement of the loop's body. claws-lean proves the loop
// terminates by requiring, as part of the function's safety obligation,
// that the measure is smaller at the start of every later iteration than
// at the start of this one. A uint32_t cannot shrink forever, so the
// loop ends.
//
// At run time it does nothing: the proof is the check.
#pragma once

#include <cstdint>

namespace claws {

inline void decreases(uint32_t) {}

} // namespace claws
