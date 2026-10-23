-- The laws of the Clamp example. A human writes this file and the AI
-- must not edit it. Each law is a `def` of type `Prop`, and PROOF.lean
-- proves it with a theorem of the same name.
import Clamp.Code

namespace Clamp.Laws

open Clamp.Code

-- LAW: when lo <= hi, clamp lands inside [lo, hi].
def clamp_in_range : Prop :=
  ∀ x lo hi : BitVec 32, lo ≤ hi → contains ⟨lo, hi⟩ (clamp x lo hi) = true

-- LAW: clamp leaves a value that is already inside [lo, hi] alone.
def clamp_keeps : Prop :=
  ∀ x lo hi : BitVec 32, contains ⟨lo, hi⟩ x = true → clamp x lo hi = x

-- LAW: a widened range holds the value it was widened by.
def widen_holds_new : Prop :=
  ∀ (r : Range) (x : BitVec 32), contains (widen r x) x = true

-- LAW: a widened range still holds everything it held before.
def widen_holds_old : Prop :=
  ∀ (r : Range) (x y : BitVec 32), contains r y = true → contains (widen r x) y = true

-- LAW: inside a range, the offset from lo never exceeds the span.
-- Both sides use wrapping subtraction, so this needs the range to hold x.
def offset_within_span : Prop :=
  ∀ (r : Range) (x : BitVec 32), contains r x = true → x - r.lo ≤ span r

end Clamp.Laws
