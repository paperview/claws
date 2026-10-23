-- The laws of the Stats example. A human writes this file and the AI
-- must not edit it. Each law is a `def` of type `Prop`, and PROOF.lean
-- proves it with a theorem of the same name.
import Stats.Code

namespace Stats.Laws

open Stats.Code

-- LAW: count is the number of values, while that number fits in uint32_t.
def count_is_length : Prop :=
  ∀ xs : List (BitVec 32), xs.length < 2 ^ 32 → (summarize xs).count.toNat = xs.length

-- LAW: total is the wrapping sum of the values.
def total_is_sum : Prop :=
  ∀ xs : List (BitVec 32), (summarize xs).total = xs.sum

-- LAW: min is at most every value.
def min_le_all : Prop :=
  ∀ (xs : List (BitVec 32)) (y : BitVec 32), y ∈ xs → (summarize xs).min ≤ y

-- LAW: max is at least every value.
def all_le_max : Prop :=
  ∀ (xs : List (BitVec 32)) (y : BitVec 32), y ∈ xs → y ≤ (summarize xs).max

-- LAW: every value seen falls inside the band.
def seen_is_inside : Prop :=
  ∀ (xs : List (BitVec 32)) (y : BitVec 32), y ∈ xs → band (summarize xs) y = Band.Inside

end Stats.Laws
