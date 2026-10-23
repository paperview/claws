-- The laws of the Vectors example. A human writes this file and the AI
-- must not edit it. Each law is a `def` of type `Prop`, and PROOF.lean
-- proves it with a theorem of the same name. Code.lean adds a safety
-- obligation, in Vectors.Laws.Safety, for each function that indexes,
-- pushes, divides, or calls a function with a precondition.
--
-- A claws::vec never holds 2^32 elements, so laws about one assume
-- `v.size < 2 ^ 32`.
import Vectors.Code

namespace Vectors.Laws

open Vectors.Code

-- LAW: max_index returns a valid index.
def max_index_in_range : Prop :=
  ∀ v : Array (BitVec 32), v.size < 2 ^ 32 → v.size ≠ 0 → (max_index v).toNat < v.size

-- LAW: no element is larger than the one at max_index.
def max_index_is_max : Prop :=
  ∀ v : Array (BitVec 32), v.size < 2 ^ 32 → v.size ≠ 0 →
    ∀ j < v.size, v[j]! ≤ v[(max_index v).toNat]!

-- LAW: fill keeps the size.
def fill_size : Prop :=
  ∀ (v : Array (BitVec 32)) (x : BitVec 32), (fill v x).size = v.size

-- LAW: after fill, every element is x.
def fill_all : Prop :=
  ∀ (v : Array (BitVec 32)) (x : BitVec 32), v.size < 2 ^ 32 →
    ∀ j < v.size, (fill v x)[j]! = x

-- LAW: evens returns only even values.
def evens_even : Prop :=
  ∀ (xs : Array (BitVec 32)) (y : BitVec 32), y ∈ evens xs → y % 2 = 0

-- LAW: evens never returns more values than it was given.
def evens_size : Prop :=
  ∀ xs : Array (BitVec 32), xs.size < 2 ^ 32 → (evens xs).size ≤ xs.size

-- LAW: a histogram has one count per bucket.
def histogram_size : Prop :=
  ∀ (xs : Array (BitVec 32)) (width n : BitVec 32), (histogram xs width n).size = n.toNat

end Vectors.Laws
