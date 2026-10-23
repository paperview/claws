-- The laws of the Bits example. A human writes this file and the AI
-- must not edit it. Each law is a `def` of type `Prop`, and PROOF.lean
-- proves it with a theorem of the same name. Code.lean adds a safety
-- obligation, in Bits.Laws.Safety, for each function that divides or
-- shifts by a variable amount.
import Bits.Code

namespace Bits.Laws

open Bits.Code

-- LAW: ceil_div rounds up: q * b covers a.
def ceil_div_covers : Prop :=
  ∀ a b : BitVec 32, b ≠ 0 → a.toNat ≤ (ceil_div a b).toNat * b.toNat

-- LAW: ceil_div rounds up by less than one b.
def ceil_div_tight : Prop :=
  ∀ a b : BitVec 32, b ≠ 0 → (ceil_div a b).toNat * b.toNat < a.toNat + b.toNat

-- LAW: every value lands in one of the n buckets.
def bucket_in_range : Prop :=
  ∀ x width n : BitVec 32, width ≠ 0 → n ≠ 0 → bucket x width n < n

-- LAW: unpack undoes pack, for 16-bit halves.
def unpack_pack : Prop :=
  ∀ hi lo : BitVec 32, unpack (pack hi lo) = ⟨hi &&& 0xFFFF, lo &&& 0xFFFF⟩

-- LAW: rotating left by k and then by 32 - k gives x back.
def rotl_inverse : Prop :=
  ∀ x k : BitVec 32, k ≠ 0 → k < 32 → rotl (rotl x k) (32 - k) = x

end Bits.Laws
