-- The proofs of the Bits example's laws and safety obligations. The AI
-- writes this file.
import Std.Tactic.BVDecide
import Bits.LAWS
import Bits.Ast
import Claws.Loop

namespace Bits.Proof

open Bits.Code

-- ceil_div in the natural numbers: the quotient, plus one if there is a
-- remainder.
theorem ceil_div_nat (a b : BitVec 32) (hb : b ≠ 0) :
    (ceil_div a b).toNat = a.toNat / b.toNat + (if a.toNat % b.toNat = 0 then 0 else 1) := by
  have hb' : 0 < b.toNat := by bv_omega
  simp only [ceil_div]
  split
  · rename_i h
    have hr : a.toNat % b.toNat ≠ 0 := by
      intro e
      have : a % b = 0 := BitVec.eq_of_toNat_eq (by simp [BitVec.toNat_umod, e])
      simp [this] at h
    -- A remainder means b ≥ 2, so q * 2 ≤ q * b ≤ a < 2^32 and q + 1 fits.
    have h2 : 2 ≤ b.toNat := by
      rcases Nat.lt_or_ge b.toNat 2 with h1 | h1
      · have : b.toNat = 1 := by omega
        rw [this] at hr
        exact absurd (Nat.mod_one _) hr
      · exact h1
    have hle : a.toNat / b.toNat * 2 ≤ a.toNat / b.toNat * b.toNat := Nat.mul_le_mul_left _ h2
    have hqb : a.toNat / b.toNat * b.toNat ≤ a.toNat := Nat.div_mul_le_self _ _
    have ha : a.toNat < 2 ^ 32 := a.isLt
    simp [BitVec.toNat_add, BitVec.toNat_udiv, hr]
    omega
  · rename_i h
    have h0 : a % b = 0 := by simpa using h
    have hr : a.toNat % b.toNat = 0 := by simpa [BitVec.toNat_umod] using congrArg BitVec.toNat h0
    simp [BitVec.toNat_udiv, hr]

-- The division facts the two ceil_div laws need, with the product turned
-- the same way in each so omega can treat it as one unknown.
theorem div_facts (a b : BitVec 32) (hb : b ≠ 0) :
    a.toNat = a.toNat / b.toNat * b.toNat + a.toNat % b.toNat ∧ a.toNat % b.toNat < b.toNat := by
  have hb' : 0 < b.toNat := by bv_omega
  refine ⟨?_, Nat.mod_lt _ hb'⟩
  have := Nat.div_add_mod a.toNat b.toNat
  rw [Nat.mul_comm] at this
  omega

theorem ceil_div_covers : Laws.ceil_div_covers := by
  intro a b hb
  rw [ceil_div_nat a b hb]
  have := div_facts a b hb
  split <;> simp only [Nat.add_mul, Nat.one_mul, Nat.add_zero] <;> omega

theorem ceil_div_tight : Laws.ceil_div_tight := by
  intro a b hb
  rw [ceil_div_nat a b hb]
  have := div_facts a b hb
  have hb' : 0 < b.toNat := by bv_omega
  split <;> simp only [Nat.add_mul, Nat.one_mul, Nat.add_zero] <;> omega

theorem bucket_in_range : Laws.bucket_in_range := by
  intro x width n hw hn
  simp only [bucket]
  generalize x / width = q
  repeat' split
  all_goals (try simp only [BitVec.ule, decide_eq_true_eq] at *)
  all_goals bv_omega

theorem unpack_pack : Laws.unpack_pack := by
  intro hi lo
  simp only [unpack, pack, Halves.mk.injEq]
  constructor <;> bv_decide

theorem rotl_inverse : Laws.rotl_inverse := by
  intro x k h0 h32
  simp only [rotl]
  bv_decide

-- Safety obligations.

theorem Safety.ceil_div : Laws.Safety.ceil_div := by
  intro a b h
  simpa [ceil_div.pre, ceil_div.safe] using h

theorem Safety.bucket : Laws.Safety.bucket := by
  intro x width n h
  simp only [bucket.pre, bucket.safe, Bool.and_eq_true] at *
  exact h.1

theorem Safety.mean : Laws.Safety.mean := by
  intro total count
  simp only [mean.safe]
  bv_decide

theorem Safety.rotl : Laws.Safety.rotl := by
  intro x k h
  simp only [rotl.pre, rotl.safe, Bool.and_eq_true] at *
  bv_decide

-- Each step of spin's loop calls rotl with 1, which meets rotl's
-- precondition, so the guard never fails.
theorem spin_loop_safe (x n i : BitVec 32) : spin.loop1.safe x n i = true := by
  fun_induction spin.loop1.safe x n i
  · rename_i x0 i0 lt hpre
    simp [rotl.pre] at hpre
  · rename_i x0 i0 lt hpre x1 i1 ih
    exact ih
  · rfl

theorem Safety.spin : Laws.Safety.spin := by
  intro x n
  exact spin_loop_safe x n 0

-- The translation: each C++ function, run by the semantics in
-- Claws.Sem within its claws::expects, returns what Code.lean computes.
-- Callees first: a caller uses a callee's lemma instead of its body.

claws_valid ceil_div [Code.ceil_div]
claws_valid bucket [Code.bucket]
claws_valid mean [Code.mean]
claws_valid pack [Code.pack]
claws_valid unpack [Code.unpack]
claws_valid rotl [Code.rotl]
claws_loop spin 1 []
claws_valid spin [Code.spin]

end Bits.Proof
