-- The proofs of the Vectors example's laws and safety obligations. The AI
-- writes this file. It follows the rules in CLAUDE.md: every branch is
-- split uniformly, and every leaf closes with bv_omega or simp.
import Std.Tactic.BVDecide
import Vectors.LAWS
import Vectors.Ast
import Claws.Loop

namespace Vectors.Proof

open Vectors.Code

-- Reading an array after writing it.

theorem get_set_ne (v : Array (BitVec 32)) (i j : Nat) (x : BitVec 32) (h : i ≠ j) :
    (v.setIfInBounds i x)[j]! = v[j]! := by
  simp only [getElem!_def, Array.getElem?_setIfInBounds_ne h]

theorem get_set_self (v : Array (BitVec 32)) (i : Nat) (x : BitVec 32) (h : i < v.size) :
    (v.setIfInBounds i x)[i]! = x := by
  simp only [getElem!_def, Array.getElem?_setIfInBounds_self_of_lt h]

-- A loop counter below `BitVec.ofNat 32 v.size` is below v.size, and one
-- more than it still fits in 32 bits.
theorem below_size (v : Array (BitVec 32)) (hs : v.size < 2 ^ 32) (i : BitVec 32)
    (h : i < BitVec.ofNat 32 v.size) : i.toNat < v.size ∧ (i + 1).toNat = i.toNat + 1 := by
  have : (BitVec.ofNat 32 v.size).toNat = v.size := by simp; omega
  constructor <;> bv_omega

-- max_index

-- The loop keeps best below i, and v[best] at least every element before i.
theorem max_loop (v : Array (BitVec 32)) (hs : v.size < 2 ^ 32) (best i : BitVec 32) :
    best.toNat < i.toNat → i.toNat ≤ v.size → (∀ j < i.toNat, v[j]! ≤ v[best.toNat]!) →
      (max_index.loop1 v best i).toNat < v.size ∧
      ∀ j < v.size, v[j]! ≤ v[(max_index.loop1 v best i).toNat]! := by
  fun_induction max_index.loop1 v best i
  · rename_i best0 i0 lt best1 i1 ih
    intro hb hi hall
    have ⟨hlt, hinc⟩ := below_size v hs i0 lt
    simp only [best1, i1] at *
    apply ih
    · split <;> bv_omega
    · bv_omega
    · intro j hj
      rw [hinc] at hj
      split
      · rename_i hgt
        simp only [BitVec.ult, decide_eq_true_eq] at hgt
        rcases Nat.lt_or_ge j i0.toNat with h1 | h1
        · have := hall j h1
          bv_omega
        · have : j = i0.toNat := by omega
          subst this
          exact BitVec.le_refl _
      · rename_i hgt
        simp only [BitVec.ult, decide_eq_true_eq] at hgt
        rcases Nat.lt_or_ge j i0.toNat with h1 | h1
        · exact hall j h1
        · have : j = i0.toNat := by omega
          subst this
          bv_omega
  · rename_i best0 i0 nlt
    intro hb hi hall
    have : (BitVec.ofNat 32 v.size).toNat = v.size := by simp; omega
    have : i0.toNat = v.size := by bv_omega
    exact ⟨by omega, fun j hj => hall j (by omega)⟩

theorem max_index_spec (v : Array (BitVec 32)) (hs : v.size < 2 ^ 32) (h0 : v.size ≠ 0) :
    (max_index v).toNat < v.size ∧ ∀ j < v.size, v[j]! ≤ v[(max_index v).toNat]! := by
  simp only [max_index]
  apply max_loop v hs 0 1
  · decide
  · simp; omega
  · intro j hj
    have : j = 0 := by simp at hj; omega
    subst this
    exact BitVec.le_refl _

theorem max_index_in_range : Laws.max_index_in_range := fun v hs h0 => (max_index_spec v hs h0).1

theorem max_index_is_max : Laws.max_index_is_max := fun v hs h0 => (max_index_spec v hs h0).2

-- fill

theorem fill_loop_size (v : Array (BitVec 32)) (x i : BitVec 32) :
    (fill.loop1 v x i).size = v.size := by
  fun_induction fill.loop1 v x i
  · rename_i v0 i0 lt v1 i1 ih
    simp only [v1] at ih
    rw [ih, Array.size_setIfInBounds]
  · rfl

-- The loop keeps every element before i equal to x.
theorem fill_loop (v : Array (BitVec 32)) (hs : v.size < 2 ^ 32) (x i : BitVec 32) :
    i.toNat ≤ v.size → (∀ j < i.toNat, v[j]! = x) → ∀ j < v.size, (fill.loop1 v x i)[j]! = x := by
  fun_induction fill.loop1 v x i
  · rename_i v0 i0 lt v1 i1 ih
    intro hi hall
    have ⟨hlt, hinc⟩ := below_size v0 hs i0 lt
    simp only [v1, i1, Array.size_setIfInBounds] at *
    apply ih hs (by omega)
    intro j hj
    rw [hinc] at hj
    rcases Nat.lt_or_ge j i0.toNat with h1 | h1
    · rw [get_set_ne _ _ _ _ (by omega)]
      exact hall j h1
    · have : j = i0.toNat := by omega
      subst this
      exact get_set_self _ _ _ hlt
  · rename_i v0 i0 nlt
    intro hi hall j hj
    have : (BitVec.ofNat 32 v0.size).toNat = v0.size := by simp; omega
    have : i0.toNat = v0.size := by bv_omega
    exact hall j (by omega)

theorem fill_size : Laws.fill_size := by
  intro v x
  simp only [fill]
  exact fill_loop_size v x 0

theorem fill_all : Laws.fill_all := by
  intro v x hs j hj
  simp only [fill]
  exact fill_loop v hs x 0 (by simp) (by simp) j hj

-- evens

theorem evens_loop_even (xs out : Array (BitVec 32)) (i : BitVec 32) :
    (∀ y ∈ out, y % 2 = 0) → ∀ y ∈ evens.loop1 xs out i, y % 2 = 0 := by
  fun_induction evens.loop1 xs out i
  · rename_i out0 i0 lt out1 i1 ih
    intro hall
    apply ih
    simp only [out1]
    split
    · rename_i heven
      intro y hy
      rcases Array.mem_push.mp hy with m | e
      · exact hall y m
      · subst e
        simpa using heven
    · exact hall
  · rename_i out0 i0 nlt
    exact id

theorem evens_loop_size (xs out : Array (BitVec 32)) (hs : xs.size < 2 ^ 32) (i : BitVec 32) :
    out.size ≤ i.toNat → i.toNat ≤ xs.size → (evens.loop1 xs out i).size ≤ xs.size := by
  fun_induction evens.loop1 xs out i
  · rename_i out0 i0 lt out1 i1 ih
    intro ho hi
    have ⟨hlt, hinc⟩ := below_size xs hs i0 lt
    simp only [out1, i1] at *
    apply ih
    · split <;> (try simp only [Array.size_push]) <;> omega
    · omega
  · rename_i out0 i0 nlt
    intro ho hi
    omega

theorem evens_even : Laws.evens_even := by
  intro xs y hy
  simp only [evens] at hy
  exact evens_loop_even xs #[] 0 (by simp) y hy

theorem evens_size : Laws.evens_size := by
  intro xs hs
  simp only [evens]
  exact evens_loop_size xs #[] hs 0 (by simp) (by simp)

-- histogram

theorem histogram_loop_size (xs : Array (BitVec 32)) (width n : BitVec 32) (counts : Array (BitVec 32))
    (i : BitVec 32) : (histogram.loop1 xs width n counts i).size = counts.size := by
  fun_induction histogram.loop1 xs width n counts i
  · rename_i counts0 i0 lt counts1 i1 ih
    simp only [counts1] at ih
    rw [ih, Array.size_setIfInBounds]
  · rfl

theorem histogram_size : Laws.histogram_size := by
  intro xs width n
  simp only [histogram]
  rw [histogram_loop_size]
  simp

-- bucket, as in the Bits example: every value lands in one of n buckets.
theorem bucket_lt (x width n : BitVec 32) (hn : n ≠ 0) : bucket x width n < n := by
  simp only [bucket]
  generalize x / width = q
  repeat' split
  all_goals (try simp only [BitVec.ule, decide_eq_true_eq] at *)
  all_goals bv_omega

-- Safety obligations.

theorem max_loop_safe (v : Array (BitVec 32)) (hs : v.size < 2 ^ 32) (best i : BitVec 32) :
    best.toNat < i.toNat → max_index.loop1.safe v best i = true := by
  fun_induction max_index.loop1.safe v best i
  · rename_i best0 i0 lt hcheck
    intro hb
    have ⟨hlt, _⟩ := below_size v hs i0 lt
    have hb' : best0.toNat < v.size := by omega
    simp [hlt, hb'] at hcheck
  · rename_i best0 i0 lt hcheck best1 i1 ih
    intro hb
    have ⟨hlt, hinc⟩ := below_size v hs i0 lt
    simp only [best1, i1] at *
    apply ih
    split <;> bv_omega
  · intro; rfl

theorem Safety.max_index : Laws.Safety.max_index := by
  intro v hs _
  simp only [max_index.safe]
  exact max_loop_safe v hs 0 1 (by decide)

theorem fill_loop_safe (v : Array (BitVec 32)) (hs : v.size < 2 ^ 32) (x i : BitVec 32) :
    fill.loop1.safe v x i = true := by
  fun_induction fill.loop1.safe v x i
  · rename_i v0 i0 lt hcheck
    have ⟨hlt, _⟩ := below_size v0 hs i0 lt
    simp [hlt] at hcheck
  · rename_i v0 i0 lt hcheck v1 i1 ih
    simp only [v1] at ih
    exact ih (by simpa using hs)
  · rfl

theorem Safety.fill : Laws.Safety.fill := by
  intro v x hs
  simp only [fill.safe]
  exact fill_loop_safe v hs x 0

theorem evens_loop_safe (xs out : Array (BitVec 32)) (hs : xs.size < 2 ^ 32) (i : BitVec 32) :
    out.size ≤ i.toNat → evens.loop1.safe xs out i = true := by
  fun_induction evens.loop1.safe xs out i
  · rename_i out0 i0 lt hcheck
    intro ho
    have ⟨hlt, _⟩ := below_size xs hs i0 lt
    simp only [hlt, decide_true, Bool.true_and, Bool.not_eq_true'] at hcheck
    split at hcheck <;> simp_all <;> omega
  · rename_i out0 i0 lt hcheck out1 i1 ih
    intro ho
    have ⟨hlt, hinc⟩ := below_size xs hs i0 lt
    simp only [out1, i1] at *
    apply ih
    split <;> (try simp only [Array.size_push]) <;> omega
  · intro; rfl

theorem Safety.evens : Laws.Safety.evens := by
  intro xs hs
  simp only [evens.safe]
  exact evens_loop_safe xs #[] hs 0 (by simp)

theorem Safety.bucket : Laws.Safety.bucket := by
  intro x width n h
  simp only [bucket.pre, bucket.safe, Bool.and_eq_true] at *
  exact h.1

-- The histogram's loop indexes counts with bucket's result, which is
-- below n, which is the size of counts: the functional fact bucket_lt is
-- what makes the write safe.
theorem histogram_loop_safe (xs : Array (BitVec 32)) (hs : xs.size < 2 ^ 32) (width n : BitVec 32)
    (hw : width ≠ 0) (hn : n ≠ 0) (counts : Array (BitVec 32)) (i : BitVec 32) :
    counts.size = n.toNat → histogram.loop1.safe xs width n counts i = true := by
  fun_induction histogram.loop1.safe xs width n counts i
  · rename_i counts0 i0 lt hcheck
    intro hc
    have ⟨hlt, _⟩ := below_size xs hs i0 lt
    have hb := BitVec.lt_def.mp (bucket_lt (xs[i0.toNat]!) width n hn)
    -- simp_all rewrites hb and hcheck alike, so they stay comparable.
    simp_all [bucket.pre]
    omega
  · rename_i counts0 i0 lt hcheck counts1 i1 ih
    intro hc
    simp only [counts1] at ih
    exact ih (by rw [Array.size_setIfInBounds]; exact hc)
  · intro; rfl

theorem Safety.histogram : Laws.Safety.histogram := by
  intro xs width n hs h
  simp only [histogram.pre, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  simp only [histogram.safe]
  exact histogram_loop_safe xs hs width n h.1 h.2 _ 0 (by simp)

-- The translation: each C++ function, run by the semantics in
-- Claws.Sem, returns what Code.lean computes. Callees first, and each
-- loop before its function.

claws_valid bucket [Code.bucket]
claws_loop fill 1 []
claws_valid fill [Code.fill]
claws_loop max_index 1 []
claws_valid max_index [Code.max_index]
claws_loop evens 1 []
claws_valid evens [Code.evens]
claws_loop histogram 1 []
claws_valid histogram [Code.histogram]

end Vectors.Proof
