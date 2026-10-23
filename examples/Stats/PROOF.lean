-- The proofs of the Stats example's laws. The AI writes this file.
import Std.Tactic.BVDecide
import Stats.LAWS
import Stats.Ast
import Claws.Validate

namespace Stats.Proof

open Stats.Code

-- What one `record` step does to each field. Each proof splits every
-- branch of `record`, however many there are, and lets bv_decide finish,
-- so a refactor of `record` that keeps its meaning keeps these proofs.
theorem record_count (s : Stats) (x : BitVec 32) : (record s x).count = s.count + 1 := by
  simp only [record]; repeat' split
  all_goals simp_all

theorem record_total (s : Stats) (x : BitVec 32) : (record s x).total = s.total + x := by
  simp only [record]; repeat' split
  all_goals simp_all

theorem record_min (s : Stats) (x : BitVec 32) :
    (record s x).min ≤ x ∧ (record s x).min ≤ s.min := by
  simp only [record]; repeat' split
  all_goals simp_all <;> bv_decide

theorem record_max (s : Stats) (x : BitVec 32) :
    x ≤ (record s x).max ∧ s.max ≤ (record s x).max := by
  simp only [record]; repeat' split
  all_goals simp_all <;> bv_decide

theorem count_is_length : Laws.count_is_length := by
  intro xs
  induction xs with
  | nil => intro; rfl
  | cons h t ih =>
    intro hl
    simp only [List.length_cons] at hl
    have ht := ih (by omega)
    simp [summarize, record_count, BitVec.toNat_add, ht]
    omega

theorem total_is_sum : Laws.total_is_sum := by
  intro xs
  induction xs with
  | nil => rfl
  | cons h t ih =>
    simp only [summarize, record_total, ih, List.sum_cons]
    exact BitVec.add_comm _ _

theorem min_le_all : Laws.min_le_all := by
  intro xs
  induction xs with
  | nil => simp
  | cons h t ih =>
    intro y hy
    simp only [summarize]
    have := record_min (summarize t) h
    cases List.mem_cons.mp hy with
    | inl e => exact e ▸ this.1
    | inr m => exact BitVec.le_trans this.2 (ih y m)

theorem all_le_max : Laws.all_le_max := by
  intro xs
  induction xs with
  | nil => simp
  | cons h t ih =>
    intro y hy
    simp only [summarize]
    have := record_max (summarize t) h
    cases List.mem_cons.mp hy with
    | inl e => exact e ▸ this.1
    | inr m => exact BitVec.le_trans (ih y m) this.2

-- Inside the range means inside the band; the other branches contradict
-- the bounds.
theorem band_inside (s : Stats) (y : BitVec 32) (lo : s.min ≤ y) (hi : y ≤ s.max) :
    band s y = Band.Inside := by
  simp only [band]
  repeat' split
  all_goals first | rfl | (exfalso; bv_decide)

theorem seen_is_inside : Laws.seen_is_inside := by
  intro xs y hy
  exact band_inside _ y (min_le_all xs y hy) (all_le_max xs y hy)

-- The translation: each C++ function, run by the semantics in
-- Claws.Sem, returns what Code.lean computes.
-- Callees first: a caller uses a callee's lemma instead of its body.

claws_valid no_stats [Code.no_stats]
claws_valid record [Code.record]
claws_valid summarize [Code.summarize]
claws_valid band [Code.band]

end Stats.Proof
