-- The proofs of the Sorting example's laws. The AI writes this file.
import Std.Tactic.BVDecide
import Sorting.LAWS
import Sorting.Ast
import Claws.Validate

namespace Sorting.Proof

open Sorting.Code

-- in_order is a total order on each side.
theorem in_order_total (o : Order) (a b : BitVec 32) :
    in_order o a b = false → in_order o b a = true := by
  cases o <;> simp only [in_order] <;> bv_decide

theorem in_order_trans (o : Order) (a b c : BitVec 32) :
    in_order o a b = true → in_order o b c = true → in_order o a c = true := by
  cases o <;> simp only [in_order] <;> bv_decide

theorem insert_perm (o : Order) (x : BitVec 32) (xs : List (BitVec 32)) :
    (Code.insert o x xs).Perm (x :: xs) := by
  induction xs with
  | nil => simp [Code.insert]
  | cons h t ih =>
    simp only [Code.insert]
    split
    · exact List.Perm.refl _
    · exact (ih.cons h).trans (List.Perm.swap x h t)

theorem sort_perm : Laws.sort_perm := by
  intro o xs
  induction xs with
  | nil => simp [sort]
  | cons h t ih =>
    simp only [sort]
    exact (insert_perm o h _).trans (ih.cons h)

theorem insert_sorted (o : Order) (x : BitVec 32) (xs : List (BitVec 32))
    (hs : xs.Pairwise (fun a b => in_order o a b = true)) :
    (Code.insert o x xs).Pairwise (fun a b => in_order o a b = true) := by
  induction xs with
  | nil => simp [Code.insert]
  | cons h t ih =>
    rw [List.pairwise_cons] at hs
    simp only [Code.insert]
    split
    · next hx =>
      rw [List.pairwise_cons]
      refine ⟨?_, List.pairwise_cons.mpr hs⟩
      intro y hy
      cases List.mem_cons.mp hy with
      | inl e => exact e ▸ hx
      | inr m => exact in_order_trans o x h y hx (hs.1 y m)
    · next hx =>
      rw [List.pairwise_cons]
      refine ⟨?_, ih hs.2⟩
      intro y hy
      cases List.mem_cons.mp ((insert_perm o x t).mem_iff.mp hy) with
      | inl e => exact e ▸ in_order_total o x h (by simpa using hx)
      | inr m => exact hs.1 y m

theorem sort_sorted : Laws.sort_sorted := by
  intro o xs
  induction xs with
  | nil => simp [sort]
  | cons h t ih =>
    simp only [sort]
    exact insert_sorted o h _ ih

theorem sum_perm {xs ys : List (BitVec 32)} (p : xs.Perm ys) : sum xs = sum ys := by
  induction p with
  | nil => rfl
  | cons x _ ih => simp only [sum, ih]
  | swap x y l =>
    simp only [sum]
    bv_decide
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem sort_sum : Laws.sort_sum := by
  intro o xs
  exact sum_perm (sort_perm o xs)

-- The translation: each C++ function, run by the semantics in
-- Claws.Sem within its claws::expects, returns what Code.lean computes.
-- Callees first: a caller uses a callee's lemma instead of its body.

claws_valid in_order [Code.in_order]
claws_valid insert [Code.insert]
claws_valid sort [Code.sort]
claws_valid sum [Code.sum]

end Sorting.Proof
