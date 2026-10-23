-- The proofs of the Loops example's laws. The AI writes this file.
--
-- Each loop gets an invariant proved by functional induction on its
-- loop function (`fun_induction`), which follows the loop's own steps.
-- The invariant holds for any counter at most the bound, so the law
-- follows by starting the counter at 0.
import Std.Tactic.BVDecide
import Loops.LAWS
import Loops.Ast
import Claws.Loop

namespace Loops.Proof

open Loops.Code

theorem replicate_loop_length (x n : BitVec 32) (xs : List (BitVec 32)) (i : BitVec 32) :
    i ≤ n → (replicate.loop1 x n xs i).length = xs.length + (n - i).toNat := by
  fun_induction replicate.loop1 x n xs i
  all_goals intro hi
  · rename_i xs0 i0 lt xs1 i1 ih
    simp only [xs1, i1] at *
    rw [ih (by bv_omega)]
    simp only [List.length_cons]
    bv_omega
  · bv_omega

theorem replicate_loop_mem (x n : BitVec 32) (xs : List (BitVec 32)) (i y : BitVec 32) :
    y ∈ replicate.loop1 x n xs i → y = x ∨ y ∈ xs := by
  fun_induction replicate.loop1 x n xs i
  · rename_i xs0 i0 lt xs1 i1 ih
    intro hy
    rcases ih hy with e | m
    · exact .inl e
    · simp only [xs1, List.mem_cons] at m
      exact m
  · exact .inr

theorem replicate_length : Laws.replicate_length := by
  intro x n
  simp only [replicate]
  rw [replicate_loop_length x n [] 0 (by bv_omega)]
  simp

theorem replicate_all : Laws.replicate_all := by
  intro x n y hy
  simp only [replicate] at hy
  simpa using replicate_loop_mem x n [] 0 y hy

theorem triangle_loop (n s i : BitVec 32) :
    i ≤ n → 2 * triangle.loop1 n s i + i * (i - 1) = 2 * s + n * (n - 1) := by
  fun_induction triangle.loop1 n s i
  all_goals intro hi
  · rename_i s0 i0 lt s1 i1 ih
    simp only [s1, i1] at *
    have := ih (by bv_omega)
    grind
  · rename_i s0 i0 nlt
    have : i0 = n := by bv_omega
    subst this
    rfl

theorem triangle_formula : Laws.triangle_formula := by
  intro n
  have := triangle_loop n 0 0 (by bv_omega)
  simp only [triangle]
  grind

theorem cells_inner (w c x : BitVec 32) : x ≤ w → cells.loop2 w c x = c + (w - x) := by
  fun_induction cells.loop2 w c x
  all_goals intro hx
  · rename_i c0 x0 lt c1 x1 ih
    simp only [c1, x1] at *
    rw [ih (by bv_omega)]
    grind
  · rename_i c0 x0 nlt
    have : x0 = w := by bv_omega
    subst this
    grind

theorem cells_outer (w h c y : BitVec 32) : y ≤ h → cells.loop1 w h c y = c + w * (h - y) := by
  fun_induction cells.loop1 w h c y
  all_goals intro hy
  · rename_i c0 y0 lt c1 y1 ih
    simp only [c1, y1] at *
    rw [ih (by bv_omega), cells_inner w c0 0 (by bv_omega)]
    grind
  · rename_i c0 y0 nlt
    have : y0 = h := by bv_omega
    subst this
    grind

theorem cells_product : Laws.cells_product := by
  intro w h
  simp only [cells]
  rw [cells_outer w h 0 0 (by bv_omega)]
  grind

-- The translation: each C++ function, run by the semantics in
-- Claws.Sem, returns what Code.lean computes. A loop is proven first, by
-- induction over its function in Code.lean, and inner loops before outer.

claws_loop replicate 1 []
claws_valid replicate [Code.replicate]
claws_loop triangle 1 []
claws_valid triangle [Code.triangle]
claws_loop cells 2 []
claws_loop cells 1 []
claws_valid cells [Code.cells]

end Loops.Proof
