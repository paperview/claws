-- The proofs of the Clamp example's laws. The AI writes this file.
import Std.Tactic.BVDecide
import Claws.Validate
import Clamp.LAWS
import Clamp.Ast

namespace Clamp.Proof

open Clamp.Code

theorem clamp_in_range : Laws.clamp_in_range := by
  intro x lo hi h
  simp only [clamp, contains]
  bv_decide

theorem clamp_keeps : Laws.clamp_keeps := by
  intro x lo hi h
  simp only [contains] at h
  simp only [clamp]
  bv_decide

theorem widen_holds_new : Laws.widen_holds_new := by
  intro r x
  simp only [widen, contains, Code.min, Code.max]
  bv_decide

theorem widen_holds_old : Laws.widen_holds_old := by
  intro r x y h
  simp only [contains] at h
  simp only [widen, contains, Code.min, Code.max]
  bv_decide

theorem offset_within_span : Laws.offset_within_span := by
  intro r x h
  simp only [contains] at h
  simp only [span]
  bv_decide

-- The translation: each C++ function, run by the semantics in
-- Claws.Sem, returns what its translation in Code.lean computes.
-- Callees first: a caller uses a callee's lemma instead of its body.

claws_valid min [Code.min]
claws_valid max [Code.max]
claws_valid clamp [Code.clamp]
claws_valid contains [Code.contains]
claws_valid span [Code.span]
claws_valid widen [Code.widen]

end Clamp.Proof
