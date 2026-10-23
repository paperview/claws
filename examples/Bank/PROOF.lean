-- The proofs of the Bank example's laws. The AI writes this file.
import Std.Tactic.BVDecide
import Bank.LAWS
import Bank.Ast
import Claws.Loop

namespace Bank.Proof

-- BitVec.ule is unused today, but a rewrite of transfer with <= needs it.
set_option linter.unusedSimpArgs false

open Bank.Code

-- A transfer either refuses and returns both accounts unchanged, or moves
-- amt from a balance that covers it into one with room for it.
theorem transfer_cases (f t : Account) (amt : BitVec 32) :
    transfer f t amt = (false, f, t) ∨
    (amt.toNat ≤ f.balance.toNat ∧ t.balance.toNat + amt.toNat < 2 ^ 32 ∧
      transfer f t amt =
        (true, { f with balance := f.balance - amt }, { t with balance := t.balance + amt })) := by
  -- Split every branch of transfer, however it is written, then let
  -- bv_omega settle the bounds in each.
  simp only [transfer]
  repeat' split
  all_goals first
    | exact .inl rfl
    | refine .inr ⟨?_, ?_, rfl⟩ <;> simp only [BitVec.ult, BitVec.ule, decide_eq_true_eq] at * <;> bv_omega

theorem transfer_conserves : Laws.transfer_conserves := by
  intro f t f' t' amt moved h
  rcases transfer_cases f t amt with e | ⟨hle, hroom, e⟩ <;> rw [e] at h <;>
    simp only [Prod.mk.injEq] at h <;> obtain ⟨-, rfl, rfl⟩ := h
  · rfl
  · simp only [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle)]
    bv_omega

theorem refusal_changes_nothing : Laws.refusal_changes_nothing := by
  intro f t f' t' amt h
  rcases transfer_cases f t amt with e | ⟨-, -, e⟩ <;> rw [e] at h <;> simp only [Prod.mk.injEq] at h
  · exact ⟨h.2.1.symm, h.2.2.symm⟩
  · exact absurd h.1 (by decide)

theorem moves_exactly : Laws.moves_exactly := by
  intro f t f' t' amt h
  rcases transfer_cases f t amt with e | ⟨hle, hroom, e⟩ <;> rw [e] at h <;> simp only [Prod.mk.injEq] at h
  · exact absurd h.1 (by decide)
  · obtain ⟨-, rfl, rfl⟩ := h
    constructor <;> simp only <;> bv_omega

theorem moves_when_possible : Laws.moves_when_possible := by
  intro f t amt hle hroom
  simp only [transfer]
  repeat' split
  all_goals first
    | rfl
    | (exfalso; simp only [BitVec.ult, BitVec.ule, decide_eq_true_eq] at *; bv_omega)

theorem ids_unchanged : Laws.ids_unchanged := by
  intro f t f' t' amt moved h
  rcases transfer_cases f t amt with e | ⟨-, -, e⟩ <;> rw [e] at h <;>
    simp only [Prod.mk.injEq] at h <;> obtain ⟨-, rfl, rfl⟩ := h <;> exact ⟨rfl, rfl⟩

-- Each step of the payment plan's loop is one transfer, which conserves.
theorem plan_loop (f t : Account) (amt n i : BitVec 32) :
    let r := pay_in_parts.loop1 f t amt n i
    r.1.balance.toNat + r.2.balance.toNat = f.balance.toNat + t.balance.toNat := by
  fun_induction pay_in_parts.loop1 f t amt n i
  · rename_i f0 t0 i0 lt f1 t1 heq i1 ih
    simp only at ih ⊢
    rw [ih]
    rcases hr : transfer f0 t0 amt with ⟨moved, f2, t2⟩
    rw [hr] at heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact transfer_conserves _ _ _ _ _ _ hr
  · rfl

theorem plan_conserves : Laws.plan_conserves := by
  intro f t f' t' amt n h
  have := plan_loop f t amt n 0
  simp only [pay_in_parts, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact this

-- The translation: each C++ function, run by the semantics in
-- Claws.Sem with any objects as its T& arguments, returns what Code.lean
-- computes and leaves those objects as Code.lean does.

claws_valid transfer [Code.transfer]
claws_loop pay_in_parts 1 []
claws_valid pay_in_parts [Code.pay_in_parts]

-- Why the law asks for two different accounts. In C++, transfer(a, a, 5)
-- on one account holding 10 takes 5 and gives it back: it ends at 10.
example : Claws.Sem.callFn 1000 Ast.prog [Ast.Account.toVal ⟨1, 10⟩] "transfer"
    [.loc ⟨0, []⟩, .loc ⟨0, []⟩, .val (.uint 5)] =
    some (some (.bool true), [Ast.Account.toVal ⟨1, 10⟩]) := by
  simp only [Claws.Sem.callFn]
  claws_run [Claws.Sem.eval]
  all_goals rfl

-- The translation, which copies each T& in and out, ends one copy at 5 and
-- the other at 15, so it cannot describe that call; claws-lean rejects
-- two T& arguments that may overlap.
example : Code.transfer ⟨1, 10⟩ ⟨1, 10⟩ 5 = (true, ⟨1, 5⟩, ⟨1, 15⟩) := by decide

end Bank.Proof
