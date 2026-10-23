-- The laws of the Bank example. A human writes this file and the AI
-- must not edit it. Each law is a `def` of type `Prop`, and PROOF.lean
-- proves it with a theorem of the same name.
--
-- `transfer f t amt` returns (moved, f', t'): whether it moved anything,
-- and the two accounts afterwards.
import Bank.Code

namespace Bank.Laws

open Bank.Code

-- LAW: a transfer never creates or destroys money. The sum is taken in
-- the natural numbers, so a wrapped balance could not hide a loss.
def transfer_conserves : Prop :=
  ∀ f t f' t' : Account, ∀ amt : BitVec 32, ∀ moved : Bool,
    transfer f t amt = (moved, f', t') →
      f'.balance.toNat + t'.balance.toNat = f.balance.toNat + t.balance.toNat

-- LAW: a refused transfer changes nothing.
def refusal_changes_nothing : Prop :=
  ∀ f t f' t' : Account, ∀ amt : BitVec 32,
    transfer f t amt = (false, f', t') → f' = f ∧ t' = t

-- LAW: a transfer that moves money moves exactly amt.
def moves_exactly : Prop :=
  ∀ f t f' t' : Account, ∀ amt : BitVec 32,
    transfer f t amt = (true, f', t') →
      f'.balance.toNat + amt.toNat = f.balance.toNat ∧
      t'.balance.toNat = t.balance.toNat + amt.toNat

-- LAW: a transfer that can happen does happen: refusing is only allowed
-- when `from` cannot cover amt or `to` has no room for it.
def moves_when_possible : Prop :=
  ∀ f t : Account, ∀ amt : BitVec 32,
    amt.toNat ≤ f.balance.toNat → t.balance.toNat + amt.toNat < 2 ^ 32 →
      (transfer f t amt).1 = true

-- LAW: accounts keep their ids.
def ids_unchanged : Prop :=
  ∀ f t f' t' : Account, ∀ amt : BitVec 32, ∀ moved : Bool,
    transfer f t amt = (moved, f', t') → f'.id = f.id ∧ t'.id = t.id

-- LAW: a payment plan never creates or destroys money either.
def plan_conserves : Prop :=
  ∀ f t f' t' : Account, ∀ amt n : BitVec 32,
    pay_in_parts f t amt n = (f', t') →
      f'.balance.toNat + t'.balance.toNat = f.balance.toNat + t.balance.toNat

end Bank.Laws
