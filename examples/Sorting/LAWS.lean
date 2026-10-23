-- The laws of the Sorting example. A human writes this file and the AI
-- must not edit it. Each law is a `def` of type `Prop`, and PROOF.lean
-- proves it with a theorem of the same name.
import Sorting.Code

namespace Sorting.Laws

open Sorting.Code

-- LAW: sort puts every element in order with every element after it.
def sort_sorted : Prop :=
  ∀ (o : Order) (xs : List (BitVec 32)),
    (sort o xs).Pairwise (fun a b => in_order o a b = true)

-- LAW: sort returns a rearrangement of its input: nothing lost, nothing added.
def sort_perm : Prop :=
  ∀ (o : Order) (xs : List (BitVec 32)), (sort o xs).Perm xs

-- LAW: sorting does not change the sum, wrapping included.
def sort_sum : Prop :=
  ∀ (o : Order) (xs : List (BitVec 32)), sum (sort o xs) = sum xs

end Sorting.Laws
