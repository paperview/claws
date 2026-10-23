-- The laws of the Loops example. A human writes this file and the AI
-- must not edit it. Each law is a `def` of type `Prop`, and PROOF.lean
-- proves it with a theorem of the same name.
import Loops.Code

namespace Loops.Laws

open Loops.Code

-- LAW: replicate makes exactly n values.
def replicate_length : Prop :=
  ∀ x n : BitVec 32, (replicate x n).length = n.toNat

-- LAW: every value replicate makes is x.
def replicate_all : Prop :=
  ∀ x n y : BitVec 32, y ∈ replicate x n → y = x

-- LAW: twice the triangle number is n * (n - 1), wrapping.
def triangle_formula : Prop :=
  ∀ n : BitVec 32, 2 * triangle n = n * (n - 1)

-- LAW: counting cells one at a time gives w * h, wrapping.
def cells_product : Prop :=
  ∀ w h : BitVec 32, cells w h = w * h

end Loops.Laws
