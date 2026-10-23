-- The laws of the Game example, ported from Bend 2's demo. A human writes
-- this file and the AI must not edit it. Each law is a `def` of type
-- `Prop`, and PROOF.lean proves it with a theorem of the same name.
import Game.Code

namespace Game.Laws

open Game.Code

-- LAW: for any sequence of moves, replaying them from the start can never
-- lead to victory.
def you_cant_win : Prop :=
  ∀ moves : Array Move, is_won (replay start moves) = false

-- LAW: the player never stands on the flag the driver draws: no sequence
-- of moves puts the player on a cell that `cell` reports as the flag.
def never_on_flag : Prop :=
  ∀ moves : Array Move,
    let g := replay start moves
    cell g.x g.y ≠ Cell.Flag

end Game.Laws
