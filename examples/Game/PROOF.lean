-- The proofs of the Game example's laws. The AI writes this file.
-- They follow Bend 2's demo (Copyright 2026 HigherOrderCO, Apache License
-- 2.0); NOTICE says what changed.
--
-- As in Bend's proof, an invariant holds at the start and survives every
-- move: the player stands on a safe cell (on the map, not on a wall, not
-- in the flag's room) and has not won. Bend checks the geometric heart by
-- enumerating the map; here bv_decide proves it for every pair of 32-bit
-- coordinates at once.
import Std.Tactic.BVDecide
import Game.LAWS
import Game.Ast
import Claws.Validate
import Claws.Loop

namespace Game.Proof

open Game.Code

def safe (g : Game) : Prop :=
  g.x < 12 ∧ g.y < 8 ∧ wall g.x g.y = false ∧ ¬(g.x < 3 ∧ g.y < 3) ∧ g.won = false

theorem start_safe : safe start := by
  simp only [safe, start, start_x, start_y, wall, room_w, room_h, map_w, map_h]
  decide

-- The geometric heart: a move from a safe cell lands on a safe cell. Full
-- simp (not simp only) unfolds the map's constants inside the conditions
-- without breaking their decidability instances; every branch then is a
-- fact about two 32-bit coordinates, which bv_decide settles.
theorem step_safe (g : Game) (m : Move) : safe g → safe (step g m) := by
  rcases g with ⟨x, y, won⟩
  intro ⟨hx, hy, hw, hr, hwon⟩
  simp only at hx hy hw hr hwon
  subst hwon
  simp only [wall, room_w, room_h, map_w, map_h] at hw
  cases m
  all_goals simp [safe, step, move_to, move_diag, warp_up, warp_down, warp_left, warp_right, wall, on_flag,
      room_w, room_h, map_w, map_h, flag_x, flag_y]
  all_goals (repeat' split)
  -- dsimp only reduces field projections of structure literals, which
  -- bv_decide would otherwise treat as unknowns. Not simp_all, which
  -- rewrites hypotheses with each other into forms bv_decide loses.
  all_goals (try dsimp only at *)
  all_goals bv_decide

theorem replay_safe (g : Game) (moves : Array Move) (i : BitVec 32) :
    safe g → safe (replay.loop1 g moves i) := by
  fun_induction replay.loop1 g moves i
  · rename_i g0 i0 lt g1 i1 ih
    intro h
    exact ih (step_safe g0 _ h)
  · rename_i g0 i0 nlt
    exact id

theorem played_safe (moves : Array Move) : safe (replay start moves) := by
  simp only [replay]
  exact replay_safe start moves 0 start_safe

theorem you_cant_win : Laws.you_cant_win := by
  intro moves
  exact (played_safe moves).2.2.2.2

-- A safe cell is not the flag's: the flag is inside the room.
theorem never_on_flag : Laws.never_on_flag := by
  intro moves
  have ⟨hx, hy, hw, hr, _⟩ := played_safe moves
  generalize replay start moves = g at *
  simp only [cell]
  repeat' split
  all_goals (try simp_all [on_flag, flag_x, flag_y, start_x, start_y])
  all_goals bv_decide

-- Safety obligation: replay reads moves[i] only below moves.size.

theorem replay_loop_safe (g : Game) (moves : Array Move) (hs : moves.size < 2 ^ 32) (i : BitVec 32) :
    replay.loop1.safe g moves i = true := by
  fun_induction replay.loop1.safe g moves i
  · rename_i g0 i0 lt hcheck
    have : (BitVec.ofNat 32 moves.size).toNat = moves.size := by simp; omega
    have : i0.toNat < moves.size := by bv_omega
    simp [this] at hcheck
  · rename_i g0 i0 lt hcheck g1 i1 ih
    exact ih
  · rfl

theorem Safety.replay : Laws.Safety.replay := by
  intro g moves hs
  simp only [replay.safe]
  exact replay_loop_safe g moves hs 0

-- The translation: each C++ function, run by the semantics in
-- Claws.Sem within its claws::expects, returns what Code.lean computes.
-- Callees first: a caller uses a callee's lemma instead of its body.

claws_valid map_w [Code.map_w]
claws_valid map_h [Code.map_h]
claws_valid room_w [Code.room_w]
claws_valid room_h [Code.room_h]
claws_valid flag_x [Code.flag_x]
claws_valid flag_y [Code.flag_y]
claws_valid start_x [Code.start_x]
claws_valid start_y [Code.start_y]
claws_valid wall [Code.wall]
claws_valid on_flag [Code.on_flag]
claws_valid warp_up [Code.warp_up]
claws_valid warp_down [Code.warp_down]
claws_valid warp_left [Code.warp_left]
claws_valid warp_right [Code.warp_right]
claws_valid start [Code.start]
claws_valid cell [Code.cell]
claws_valid is_won [Code.is_won]
claws_valid key [Code.key]
claws_valid move_to [Code.move_to]
claws_valid move_diag [Code.move_diag]
claws_valid step [Code.step]
claws_loop replay 1 []
claws_valid replay [Code.replay]

end Game.Proof
