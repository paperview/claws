-- The proofs of the Utf8 example's laws. The AI writes this file.
--
-- Most proofs follow one recipe: unfold the code, rewrite each lookup in
-- the `first` table into a description of the byte's range (checked
-- against all 256 entries by `decide`), turn each comparison with
-- `p.size` into a BitVec comparison, and let `bv_decide` check every
-- path at once. The bytes of p stay unknowns, so each proof covers every
-- possible input.
import Std.Tactic.BVDecide
import Utf8.LAWS
import Utf8.Ast
import Claws.Loop

namespace Utf8.Proof

open Utf8.Code Utf8.Laws

-- One tactic list serves every goal of a proof, so some goals leave
-- some of its lemmas unused.
set_option linter.unusedSimpArgs false

-- Specifications

theorem scalar_iff (r : BitVec 32) : scalar r ↔ (r < 0xD800 ∨ (0xDFFF < r ∧ r ≤ 0x10FFFF)) := by
  simp only [scalar]; bv_omega

-- encode, with BitVec arithmetic in place of Nat.
theorem encode_bv (r : BitVec 32) : encode r =
    if r < 0x80 then [r.setWidth 8]
    else if r < 0x800 then [((r >>> 6) + 0xC0).setWidth 8, ((r % 0x40) + 0x80).setWidth 8]
    else if r < 0x10000 then
      [((r >>> 12) + 0xE0).setWidth 8, (((r >>> 6) % 0x40) + 0x80).setWidth 8, ((r % 0x40) + 0x80).setWidth 8]
    else
      [((r >>> 18) + 0xF0).setWidth 8, (((r >>> 12) % 0x40) + 0x80).setWidth 8,
       (((r >>> 6) % 0x40) + 0x80).setWidth 8, ((r % 0x40) + 0x80).setWidth 8] := by
  simp only [encode]
  repeat' split
  all_goals (try simp only [List.cons.injEq, and_true])
  all_goals (try (exfalso; bv_omega))
  all_goals (repeat' apply And.intro)
  all_goals (apply BitVec.eq_of_toNat_eq; simp [Nat.shiftRight_eq_div_pow] at * <;> omega)

-- The tables

-- Go's `first` table, by ranges of the byte.
def firstSpec (b : BitVec 8) : BitVec 8 :=
  if b < 0x80 then 0xF0 else if b < 0xC2 then 0xF1 else if b < 0xE0 then 0x02
  else if b = 0xE0 then 0x13 else if b = 0xED then 0x23 else if b < 0xF0 then 0x03
  else if b = 0xF0 then 0x34 else if b < 0xF4 then 0x04 else if b = 0xF4 then 0x44 else 0xF1

-- Checked entry by entry. Plain decide, unlike decide +kernel, says
-- which way a wrong table fails.
set_option maxRecDepth 10000 in
theorem first_eq : ∀ b : BitVec 8, first[b.toNat]! = firstSpec b := by decide

-- The second-byte ranges of Go's accept_ranges, by the first byte.
def loSpec (b : BitVec 8) : BitVec 8 :=
  if b = 0xE0 then 0xA0 else if b = 0xF0 then 0x90 else if b < 0xC2 ∨ 0xF4 < b then 0 else 0x80
def hiSpec (b : BitVec 8) : BitVec 8 :=
  if b = 0xED then 0x9F else if b = 0xF4 then 0x8F else if b < 0xC2 ∨ 0xF4 < b then 0 else 0xBF

theorem lo_eq : ∀ b : BitVec 8, (accept_ranges[((firstSpec b).setWidth 32 >>> (4 : BitVec 32)).toNat]!).lo = loSpec b := by
  decide +kernel
theorem hi_eq : ∀ b : BitVec 8, (accept_ranges[((firstSpec b).setWidth 32 >>> (4 : BitVec 32)).toNat]!).hi = hiSpec b := by
  decide +kernel

-- Comparisons with a size, as BitVec comparisons

theorem toNat_lt_size {α : Type} {p : Array α} (hs : p.size < 2 ^ 32) (k : BitVec 32) :
    k.toNat < p.size ↔ k < BitVec.ofNat 32 p.size := by
  rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs]

theorem toNat_lt_lit (k : BitVec 32) (n : Nat) (h : n < 2 ^ 32) : k.toNat < n ↔ k < BitVec.ofNat 32 n := by
  rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem toNat_eq_size {α : Type} {p : Array α} (hs : p.size < 2 ^ 32) (k : BitVec 32) :
    k.toNat = p.size ↔ k = BitVec.ofNat 32 p.size := by
  rw [← BitVec.toNat_inj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs]

-- A prefix of p from position k, as reads of p in the form the code
-- writes them (`p[(pos + 1).toNat]!`), so that bv_decide sees the same
-- unknowns on both sides.

theorem cons_prefix_drop (p : Array (BitVec 8)) (k : Nat) (a : BitVec 8) (l : List (BitVec 8)) :
    (a :: l) <+: p.toList.drop k ↔ k < p.size ∧ a = p[k]! ∧ l <+: p.toList.drop (k + 1) := by
  by_cases h : k < p.size
  · rw [List.drop_eq_getElem_cons (by simpa using h)]
    simp [List.cons_prefix_cons, h]
  · have : p.toList.drop k = [] := by simp; omega
    simp [this, h]

-- A read at pos + j, in the form the code writes it.
theorem natRead (p : Array (BitVec 8)) (hs : p.size < 2 ^ 32) (pos : BitVec 32) (j : Nat) :
    p[pos.toNat + j]! = if pos.toNat + j < p.size then p[(pos + BitVec.ofNat 32 j).toNat]! else 0 := by
  split
  · congr 1; simp [BitVec.toNat_add]; omega
  · simp [getElem!_neg, *]; rfl

theorem add_lt_size (p : Array (BitVec 8)) (hs : p.size < 2 ^ 32) (pos : BitVec 32) (hpos : pos.toNat ≤ p.size)
    (j : Nat) :
    pos.toNat + j < p.size ↔ j < 2 ^ 32 ∧ BitVec.ofNat 32 j < BitVec.ofNat 32 p.size - pos := by
  rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_sub, BitVec.toNat_ofNat]
  constructor
  · intro h; refine ⟨by omega, ?_⟩; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hs]; omega
  · rintro ⟨hj, h⟩; rw [Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hs] at h; omega

-- Results and encodings, field by field

theorem decoded_eq (a b : Decoded) : a = b ↔ a.r = b.r ∧ a.size = b.size := by
  cases a; cases b; simp

theorem toNat_eq_encode_len (x r : BitVec 32) : x.toNat = (encode r).length ↔
    x = (if r < 0x80 then 1 else if r < 0x800 then 2 else if r < 0x10000 then 3 else 4) := by
  rw [encode_bv]
  repeat' split
  all_goals (simp only [List.length_cons, List.length_nil]; bv_omega)

theorem ite_prefix (c : Prop) [Decidable c] (a b l : List (BitVec 8)) :
    (if c then a else b) <+: l ↔ (c ∧ a <+: l) ∨ (¬c ∧ b <+: l) := by
  split <;> simp [*]

theorem encode_len_bv (r : BitVec 32) : BitVec.ofNat 32 (encode r).length =
    (if r < 0x80 then 1 else if r < 0x800 then 2 else if r < 0x10000 then 3 else 4) := by
  rw [encode_bv]
  repeat' split
  all_goals rfl

-- Laws about one rune

theorem valid_rune_scalar : Laws.valid_rune_scalar := by
  intro r
  simp only [valid_rune, scalar_iff, surrogate_min, surrogate_max, max_rune]
  repeat' split
  all_goals (try simp only [true_iff, false_iff, iff_true, iff_false] at *)
  all_goals bv_decide

-- Splitting before unfolding the constants keeps each `if` condition
-- intact, so `split` can use it.
theorem rune_len_encode : Laws.rune_len_encode := by
  intro r
  rw [encode_bv, scalar_iff]
  refine ⟨fun h => ?_, fun h => ?_⟩
  all_goals simp only [rune_len]
  repeat' split
  all_goals (try simp only [rune1_max, rune2_max, rune3_max, surrogate_min, surrogate_max, max_rune] at *)
  all_goals (try simp only [List.length_cons, List.length_nil] at *)
  all_goals (try simp only [BitVec.ofNat_eq_ofNat] at *)
  all_goals bv_decide

theorem append_encodes : Laws.append_encodes := by
  intro p r _
  rw [encode_bv, encode_bv, scalar_iff]
  refine ⟨fun h => ?_, fun h => ?_⟩
  all_goals simp only [append_rune]
  repeat' split
  all_goals (try simp only [rune1_max, rune2_max, rune3_max, surrogate_min, surrogate_max, max_rune,
    t2, t3, t4, tx, maskx, rune_error_byte0, rune_error_byte1, rune_error_byte2] at *)
  all_goals (try simp only [Array.toList_push, List.append_assoc, List.cons_append, List.nil_append,
    List.append_cancel_left_eq, List.cons.injEq, and_true] at *)
  all_goals (try (repeat' apply And.intro))
  all_goals bv_decide

theorem decode_sound : Laws.decode_sound := by
  intro p pos hs hpos
  have hpos' : pos ≤ BitVec.ofNat 32 p.size := by
    rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs]; exact hpos
  simp only [decode_rune, decoded_eq, apply_ite Decoded.r, apply_ite Decoded.size, first_eq, lo_eq, hi_eq,
    toNat_eq_encode_len]
  simp only [scalar_iff, toNat_eq_encode_len, encode_bv, ite_prefix, cons_prefix_drop, List.nil_prefix, and_true,
    Nat.add_assoc, Nat.reduceAdd, natRead p hs, add_lt_size p hs pos hpos, toNat_lt_size hs, toNat_eq_size hs,
    BitVec.ofNat_eq_ofNat, Nat.reducePow, Nat.reduceLT, true_and, firstSpec, loSpec, hiSpec,
    rune_error, as, locb, hicb, maskx, mask2, mask3, mask4]
  bv_decide

-- The encoding of a scalar value at pos decodes to it.
theorem decode_of_prefix (p : Array (BitVec 8)) (hs : p.size < 2 ^ 32) (pos : BitVec 32)
    (hpos : pos.toNat ≤ p.size) (r : BitVec 32) (hr : scalar r)
    (hpre : encode r <+: p.toList.drop pos.toNat) :
    decode_rune p pos = { r := r, size := BitVec.ofNat 32 (encode r).length } := by
  have hfit : BitVec.ofNat 32 (encode r).length ≤ BitVec.ofNat 32 p.size - pos := by
    have := hpre.length_le
    simp only [List.length_drop, Array.length_toList] at this
    have h4 : (encode r).length ≤ 4 := by rw [encode_bv]; repeat' split
                                          all_goals simp
    simp only [BitVec.le_def, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hpos' : pos ≤ BitVec.ofNat 32 p.size := by
    rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs]; exact hpos
  simp only [decode_rune, decoded_eq, apply_ite Decoded.r, apply_ite Decoded.size, first_eq, lo_eq, hi_eq,
    encode_len_bv] at *
  simp only [scalar_iff, encode_bv, ite_prefix, cons_prefix_drop, List.nil_prefix, and_true,
    Nat.add_assoc, Nat.reduceAdd, natRead p hs, add_lt_size p hs pos hpos, toNat_lt_size hs,
    BitVec.ofNat_eq_ofNat, Nat.reducePow, Nat.reduceLT, true_and, firstSpec, loSpec, hiSpec,
    rune_error, as, locb, hicb, maskx, mask2, mask3, mask4] at *
  bv_decide

theorem decode_encoded : Laws.decode_encoded := by
  intro b a r hr hlen
  have hb : (BitVec.ofNat 32 b.length).toNat = b.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simp at hlen; omega)]
  apply decode_of_prefix _ (by simpa using hlen) _ (by rw [hb]; simp) r hr
  rw [hb]; simp [List.drop_left']

-- Reads of p ++ more, and of short explicit lists, by a BitVec index.

-- A read of p ++ more, as a read of one or the other.
theorem appRead (p : Array (BitVec 8)) (hs : p.size < 2 ^ 32) (more : List (BitVec 8)) (i : BitVec 32) :
    (p ++ more.toArray)[i.toNat]! =
      if i < BitVec.ofNat 32 p.size then p[i.toNat]! else more[(i - BitVec.ofNat 32 p.size).toNat]! := by
  have key : (p ++ more.toArray)[i.toNat]? =
      if i.toNat < p.size then p[i.toNat]? else more[i.toNat - p.size]? := by
    rw [Array.getElem?_append]; simp
  have hsub : ¬ i.toNat < p.size → (i - BitVec.ofNat 32 p.size).toNat = i.toNat - p.size := by
    intro h; rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs]; omega
  simp only [getElem!_def, key]
  by_cases h : i.toNat < p.size
  · simp only [h, (toNat_lt_size hs i).mp h, ↓reduceIte]
  · have h2 : ¬ i < BitVec.ofNat 32 p.size := fun hh => h ((toNat_lt_size hs i).mpr hh)
    simp only [h, h2, ↓reduceIte, hsub h]

theorem appSize (p : Array (BitVec 8)) (more : List (BitVec 8)) :
    BitVec.ofNat 32 (p ++ more.toArray).size = BitVec.ofNat 32 p.size + BitVec.ofNat 32 more.length := by
  simp [BitVec.ofNat_add]


theorem ite_read (c : Prop) [Decidable c] (l1 l2 : List (BitVec 8)) (j : Nat) :
    (if c then l1 else l2)[j]! = if c then l1[j]! else l2[j]! := by
  split <;> rfl

theorem list_read (a : BitVec 8) (l : List (BitVec 8)) (j : BitVec 32) :
    (a :: l)[j.toNat]! = if j = 0 then a else l[(j - 1).toNat]! := by
  by_cases h : j = 0
  · subst h; rfl
  · have : j.toNat = (j - 1).toNat + 1 := by bv_omega
    simp only [h, ↓reduceIte, this, getElem!_def, List.getElem?_cons_succ]

theorem nil_read (j : BitVec 32) : ([] : List (BitVec 8))[j.toNat]! = 0 := by
  simp [getElem!_def]; rfl

theorem full_rune_stable : Laws.full_rune_stable := by
  intro p pos hs3 hpos
  have hs : p.size < 2 ^ 32 := by omega
  have hpos' : pos ≤ BitVec.ofNat 32 p.size := by
    rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs]; exact hpos
  have hroom : BitVec.ofNat 32 p.size < 0xFFFFFFFD := by
    rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs]; simp; omega
  constructor
  · intro hf more hm
    have hfit : BitVec.ofNat 32 p.size ≤ BitVec.ofNat 32 p.size + BitVec.ofNat 32 more.length := by
      simp only [BitVec.le_def, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    simp only [full_rune, first_eq, lo_eq, hi_eq] at hf
    simp only [decode_rune, decoded_eq, apply_ite Decoded.r, apply_ite Decoded.size, appRead p hs, appSize,
      first_eq, lo_eq, hi_eq]
    simp only [firstSpec, loSpec, hiSpec, rune_error, as, locb, hicb, maskx, mask2, mask3, mask4,
      BitVec.ofNat_eq_ofNat] at hf hfit ⊢
    generalize BitVec.ofNat 32 more.length = M at *
    bv_decide
  · intro h
    apply Classical.byContradiction
    intro hf
    have hw := h (if BitVec.ofNat 32 p.size - pos = 0 then [0x41]
        else if BitVec.ofNat 32 p.size - pos = 1 then [loSpec p[pos.toNat]!, 0x80, 0x80] else [0x80, 0x80])
      (by repeat' split
          all_goals (simp; omega))
    simp only [full_rune, first_eq, lo_eq, hi_eq] at hf
    simp only [decode_rune, decoded_eq, apply_ite Decoded.r, apply_ite Decoded.size, appRead p hs, appSize,
      first_eq, lo_eq, hi_eq, ite_read, list_read, nil_read, apply_ite List.length, List.length_cons,
      List.length_nil] at hw
    simp only [firstSpec, loSpec, hiSpec, rune_error, as, locb, hicb, maskx, mask2, mask3, mask4,
      BitVec.ofNat_eq_ofNat, Nat.reduceAdd, apply_ite (BitVec.ofNat 32)] at hf hw
    clear h
    bv_decide

-- valid


-- Safety obligations

theorem Safety.append_rune : Laws.Safety.append_rune := by
  intro p r _ hpre
  simp only [append_rune.pre, BitVec.ule, decide_eq_true_eq] at hpre
  simp only [append_rune.safe]
  repeat' split
  all_goals (try simp only [Array.size_push, decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true'] at *)
  all_goals (try split)
  all_goals (simp at * <;> omega)

theorem Safety.decode_rune : Laws.Safety.decode_rune := by
  intro p pos hs hpre
  simp only [decode_rune.pre] at hpre
  simp only [decode_rune.safe, first_eq, firstSpec, toNat_lt_size hs, toNat_lt_lit _ 16 (by decide), as, locb, hicb]
  bv_decide

theorem Safety.full_rune : Laws.Safety.full_rune := by
  intro p pos hs hpre
  simp only [full_rune.pre] at hpre
  simp only [full_rune.safe, first_eq, firstSpec, toNat_lt_size hs, toNat_lt_lit _ 16 (by decide), locb, hicb]
  bv_decide

-- The fast path never moves i past the end of p.
theorem loop1_le (p : Array (BitVec 8)) (i : BitVec 32) :
    i ≤ BitVec.ofNat 32 p.size → valid.loop1 p i ≤ BitVec.ofNat 32 p.size := by
  fun_induction valid.loop1 p i
  all_goals intro hi
  all_goals (try (rename_i ih; apply ih))
  all_goals (try simp +zetaDelta only at *)
  all_goals (try simp only [decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_eq_eq_not, Bool.not_true,
    Bool.or_eq_true, beq_iff_eq, Decidable.not_not] at *)
  all_goals bv_decide

theorem loop1_safe (p : Array (BitVec 8)) (hs : p.size < 2 ^ 32) (i : BitVec 32) :
    i ≤ BitVec.ofNat 32 p.size → valid.loop1.safe p i = true := by
  fun_induction valid.loop1.safe p i
  all_goals intro hi
  all_goals (try (rename_i ih; apply ih))
  all_goals (simp +zetaDelta only [toNat_lt_size hs] at *)
  all_goals (try simp only [decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_eq_eq_not, Bool.not_true,
    Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Decidable.not_not] at *)
  all_goals bv_decide

-- The loop function is large, so its induction principle needs room.
set_option maxRecDepth 20000 in
theorem loop2_safe (p : Array (BitVec 8)) (hs : p.size < 2 ^ 32) (i : BitVec 32) :
    i ≤ BitVec.ofNat 32 p.size → valid.loop2.safe p i (BitVec.ofNat 32 p.size) = true := by
  fun_induction valid.loop2.safe p i (BitVec.ofNat 32 p.size)
  all_goals intro hi
  all_goals (try (rename_i ih; apply ih))
  all_goals (simp +zetaDelta only [first_eq, firstSpec, toNat_lt_size hs, toNat_lt_lit _ 16 (by decide),
    rune_self, xx, locb, hicb] at *)
  all_goals (try simp only [decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
    Bool.not_eq_eq_eq_not, Bool.not_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Decidable.not_not] at *)
  all_goals bv_decide

theorem Safety.valid : Laws.Safety.valid := by
  intro p hs
  have h0 : (0 : BitVec 32) ≤ BitVec.ofNat 32 p.size := by bv_decide
  simp only [valid.safe, loop1_safe p hs 0 h0, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  exact loop2_safe p hs _ (loop1_le p 0 h0)

-- valid accepts exactly the well-formed UTF-8

theorem wf_nil : well_formed [] := ⟨[], by simp, rfl⟩

-- A nonempty well-formed sequence starts with the encoding of a scalar
-- value and continues well formed.
theorem wf_cons_iff (l : List (BitVec 8)) (hl : l ≠ []) :
    well_formed l ↔ ∃ r, scalar r ∧ encode r <+: l ∧ well_formed (l.drop (encode r).length) := by
  constructor
  · rintro ⟨rs, hall, heq⟩
    cases rs with
    | nil => simp at heq; exact absurd heq hl
    | cons r rs =>
      refine ⟨r, hall r (by simp), ?_, rs, fun x hx => hall x (by simp [hx]), ?_⟩
      · rw [heq]; simp [List.flatMap_cons]
      · rw [heq]; simp [List.flatMap_cons]
  · rintro ⟨r, hr, ⟨t, ht⟩, rs, hall, heq⟩
    refine ⟨r :: rs, ?_, ?_⟩
    · intro x hx; simp at hx; rcases hx with rfl | hx; exact hr; exact hall x hx
    · rw [← ht] at heq ⊢; simp at heq; simp [List.flatMap_cons, heq]

-- One step of well-formedness, by decode_rune: p from i is well formed
-- exactly when decoding at i does not fail and p is well formed again
-- after the rune it decodes.
theorem wf_step (p : Array (BitVec 8)) (hs : p.size < 2 ^ 32) (i : BitVec 32) (hi : i.toNat < p.size) :
    well_formed (p.toList.drop i.toNat) ↔
      decode_rune p i ≠ { r := 0xFFFD, size := 1 } ∧
      well_formed (p.toList.drop (i.toNat + (decode_rune p i).size.toNat)) := by
  have hne : p.toList.drop i.toNat ≠ [] := by simp; omega
  rw [wf_cons_iff _ hne]
  constructor
  · rintro ⟨r, hr, hpre, hwf⟩
    have hd := decode_of_prefix p hs i (by omega) r hr hpre
    have h4 : (encode r).length ≤ 4 := by rw [encode_bv]; repeat' split
                                          all_goals simp
    rw [hd]
    refine ⟨?_, ?_⟩
    · intro h; simp only [decoded_eq] at h
      rcases h with ⟨rfl, h⟩
      revert h; rw [encode_bv]; decide
    · simp only [List.drop_drop, BitVec.toNat_ofNat] at hwf ⊢
      rw [Nat.mod_eq_of_lt (by omega)]
      first | exact hwf | (rw [Nat.add_comm]; exact hwf)
  · rintro ⟨hne1, hwf⟩
    have := decode_sound p i hs (by omega)
    simp only at this
    rcases this with ⟨h, _⟩ | ⟨_, h⟩ | ⟨hr, hpre, hlen⟩
    · omega
    · exact absurd h hne1
    · refine ⟨_, hr, hpre, ?_⟩
      rw [List.drop_drop, ← hlen]
      first | exact hwf | (rw [Nat.add_comm]; exact hwf)

theorem wf_end (p : Array (BitVec 8)) (hs : p.size < 2 ^ 32) (i : BitVec 32)
    (h : ¬ i < BitVec.ofNat 32 p.size) (hi : i ≤ BitVec.ofNat 32 p.size) : well_formed (p.toList.drop i.toNat) := by
  have : i.toNat = p.size := by
    have := (toNat_eq_size hs i).mpr (by bv_decide); exact this
  simp only [this, List.drop_eq_nil_of_le (by simp : p.toList.length ≤ p.size)]
  exact wf_nil

theorem wf_next (p : Array (BitVec 8)) (hs : p.size < 2 ^ 32) (i i' : BitVec 32)
    (hi : i < BitVec.ofNat 32 p.size) (hd : decode_rune p i ≠ { r := 0xFFFD, size := 1 })
    (hsz : i + (decode_rune p i).size = i') (hge : i ≤ i') (hle : i' ≤ BitVec.ofNat 32 p.size) :
    well_formed (p.toList.drop i.toNat) ↔ well_formed (p.toList.drop i'.toNat) := by
  rw [wf_step p hs i ((toNat_lt_size hs i).mpr hi)]
  have : i.toNat + (decode_rune p i).size.toNat = i'.toNat := by
    subst hsz; rw [BitVec.toNat_add, Nat.mod_eq_of_lt]; bv_omega
  rw [this]; exact ⟨fun h => h.2, fun h => ⟨hd, h⟩⟩

theorem wf_fail (p : Array (BitVec 8)) (hs : p.size < 2 ^ 32) (i : BitVec 32)
    (hi : i < BitVec.ofNat 32 p.size) (hd : decode_rune p i = { r := 0xFFFD, size := 1 }) :
    ¬ well_formed (p.toList.drop i.toNat) := by
  rw [wf_step p hs i ((toNat_lt_size hs i).mpr hi)]
  exact fun h => h.1 hd

theorem iff_step {A B w w' : Prop} (hstep : w ↔ w') (ih : (A ↔ w') ∧ B) : (A ↔ w) ∧ B :=
  ⟨ih.1.trans hstep.symm, ih.2⟩

-- Bytes: unfold the loop's locals and decode_rune, and decide.
macro "bytes" hs:term : tactic => `(tactic| (
  try simp +zetaDelta only [decode_rune, decoded_eq, apply_ite Decoded.r, apply_ite Decoded.size, first_eq, lo_eq, hi_eq,
    ne_eq] at *
  try simp only [firstSpec, loSpec, hiSpec, rune_error, rune_self, as, xx, locb, hicb, maskx, mask2, mask3, mask4,
    toNat_lt_size $hs, toNat_lt_lit _ 16 (by decide), BitVec.ofNat_eq_ofNat, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    Decidable.not_not] at *
  bv_decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem loop2_wf (p : Array (BitVec 8)) (hs : p.size < 2 ^ 32) (i : BitVec 32) :
    i ≤ BitVec.ofNat 32 p.size →
      (((valid.loop2 p i (BitVec.ofNat 32 p.size)).1 = none ↔ well_formed (p.toList.drop i.toNat)) ∧
        (valid.loop2 p i (BitVec.ofNat 32 p.size)).1 ≠ some true) := by
  fun_induction valid.loop2 p i (BitVec.ofNat 32 p.size)
  all_goals intro hi
  all_goals (try simp only [reduceCtorEq, iff_true, true_iff, false_iff, iff_false, ne_eq, not_false_eq_true,
    and_true, Option.some.injEq, Bool.false_eq_true])
  all_goals first
    | (rename_i ih
       refine iff_step (wf_next p hs _ _ ?_ ?_ ?_ ?_ ?_) (ih ?_)
       all_goals (clear ih; bytes hs))
    | (refine wf_fail p hs _ ?_ ?_
       all_goals bytes hs)
    | (refine (wf_next p hs _ (_ + (decode_rune p _).size) ?_ ?_ rfl ?_ ?_).mpr (wf_end p hs _ ?_ ?_)
       all_goals bytes hs)
    | (refine wf_end p hs _ ?_ hi
       bytes hs)
    | (exfalso; bytes hs)

-- An ASCII byte is a rune of its own.
theorem wf_ascii (p : Array (BitVec 8)) (hs : p.size < 2 ^ 32) (i : BitVec 32)
    (hi : i < BitVec.ofNat 32 p.size) (hb : p[i.toNat]! < 0x80) :
    well_formed (p.toList.drop i.toNat) ↔ well_formed (p.toList.drop (i + 1).toNat) :=
  wf_next p hs i (i + 1) hi (by bytes hs) (by bytes hs) (by bytes hs) (by bytes hs)

-- The fast path's step: eight ASCII bytes.
theorem wf_ascii8 (p : Array (BitVec 8)) (hs : p.size < 2 ^ 32) (i : BitVec 32)
    (hi : i ≤ BitVec.ofNat 32 p.size) (h8 : 8 ≤ BitVec.ofNat 32 p.size - i)
    (hb : p[i.toNat]! < 0x80 ∧ p[(i + 1).toNat]! < 0x80 ∧ p[(i + 2).toNat]! < 0x80 ∧ p[(i + 3).toNat]! < 0x80 ∧
      p[(i + 4).toNat]! < 0x80 ∧ p[(i + 5).toNat]! < 0x80 ∧ p[(i + 6).toNat]! < 0x80 ∧ p[(i + 7).toNat]! < 0x80) :
    well_formed (p.toList.drop i.toNat) ↔ well_formed (p.toList.drop (i + 8).toNat) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hb
  -- One byte at a time, renaming i + k + 1 to i + (k + 1) after each.
  have step : ∀ k k' : BitVec 32, k' = k + 1 → k < 8 → p[(i + k).toNat]! < 0x80 →
      (well_formed (p.toList.drop (i + k).toNat) ↔ well_formed (p.toList.drop (i + k').toNat)) := by
    intro k k' hk' hk hb
    rw [show i + k' = i + k + 1 by bv_omega]
    exact wf_ascii p hs (i + k) (by bv_omega) hb
  have z : i + 0 = i := by bv_omega
  have e0 : well_formed (p.toList.drop i.toNat) ↔ well_formed (p.toList.drop (i + 0).toNat) := by rw [z]
  exact e0.trans <| (step 0 1 rfl (by decide) (by rw [z]; exact h0)).trans <| (step 1 2 rfl (by decide) h1).trans <|
    (step 2 3 rfl (by decide) h2).trans <| (step 3 4 rfl (by decide) h3).trans <|
    (step 4 5 rfl (by decide) h4).trans <| (step 5 6 rfl (by decide) h5).trans <|
    (step 6 7 rfl (by decide) h6).trans <| (step 7 8 rfl (by decide) h7)

theorem loop1_wf (p : Array (BitVec 8)) (hs : p.size < 2 ^ 32) (i : BitVec 32) :
    i ≤ BitVec.ofNat 32 p.size →
      (well_formed (p.toList.drop i.toNat) ↔ well_formed (p.toList.drop (valid.loop1 p i).toNat)) := by
  fun_induction valid.loop1 p i
  all_goals intro hi
  all_goals first
    | exact Iff.rfl
    | (rename_i ih
       refine (wf_ascii8 p hs _ hi ?_ ?_).trans (ih ?_)
       all_goals (clear ih; bytes hs))
    | (refine wf_ascii8 p hs _ hi ?_ ?_
       all_goals bytes hs)
    | (exfalso; bytes hs)

theorem valid_well_formed : Laws.valid_well_formed := by
  intro p hs
  have h0 : (0 : BitVec 32) ≤ BitVec.ofNat 32 p.size := by bv_decide
  have h1 := loop1_wf p hs 0 h0
  have h2 := loop2_wf p hs _ (loop1_le p 0 h0)
  rw [show (0 : BitVec 32).toNat = 0 from rfl, List.drop_zero] at h1
  simp only [valid]
  generalize (valid.loop2 p (valid.loop1 p 0) (BitVec.ofNat 32 p.size)).fst = res at h2
  cases res with
  | none => simp only [true_iff] at h2 ⊢; exact h1.mpr h2.1
  | some b =>
    cases b
    · simp only [reduceCtorEq, false_iff, Bool.false_eq_true] at h2 ⊢; exact fun h => h2.1 (h1.mp h)
    · simp at h2

-- The translation: each C++ function, run by the semantics in
-- Claws.Sem, returns what Code.lean computes. Callees first, and each
-- loop before its function.

claws_valid rune_start [Code.rune_start]
claws_valid valid_rune [Code.valid_rune]
claws_valid rune_len [Code.rune_len]
claws_valid full_rune [Code.full_rune]
claws_valid append_rune [Code.append_rune]
-- decode_rune computes a rune from up to four bytes on each of twelve
-- paths: its proof needs more than the default time.
set_option maxHeartbeats 1000000 in
claws_valid decode_rune [Code.decode_rune]
claws_loop valid 1 []
-- The second loop of valid has seventeen paths through its body: its
-- proof needs more than the default time.
set_option maxHeartbeats 1000000 in
claws_loop valid 2 []
claws_valid valid [Code.valid]

end Utf8.Proof
