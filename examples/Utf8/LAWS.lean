-- The laws of the Utf8 example, a port of Go's unicode/utf8. A human
-- writes this file and the AI must not edit it. Each law is a `def` of
-- type `Prop`, and PROOF.lean proves it with a theorem of the same name.
-- Code.lean adds a safety obligation, in Utf8.Laws.Safety, for each
-- function that indexes, pushes, or runs a while loop.
--
-- The laws compare the port with UTF-8 as the Unicode Standard defines
-- it (chapter 3: D92 and Table 3-6), written here independently of the
-- code: with arithmetic on natural numbers instead of shifts and masks,
-- and with no lookup tables.
--
-- A claws::vec never holds 2^32 elements, so laws about one assume
-- `p.size < 2 ^ 32`.
import Utf8.Code

namespace Utf8.Laws

open Utf8.Code

-- A Unicode scalar value: any code point except a surrogate.
def scalar (r : BitVec 32) : Prop :=
  r.toNat < 0xD800 ∨ (0xDFFF < r.toNat ∧ r.toNat ≤ 0x10FFFF)

-- The UTF-8 encoding of a scalar value (Table 3-6).
def encode (r : BitVec 32) : List (BitVec 8) :=
  let n := r.toNat
  if n < 0x80 then
    [BitVec.ofNat 8 n]
  else if n < 0x800 then
    [BitVec.ofNat 8 (0xC0 + n / 0x40), BitVec.ofNat 8 (0x80 + n % 0x40)]
  else if n < 0x10000 then
    [BitVec.ofNat 8 (0xE0 + n / 0x1000), BitVec.ofNat 8 (0x80 + n / 0x40 % 0x40),
     BitVec.ofNat 8 (0x80 + n % 0x40)]
  else
    [BitVec.ofNat 8 (0xF0 + n / 0x40000), BitVec.ofNat 8 (0x80 + n / 0x1000 % 0x40),
     BitVec.ofNat 8 (0x80 + n / 0x40 % 0x40), BitVec.ofNat 8 (0x80 + n % 0x40)]

-- Well-formed UTF-8 (D92): the encodings of some scalar values, one after
-- another.
def well_formed (bytes : List (BitVec 8)) : Prop :=
  ∃ rs : List (BitVec 32), (∀ r ∈ rs, scalar r) ∧ bytes = rs.flatMap encode

-- LAW: valid_rune accepts exactly the scalar values.
def valid_rune_scalar : Prop :=
  ∀ r : BitVec 32, valid_rune r = true ↔ scalar r

-- LAW: rune_len is the length of the encoding, or Go's -1 (as a uint32_t)
-- for a value that is not a scalar value.
def rune_len_encode : Prop :=
  ∀ r : BitVec 32,
    (scalar r → rune_len r = BitVec.ofNat 32 (encode r).length) ∧
    (¬ scalar r → rune_len r = 0xFFFFFFFF)

-- LAW: append_rune appends the encoding of r, or of U+FFFD (the
-- replacement character) when r is not a scalar value.
def append_encodes : Prop :=
  ∀ (p : Array (BitVec 8)) (r : BitVec 32), p.size ≤ 0xFFFFFFFA →
    (scalar r → (append_rune p r).toList = p.toList ++ encode r) ∧
    (¬ scalar r → (append_rune p r).toList = p.toList ++ encode 0xFFFD)

-- LAW: the encoding of a scalar value decodes to that value and its
-- length, whatever bytes come before and after it.
def decode_encoded : Prop :=
  ∀ (before after : List (BitVec 8)) (r : BitVec 32), scalar r →
    (before ++ encode r ++ after).length < 2 ^ 32 →
    decode_rune (before ++ encode r ++ after).toArray (BitVec.ofNat 32 before.length) =
      { r := r, size := BitVec.ofNat 32 (encode r).length }

-- LAW: decoding never invents a rune. At the end of p it gives U+FFFD and
-- size 0. Otherwise either it gives U+FFFD and size 1, or the bytes at pos
-- begin with the encoding of the scalar value it gives, and size is that
-- encoding's length. So no overlong encoding, no surrogate, and nothing
-- past U+10FFFF ever decodes.
def decode_sound : Prop :=
  ∀ (p : Array (BitVec 8)) (pos : BitVec 32), p.size < 2 ^ 32 → pos.toNat ≤ p.size →
    let d := decode_rune p pos
    (pos.toNat = p.size ∧ d = { r := 0xFFFD, size := 0 }) ∨
    (pos.toNat < p.size ∧ d = { r := 0xFFFD, size := 1 }) ∨
    (scalar d.r ∧ encode d.r <+: p.toList.drop pos.toNat ∧ d.size.toNat = (encode d.r).length)

-- LAW: full_rune holds exactly when no bytes added to the end of p could
-- change what decodes at pos. The law needs room in a vec for the
-- longest completion of a rune, 3 bytes: when p is too full to grow, no
-- addition is possible, and so none could change anything.
def full_rune_stable : Prop :=
  ∀ (p : Array (BitVec 8)) (pos : BitVec 32), p.size + 3 < 2 ^ 32 → pos.toNat ≤ p.size →
    (full_rune p pos = true ↔
      ∀ more : List (BitVec 8), p.size + more.length < 2 ^ 32 →
        decode_rune (p ++ more.toArray) pos = decode_rune p pos)

-- LAW: valid accepts exactly the well-formed UTF-8, including through its
-- fast path that checks 8 bytes at a time.
def valid_well_formed : Prop :=
  ∀ p : Array (BitVec 8), p.size < 2 ^ 32 → (valid p = true ↔ well_formed p.toList)

end Utf8.Laws
