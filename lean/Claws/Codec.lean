import Claws.Interp
import Claws.SimpAttr

/-!
# Reading values back

claws-ast writes, for each struct and enum, an encoding `S.toVal` of
`Code.S` as a `Claws.Sem.Val` and a decoding `S.ofVal` back. These are
the decodings of the scalar fields they are built from. They are proof
aids, not part of the trusted base: a validation law states its claim
with the encodings alone.
-/

namespace Claws.Sem

def Val.asUint : Val → BitVec 32
  | .uint v => v
  | _ => 0

def Val.asUchar : Val → BitVec 8
  | .uchar v => v
  | _ => 0

def Val.asBool : Val → Bool
  | .bool b => b
  | _ => false

/-- A `claws::vec` of a Lean array, from its elements' encoding `f`. -/
def Val.ofArray {α : Type} (f : α → Val) (a : Array α) : Val := .vec (a.toList.map f)

/-- A Lean array of a `claws::vec`, from its elements' decoding `g`. -/
def Val.asArray {α : Type} (g : Val → α) : Val → Array α
  | .vec xs => (xs.map g).toArray
  | _ => #[]

/-- A `claws::list` of a Lean list, from its elements' encoding `f`. -/
def Val.ofList {α : Type} (f : α → Val) (l : List α) : Val := .list (l.map f)

/-- A Lean list of a `claws::list`, from its elements' decoding `g`. -/
def Val.asList {α : Type} (g : Val → α) : Val → List α
  | .list xs => xs.map g
  | _ => []

/-! A run takes a list apart by its constructor, so it states each list
by its elements, `.list (l.map f)`; an induction hypothesis about a call
is stated the same way (`claws_ih`). -/

@[claws_interp] theorem Val.ofList_def {α : Type} (f : α → Val) (l : List α) :
    Val.ofList f l = .list (l.map f) := rfl

attribute [claws_interp] List.map_cons List.map_nil

@[claws_codec] theorem Val.asUint_uint (v : BitVec 32) : (Val.uint v).asUint = v := rfl
@[claws_codec] theorem Val.asUchar_uchar (v : BitVec 8) : (Val.uchar v).asUchar = v := rfl
@[claws_codec] theorem Val.asBool_bool (b : Bool) : (Val.bool b).asBool = b := rfl

/-- Decoding a vec decodes each element; the element lemmas then leave
`fun x => x`, which `Array.map_id'` removes. (A version with the
hypothesis `∀ x, g (f x) = x` is one simp cannot discharge.) -/
@[claws_codec] theorem Val.asArray_ofArray {α : Type} (f : α → Val) (g : Val → α) (a : Array α) :
    Val.asArray g (Val.ofArray f a) = a.map (fun x => g (f x)) := by
  cases a; simp [ofArray, asArray, List.map_map, Function.comp_def]

@[claws_codec] theorem Val.asList_ofList {α : Type} (f : α → Val) (g : Val → α) (l : List α) :
    Val.asList g (Val.ofList f l) = l.map (fun x => g (f x)) := by
  simp [ofList, asList, List.map_map, Function.comp_def]

/-- Decoding a list the run states by its elements, `.list (l.map f)`:
`List.map_map` and `Function.comp_def` then leave each element decoded
from its encoding. -/
@[claws_codec] theorem Val.asList_list {α : Type} (g : Val → α) (xs : List Val) :
    Val.asList g (.list xs) = xs.map g := rfl

attribute [claws_codec] Array.map_id' List.map_id' List.map_map Function.comp_def

/- The run reads a list argument back as `Code.f` takes it, as it does a
struct's (`S.ofVal_toVal`). -/
attribute [claws_interp] Val.asList_list Val.asList_ofList List.map_map Function.comp_def List.map_id'
  Val.asUint_uint Val.asUchar_uchar Val.asBool_bool

end Claws.Sem
