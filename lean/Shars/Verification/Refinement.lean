import Aeneas
import Shars.Definitions.Algos
import Sha3.Spec
import Shars.Verification.Utils.List


/- def Aeneas.Std.Array.toBitVec{size: Std.Usize}(self: Std.Array Bool size): BitVec (size.val) := -/
/-   (BitVec.ofBoolListLE <| self.val).cast (by simp) -/
/- def Aeneas.Std.Slice.toBitVec(self: Aeneas.Std.Slice Bool): BitVec self.length := -/
/-   (BitVec.ofBoolListLE self.val).cast (by simp) -/

def Aeneas.Std.UScalar.toBits(u: Aeneas.Std.UScalar ty): List Bool := List.ofFn (u.bv[·])
@[simp] theorem Aeneas.Std.UScalar.length_toBits(u: Aeneas.Std.UScalar ty): u.toBits.length = ty.numBits := by
  simp only [toBits, Fin.getElem_fin, List.length_ofFn]


-- TODO: Consider eliminating, we want `toBits` to be the final opaque
/- @[simp] -- -/ 
theorem Aeneas.Std.UScalar.getElem!_toBits(u: Aeneas.Std.UScalar ty)(i: Nat): u.toBits[i]! = u.bv[i]! := by
  by_cases i_idx: i < ty.numBits; case neg => simp [getElem!_neg, i_idx]
  simp only [toBits, List.getElem!_ofFn, i_idx, getElem!_pos, Fin.getElem_fin]

def List.toBits(ls: List (Aeneas.Std.UScalar ty)): List Bool := ls.map (·.toBits) |>.flatten

@[scalar_tac_simps]
theorem List.length_toBits(ls: List (Aeneas.Std.UScalar ty))
: ls.toBits.length = ls.length * ty.numBits
:= by
  rw [toBits]
  have: ∀ xs ∈ (ls.map (·.toBits)), xs.length = ty.numBits := by simp
  rw [List.length_flatten_of_uniform this]
  simp [toBits, Nat.mul_comm]

theorem List.getElem!_toBits(ls: List (Aeneas.Std.UScalar ty))(i: Nat)
: ls.toBits[i]! = ls[i / ty.numBits]!.toBits[i % ty.numBits]!
:= by
  simp only [toBits]
  have uniform : ls.map (·.toBits) |>.uniform ty.numBits := by
    intro x x_in; simp at x_in
    obtain ⟨a, a_in, a_x⟩ := x_in
    simp [←a_x]
  have numBits_pos: ty.numBits > 0 := by cases ty <;> simp

  by_cases i_idx: i < ls.toBits.length; case neg => 
    rw [getElem!_neg]; case h => simpa only [toBits]
    rw [List.length_toBits] at i_idx
    simp at i_idx
    have: ls.length ≤ i / ty.numBits := by 
      exact Nat.le_div_iff_mul_le numBits_pos |>.mpr i_idx
    conv => rhs; arg 1; rw [getElem!_neg (h := by simpa using this)]
    cases ty <;> simp [-getElem!_eq_getElem?_getD, default, Aeneas.Std.UScalar.getElem!_toBits]
  have: i / ty.numBits < ls.length := by
    rw [List.length_toBits, Nat.mul_comm] at i_idx
    exact Nat.div_lt_of_lt_mul i_idx

  rw [List.getElem!_flatten_of_uniform uniform]
  simp [-getElem!_eq_getElem?_getD, *]

@[simp, scalar_tac_simps]
abbrev Aeneas.Std.Array.toBits(arr: Aeneas.Std.Array (Aeneas.Std.UScalar ty) n): List Bool := arr.val.toBits
@[simp] def Aeneas.Std.Array.length_toBits(arr: Aeneas.Std.Array (Aeneas.Std.UScalar ty) n)
: arr.toBits.length = n * ty.numBits
:= by simp only [toBits, List.length_toBits, arr.property]

@[simp, scalar_tac_simps]
abbrev Aeneas.Std.Slice.toBits(arr: Aeneas.Std.Slice (Aeneas.Std.UScalar ty)): List Bool := arr.val.toBits
@[simp] def Aeneas.Std.Slice.length_toBits(arr: Aeneas.Std.Slice (Aeneas.Std.UScalar ty))
: arr.toBits.length = arr.length * ty.numBits
:= by simp only [toBits, List.length_toBits]

def List.toStateArray(self: List Bool): Spec.Keccak.StateArray 6 := 
    if len_self: self.length = Spec.b 6 then
      ⟨⟨self⟩, by simp +decide [len_self]⟩
    else default

-- NOTE: We make `toStateArray` fallible so that we're able to compose it with `toBits`.

@[reducible, simp]
def algos.StateArray.toSpec(self: algos.StateArray): Spec.Keccak.StateArray 6 := self.toBits.toStateArray

abbrev Spec.Keccak.StateArray.toBits(state: Spec.Keccak.StateArray 6): List Bool := state.toVector.toArray.toList

@[simp] theorem Spec.Keccak.StateArray.toStateArray_toBits(state: Spec.Keccak.StateArray 6)
: state.toBits.toStateArray = state
:= by simp [toBits, List.toStateArray]

@[simp] theorem Spec.Keccak.StateArray.toBits_toStateArray(state: List Bool)(len_state: state.length = Spec.b 6)
: state.toStateArray.toBits = state
:= by simp [toBits, List.toStateArray, len_state]

theorem Spec.Keccak.StateArray.LeftInverse_toBits
: Function.LeftInverse List.toStateArray Spec.Keccak.StateArray.toBits
:= by intro st; apply Spec.Keccak.StateArray.toStateArray_toBits st


/- theorem List.toBits_toStateArray(state: List Bool) -/
/-   (len_state: state.length = 1600) -/
/- : state.toStateArray.toBits = state -/
/- := by simp +decide [*, cond, toStateArray, Spec.Keccak.StateArray.toBits, toStateArrayCore, Spec.Keccak.StateArray.toBitsSubtype] -/

/- abbrev Aeneas.Std.Array.toArray{size: Usize}(self: Aeneas.Std.Array α size): _root_.Array α := Array.mk self.val -/
/- abbrev Aeneas.Std.Slice.toArray(self: Aeneas.Std.Slice α): _root_.Array α := Array.mk self.val -/
