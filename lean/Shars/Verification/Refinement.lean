import Aeneas
import Shars.Definitions.Algos
import Sha3.Spec
import Shars.Verification.Utils.List
import Shars.Verification.Utils.UScalar
import Shars.Verification.Utils.Nat


def Aeneas.Std.UScalar.toBits(u: Aeneas.Std.UScalar ty): List Bool := List.ofFn (u.bv[·])

@[simp, scalar_tac_simps] theorem Aeneas.Std.UScalar.length_toBits(u: Aeneas.Std.UScalar ty): u.toBits.length = ty.numBits := by
  simp only [toBits, Fin.getElem_fin, List.length_ofFn]
theorem Aeneas.Std.UScalar.getElem!_toBits(u: Aeneas.Std.UScalar ty)(i: Nat): u.toBits[i]! = u.bv[i]! := by
  by_cases i_idx: i < ty.numBits; case neg => simp [getElem!_neg, i_idx]
  simp only [toBits, List.getElem!_ofFn, i_idx, getElem!_pos, Fin.getElem_fin]

def List.toBits(ls: List (Aeneas.Std.UScalar ty)): List Bool := ls.map (·.toBits) |>.flatten

@[scalar_tac_simps]
theorem List.length_toBits(ls: List (Aeneas.Std.UScalar ty))
: ls.toBits.length = ls.length * ty.numBits
:= by rw [toBits, List.length_flatten_of_uniform (n := ty.numBits) (by simp)]
      simp [Nat.mul_comm]

theorem List.getElem!_toBits(ls: List (Aeneas.Std.UScalar ty))(i: Nat)
: ls.toBits[i]! = ls[i / ty.numBits]!.toBits[i % ty.numBits]!
:= by
  simp only [toBits]
  have uniform : ls.map (·.toBits) |>.uniform ty.numBits := by
    intro x x_in; simp at x_in
    obtain ⟨a, a_in, a_x⟩ := x_in
    simp [←a_x]

  by_cases i_idx: i < ls.toBits.length; case neg =>
    rw [getElem!_neg]; case h => simpa only [toBits]
    rw [List.length_toBits] at i_idx
    simp at i_idx
    have: ls.length ≤ i / ty.numBits := by
      exact Nat.le_div_iff_mul_le (by simp) |>.mpr i_idx
    conv => rhs; arg 1; rw [getElem!_neg (h := by simpa using this)]
    cases ty <;> simp [-getElem!_eq_getElem?_getD, default, Aeneas.Std.UScalar.getElem!_toBits]
  have: i / ty.numBits < ls.length := by
    rw [List.length_toBits, Nat.mul_comm] at i_idx
    exact Nat.div_lt_of_lt_mul i_idx

  rw [List.getElem!_flatten_of_uniform uniform]
  simp [-getElem!_eq_getElem?_getD, *]

@[simp, scalar_tac_simps]
abbrev Aeneas.Std.Array.toBits(arr: Array (UScalar ty) n): List Bool := arr.val.toBits
@[simp] def Aeneas.Std.Array.length_toBits(arr: Array (UScalar ty) n)
: arr.toBits.length = n * ty.numBits
:= by simp only [toBits, List.length_toBits, arr.property]

@[simp, scalar_tac_simps]
abbrev Aeneas.Std.Slice.toBits(arr: Slice (UScalar ty)): List Bool := arr.val.toBits
@[simp] def Aeneas.Std.Slice.length_toBits(arr: Slice (UScalar ty))
: arr.toBits.length = arr.length * ty.numBits
:= by simp only [toBits, List.length_toBits]

-- NOTE: We make `toStateArray` fallible so that we're able to compose it with `toBits`.
def List.toStateArray(self: List Bool): Spec.Keccak.StateArray 6 :=
    if len_self: self.length = Spec.b 6 then
      ⟨⟨self⟩, by simp +decide [len_self]⟩
    else default

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

-------------------

attribute [-simp] List.getElem!_eq_getElem?_getD List.ofFn_succ

open Aeneas
@[simp] theorem List.toBits_take(ls: List (Std.UScalar ty))(n: Nat)
: (ls.take n).toBits = ls.toBits.take (n* ty.numBits)
:= by
  apply List.ext_getElem <;> simp [List.length_toBits, ←getElem!_pos]
  intro i i_idx
  have := Nat.div_lt_of_lt_mul (Nat.mul_comm _ _ ▸ i_idx)
  by_cases cond: n ≤ ls.length
  case pos =>
    simp [cond] at i_idx
    simp [List.getElem!_toBits]
    simp_lists
    simp [List.getElem!_toBits]
  case neg =>
    simp at cond
    simp [cond, le_of_lt] at i_idx
    simp [List.getElem!_toBits]
    simp_lists
    rw [List.take_of_length_le, List.getElem!_toBits]
    have := Nat.mul_lt_mul_left (by cases ty <;> simp : 0 < ty.numBits) |>.mpr cond
    simp [List.length_toBits, ←Nat.mul_comm ty.numBits, this, le_of_lt]

@[simp] theorem List.toBits_drop(ls: List (Std.UScalar ty))(n: Nat)
: (ls.drop n).toBits = ls.toBits.drop (n* ty.numBits)
:= by
  apply List.ext_getElem
  · simp [List.length_toBits, Nat.sub_mul]
  simp [List.length_toBits, Nat.sub_mul, ←getElem!_pos]
  intro i i_idx
  simp [List.getElem!_toBits, Nat.mul_comm n, Nat.mul_add_div]

-- TODO: Move to `Refinement.lean`
@[simp] theorem List.toBits_append(ls1 ls2: List (Std.UScalar ty))
: (ls1 ++ ls2).toBits = ls1.toBits ++ ls2.toBits
:= by simp [List.toBits]

-- TODO: Move to `Refinement.lean`
@[simp] theorem List.toBits_setSlice!(ls s: List (Std.UScalar ty))(off: Nat)
: (ls.setSlice! off s).toBits = ls.toBits.setSlice! (ty.numBits*off) s.toBits
:= by simp only [List.setSlice!, List.toBits_drop, List.toBits_take, List.toBits_append,
   ←Nat.mul_comm ty.numBits, List.length_toBits, Nat.mul_min_mul_left, ←Nat.mul_sub, ←Nat.mul_add]

@[simp] theorem List.toBits_getElem(ls: List (Std.UScalar ty))(i: Nat)
  (i_idx: i < ls.length)
: ls[i].toBits = ls.toBits.slice (ty.numBits*i) (ty.numBits*(i+1))
:= by
  have: (ls.toBits.slice (ty.numBits*i) (ty.numBits*(i+1))).length = ls[i].toBits.length := by
    simp [List.slice, List.length_toBits, ←Nat.mul_comm ty.numBits, ←Nat.mul_sub]
    omega
  apply List.ext_getElem <;> simp only [↓this, ←getElem!_pos]
  simp
  intro j j_idx
  simp [List.slice, j_idx, List.getElem!_toBits, Nat.mod_eq_of_lt, Nat.add_comm, Nat.add_mul_div_left, Nat.div_eq_of_lt]

@[simp] theorem List.toBits_getElem!(ls: List (Std.UScalar ty))(i: Nat)
  (i_idx: i < ls.length)
: ls[i]!.toBits = ls.toBits.slice (ty.numBits*i) (ty.numBits*(i+1))
:= by simp [getElem!_pos, i_idx]


theorem List.toBits_set(ls: List (Std.UScalar ty))(u: Std.UScalar ty)(i: Nat)
: (ls.set i u).toBits = ls.toBits.setSlice! (i * ty.numBits) u.toBits
:= by
  apply List.ext_getElem
  · simp [List.length_toBits]
  intro j j_idx j_idx2
  simp [←getElem!_pos]
  simp [List.length_setSlice!, List.length_toBits] at j_idx j_idx2
  simp [List.getElem!_toBits]
  have numBits_pos: ty.numBits > 0 := by cases ty <;> simp
  have j_block_idx: j / ty.numBits < ls.length := by
    apply Nat.lt_of_mul_lt_mul_left (a := ty.numBits)
    calc _ ≤ j := by apply Nat.mul_div_le
         j < _ := Nat.mul_comm _ _ ▸ j_idx
  if cond: i = j / ty.numBits then
    subst cond
    simp [List.getElem!_set, j_block_idx]
    rw [List.getElem!_setSlice!_middle]
    all_goals simp [Nat.mul_comm _ ty.numBits, ←Nat.mod_eq_sub]
    simp [Nat.mul_div_le, Nat.mod_lt, numBits_pos, List.length_toBits, j_idx]
  else
    have := Nat.div_spec j i numBits_pos |>.not.mp cond
    simp [Nat.mul_add, -not_and, not_and_or] at this
    simp [List.getElem!_set_ne, cond, ←List.getElem!_toBits]
    rw [List.getElem!_setSlice!_same]
    simp
    rw [Nat.mul_comm] at this
    assumption
