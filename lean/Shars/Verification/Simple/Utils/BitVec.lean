import Mathlib
import Shars.Verification.Simple.Utils.SimpLikeTactics
import Shars.Verification.Simple.Utils.Notation
import Shars.Verification.Simple.Utils.List
import Shars.Verification.Simple.Refinement
import Shars.BitVec
import Sha3.Spec

attribute [-simp] List.getElem!_eq_getElem?_getD

@[simp]
theorem BitVec.toList_append(bv: BitVec n)(bv2: BitVec m)
: (bv2 ++ bv).toList = bv.toList ++ bv2.toList
:= by
  simp [toList, BitVec.getElem_append]
  apply List.ext_getElem!
  · simp +arith
  intro i
  simp_lists
  by_cases h: i < n
  case pos =>
    simp [h, ‹i < m + n›']
  case neg =>
    simp [h]
    split
    case isTrue h => simp [‹i - n < m›']
    case isFalse h => simp [‹¬ i - n < m›']

@[simp]
theorem BitVec.toList_toArray(bv: BitVec n)
: bv.toArray.toList = bv.toList
:= by simp [toArray, toList, Array.finRange, List.finRange]

@[simp]
theorem BitVec.toArray_append(bv: BitVec n)(bv2: BitVec m)
: (bv2 ++ bv).toArray = bv.toArray ++ bv2.toArray
:= by
  apply Array.toList_inj.mp
  simp [BitVec.toList_append]

@[simp]
theorem BitVec.size_toArray(bv: BitVec n)
: bv.toArray.size = n
:= by simp [toArray, Array.finRange]

@[simp]
theorem BitVec.getElem!_toList(bv: BitVec n)(i: Nat)
: bv.toList[i]! = bv[i]!
:= by
  simp [toList]
  by_cases i < n
  case neg h =>
    rw [getElem!_neg]
    case h => simpa using h
    rw [getElem!_neg]
    case h => simpa using h
  simp [List.getElem!_map, *, getElem_eq_getElem!]

@[simp]
theorem BitVec.getElem!_toArray(bv: BitVec n)(i: Nat)
: bv.toArray[i]! = bv[i]!
:= by
  have: bv.toArray[i]! = bv.toList[i]! := by
    simp [toList, toArray]
    by_cases i_idx: i < n
    case neg =>
      rw [getElem!_neg]
      case h => simpa [Array.finRange] using i_idx
      rw [getElem!_neg]
      case h => simpa [Array.finRange] using i_idx
    rw [getElem!_pos (h := by simpa [Array.finRange] using i_idx)]
    rw [getElem!_pos (h := by simpa using i_idx)]
    simp [Array.finRange]
  rw [this]
  apply getElem!_toList

@[simp]
theorem BitVec.toList_cast(bv: BitVec n)(h: n = m)
: (bv.cast h).toList = bv.toList
:= by subst h; simp [toList]

theorem BitVec.toBitVec_toList(bv: BitVec n)
: bv.toList.toBitVec = bv.cast (by simp)
:= by
  ext i i_idx
  simp [BitVec.toList]


theorem BitVec.toList_inj{bv bv2: BitVec n}
: bv.toList = bv2.toList → bv = bv2
:= by
  intro cond
  ext i i_idx
  replace cond := List.getElem_of_eq cond (by simp; exact i_idx)
  simpa [←getElem!_pos, getElem!_toList] using cond

theorem BitVec.getLsbD_eq_getElem! {x : BitVec w} {i : Nat} :
    x.getLsbD i = x[i]! := by
  if h: i < w then
    simp only [getElem!_pos, h]
    rfl
  else
    rw [getElem!_neg]
    case h => assumption
    simp [default, BitVec.getLsbD, Nat.testBit]
    have: x.toNat >>> i = 0 := by
      apply Nat.shiftRight_eq_zero
      calc
        _ < 2^w := by exact x.toFin.isLt
        _ ≤ 2^i := by
          apply Nat.pow_le_pow_of_le Nat.one_lt_two
          simpa using h
    rw [this]

attribute [local simp] BitVec.getLsbD_eq_getElem! in
theorem BitVec.toList_setWidth(bv: BitVec n)(m: Nat)
: (bv.setWidth m).toList = bv.toList.setWidth m
:= by
  apply List.ext_getElem!
  · simp
  intro i
  simp
  assume i < m
  case otherwise h => simp [getElem!_neg, h]
  simp [getElem!_pos, *]
