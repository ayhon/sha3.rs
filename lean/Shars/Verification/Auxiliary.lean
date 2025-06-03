import Aeneas
import Shars.BitVec
import Shars.Definitions.Algos
import Sha3.Spec
/- import Sha3.Utils -/
import Aeneas.SimpLists.Init
import Sha3.Facts
import Init.Data.Vector.Lemmas
import Init.Data.Nat.Basic
import Shars.Verification.Utils
import Shars.Verification.Refinement

set_option maxHeartbeats 1000000
attribute [-simp] List.getElem!_eq_getElem?_getD
attribute [simp] Aeneas.Std.Slice.set

open Aeneas hiding Std.Array
open Std.alloc.vec

-- TODO: derive automatically with `progress_pure_def` applied to `Std.core.cmp.impls.OrdUsize.min`
open Aeneas hiding Std.Array in
@[progress]
theorem Std.core.cmp.impls.OrdUsize.min_spec (x y : Std.Usize) :
  ∃ z, Std.toResult (Std.core.cmp.impls.OrdUsize.min x y) = .ok z ∧ z = Std.core.cmp.impls.OrdUsize.min x y := by
  simp [Std.core.cmp.impls.OrdUsize.min, Std.toResult]

theorem U64.numBits_eq_w
: Std.UScalarTy.U64.numBits = Spec.w 6
:= by simp +decide

attribute [local simp] Std.Array.length
attribute [-simp] List.ofFn_succ in
@[progress]
theorem algos.IndexalgosStateArrayPairUsizeUsizeU64.index.spec(input: algos.StateArray)(x y: Std.Usize)
: 5 * y.val + x.val < 25
→ ∃ output,
  index input (x,y) = .ok output ∧
  output = input.val[5 * y.val + x.val]!
:= by
  intro no_overflow
  rw [index]
  progress*
  simp [*]

@[progress]
theorem algos.IndexMutalgosStateArrayPairUsizeUsizeU64.index_mut.spec(input: algos.StateArray)(x y: Std.Usize)
: 5 * y.val + x.val < 25
→ ∃ old mk,
  index_mut input (x,y) = .ok (old, mk) ∧
  old = input.val[5 * y.val + x.val]! ∧
  ∀ u, (mk u).val = input.val.set (5 * y.val + x.val) u
:= by
  intros
  rw [index_mut]
  /- progress* -/ -- TODO: Why does using `progress*` cause an index OOB error?
  let* ⟨ i, i_post ⟩ ← Std.Usize.mul_spec
  let* ⟨ i1, i1_post ⟩ ← Std.Usize.add_spec
  let* ⟨ __discr, __discr_post ⟩ ← Std.Array.index_mut_usize_spec
  simp [*]

theorem BitVec.getElem!_rotateLeft(bv: BitVec n)(w: Nat)(i: Nat)
  (i_idx: i < n)
: (bv.rotateLeft w)[i]! = bv[(i + n - w % n) % n]!
:= by
  by_cases n_pos: n > 0; case neg => simp at n_pos; simp [n_pos] at i_idx
  simp [getElem!_pos, i_idx, Nat.mod_lt, n_pos]
  split
  all_goals (
    congr
    zmodify [CharP.cast_eq_zero]
    ring
  )

@[simp_lists_simps]
theorem Aeneas.Std.U64.getElem!_toBits_rotate_left(u: Aeneas.Std.U64)(w: Aeneas.Std.U32)(i: Nat)
  (i_idx: i < Spec.w 6)
: (u.rotate_left w).toBits[i]! = u.toBits[(i + Spec.w 6 - ↑w % Spec.w 6) % 64]!
:= by
  simp only [Spec.w, Fin.isValue, Fin.val_ofNat, Nat.reducePow, Nat.reduceMod] at *
  simp only [UScalar.toBits, List.getElem!_ofFn, i_idx, getElem!_pos, Fin.getElem_fin]
  simp_lists
  simp only [Fin.getElem_fin, ←getElem!_pos]
  simp only [Aeneas.Std.UScalar.rotate_left, Std.UScalarTy.numBits]
  simp only [BitVec.getElem!_rotateLeft, i_idx]


attribute [-simp] List.ofFn_succ

@[simp]
theorem Std.core.num.U64.toBits_to_le_bytes(u: Std.U64)
: (Std.core.num.U64.to_le_bytes u).toBits = u.toBits
:= by
  simp [Std.core.num.U64.to_le_bytes, Std.Array.toBits]
  apply List.ext_getElem
  · simp [List.length_toBits]
  intro i i_idx i_idx_2
  simp at i_idx_2
  have i_block_idx: i / 8 < 8 := by
    apply Nat.lt_of_mul_lt_mul_left (a := 8)
    calc _ ≤ i := by apply Nat.mul_div_le
         i < _ := i_idx_2
  simp [←getElem!_pos, i_block_idx, List.getElem!_toBits, List.getElem!_map]
  simp [Std.UScalar.toBits, List.getElem!_ofFn, Nat.mod_lt, i_idx_2]
  have :=  BitVec.toLEBytes_getElem!_testBit u.bv (i / 8) (i % 8) (by simp [Nat.mod_lt])
  rw [Byte.testBit] at this
  rw [BitVec.getElem_eq_testBit_toNat]
  rw [this, Nat.div_add_mod, ←getElem!_pos]

@[simp]
theorem Std.core.num.U64.toBits_from_le_bytes(arr : Aeneas.Std.Array Std.U8 8#usize)
: (Std.core.num.U64.from_le_bytes arr).toBits = arr.toBits
:= by
  rw [Std.core.num.U64.from_le_bytes, Std.Array.toBits]
  apply List.ext_getElem
  · simp
  intro i i_idx i_idx2
  simp at i_idx i_idx2
  have i_block_idx: i / 8 < 8 := by
    apply Nat.lt_of_mul_lt_mul_left (a := 8)
    calc _ ≤ i := by apply Nat.mul_div_le
         i < _ := i_idx
  simp [←getElem!_pos, List.getElem!_toBits, Std.UScalar.toBits]
  simp [List.getElem!_ofFn, *, Nat.mod_lt]
  rw [Byte.testBit]
  rw [BitVec.getElem!_eq_testBit_toNat]

/- theorem Nat.add_one_div_mul_gt(a b: Nat) -/
/- : a < (a / b + 1) * b -/
/- := by -/
/-   sorry -/

theorem Nat.div_spec(n q: Nat){d: Nat}
: 0 < d
→ (q = n / d ↔ d * q ≤ n ∧ n < d * (q + 1))
:= by
  intro d_pos
  apply Iff.intro
  · rintro rfl
    simp [Nat.mul_div_le, Nat.lt_mul_div_succ, d_pos]
  · rintro ⟨lb, ub⟩
    apply Nat.le_antisymm
    · have := Nat.div_le_div_right (c := d) lb
      rw [Nat.mul_div_cancel_left _ d_pos] at this
      exact this
    · have := Nat.div_lt_of_lt_mul ub
      have := Nat.le_of_lt_add_one this
      exact this

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

theorem List.getElem!_setSlice!_eq_ite_getElem!{α : Type u_1} [Inhabited α] (s s' : List α) (i j : ℕ)
: (s.setSlice! i s')[j]! =
  if i ≤ j ∧ j - i < s'.length ∧ j < s.length then
   s'[j - i]!
  else
   s[j]!
:= by
  assume j < s.length; case otherwise => simp [*, getElem!_neg]
  if h : i ≤ j ∧ j - i < s'.length then
    simp [h, List.getElem!_setSlice!_middle, *]
  else
    simp [h, *]
    simp [-not_and, not_and_or] at h
    rw [List.getElem!_setSlice!_same]
    omega

@[simp] theorem Aeneas.Std.UScalar.toBits_default (ty: Std.UScalarTy)
: (default: Std.UScalar ty).toBits = (List.replicate ty.numBits false)
:= by cases ty <;> simp +decide [default, Std.UScalar.toBits]

theorem Aeneas.Std.core.num.U64.getElem_toBits_getElem_to_le_bytes(u: Std.U64)(i j: Nat)
: j < 8
→ (U64.to_le_bytes u).val[i]!.toBits[j]! = u.toBits[8*i + j]!
:= by
  -- TODO: Analyze why this kind of thing makes sense. Do we want to have this
  -- kind of simplification? Didn't List.getELem!_toBits do quite the opposite?
  -- TODO: Also, does this actually make use of `toBits (f bs) = toBits bs`?
  -- I guess it also needs some kind of property over `toBits` and `getElem`.
  -- Idk.
  intro j_lt
  rw [getElem!_pos]; case h => simp [UScalar.toBits, j_lt]
  by_cases i_lt: i < 8; case neg =>
    simp at i_lt
    conv => lhs; arg 1; rw [getElem!_neg (h := by simp [i_lt])]
    conv => rhs; rw [getElem!_neg (h := by
      simp [UScalar.toBits]
      have: 8 * i ≥ 64 := Nat.mul_le_mul_left 8 i_lt
      omega
    )]
    simp only [UScalar.toBits_default, List.getElem_replicate]
    simp
  rw [getElem!_pos]; case pos.h => simp [i_lt]
  have ij_idx: 8 * i + j < 64 := by
    have: 8 * i ≤ 8 * 7 := Nat.mul_le_mul_left 8 (by omega)
    omega

  rw [getElem!_pos]; case pos.h => simp [UScalar.toBits, ij_idx]
  simp [to_le_bytes]
  unfold Std.UScalar.toBits
  simp
  trans u.bv.toLEBytes[i]!.testBit j
  · congr; rw [←getElem!_pos]
  · rw [BitVec.toLEBytes_getElem!_testBit, ←getElem!_pos]; assumption

theorem algos.StateArray.xor_byte_at.spec (input : StateArray) (byte : Std.U8) (pos : Std.Usize)
: 8 * pos.val < 1600
→ ∃ output,
  xor_byte_at (input : algos.StateArray) (byte : Std.U8) (pos : Std.Usize) = .ok output ∧
  ∀ j < output.toBits.length,
    output.toBits[j]! = if 8*pos ≤ j ∧ j < 8*pos + 8 then (input.toBits[j]! ^^ byte.toBits[j - 8*pos]!) else input.toBits[j]!
:= by
  intro valid_bound
  simp [xor_byte_at, Std.toResult] at valid_bound ⊢
  progress*
  intro j j_idx
  -- Flatten the result over lists
  simp [*, Std.Array.set, Std.Array.toBits]
  simp [*, List.toBits_set, Std.UScalar.getElem!_xor_toBits, Std.Array.toBits]
  simp [List.getElem!_setSlice!_eq_ite_getElem!]
  split
  case isTrue in_lane =>
    -- TODO: Maybe add some a - a % b = a / b or a / b = a - a % b simplifications here
    have j_block_eq_pos_block: j / 64 = pos.val / 8 := by
      have := Nat.div_spec j (pos.val / 8) (show 0 < 64 from by decide) |>.mpr
      simp +decide [Nat.mul_add] at this
      have := this (by omega) (by omega)
      simp [this]
    split
    case isTrue in_byte =>
      simp [Std.UScalar.getElem!_xor_toBits]
      rw [Aeneas.Std.core.num.U64.getElem_toBits_getElem_to_le_bytes]
      case a => omega
      have: 8 * pos.val ≤ j := by
        rw [←Nat.div_add_mod pos.val 8]
        simp +arith [Nat.mul_add]
        omega
      have: j < 8 * pos.val + 8 := by
        rw [←Nat.div_add_mod pos.val 8]
        simp +arith [Nat.mul_add]
        omega
      simp [*]
      simp [List.getElem!_toBits]
      congr 2
      · simp [j_block_eq_pos_block]
      · have: pos.val * 8 = pos.val * 8 := by rfl
        conv at this => lhs; rw [←Nat.div_add_mod pos.val 8]; simp +arith [Nat.mul_add]; rw [Nat.mul_comm, Nat.mul_comm 8]
        rw [Nat.sub_sub, this, Nat.add_comm]
        conv => lhs; rw [←Nat.div_add_mod j 64, j_block_eq_pos_block]
        conv => lhs; lhs; rhs; rw [←Nat.div_add_mod pos.val 8]
        simp +arith [Nat.mul_add]
        omega
      · conv => rhs; rw [←Nat.div_add_mod pos.val 8]
        simp +arith [Nat.mul_add]
        omega
    case isFalse =>
      simp_ifs
      simp +arith [List.getElem!_toBits, Nat.mod_eq_sub, j_block_eq_pos_block]
  case isFalse =>
    simp_ifs


@[progress]
theorem algos.StateArray.xor_lane.inner_loop.spec(i : Std.Usize)(input : Aeneas.Std.Array Std.U8 8#usize)(src : Std.Slice Std.U8)
: src.length ≤ input.length
→ ∃ output,
  inner_loop i input src = .ok output ∧
  ∀ j < output.toBits.length,
  output.toBits[j]! = if 8*i ≤ j ∧ j < src.toBits.length then input.toBits[j]! ^^ src.toBits[j]! else input.toBits[j]!
:= by
  intro input_big_enough
  unfold inner_loop
  simp [Std.toResult]
  progress*
  · intro j j_idx
    simp [*, Std.Array.set, Std.Array.toBits]
    simp [List.toBits_set, Nat.mul_add]
    split
    case isTrue already_processed =>
      simp_ifs
      rw [List.getElem!_setSlice!_same]
      simp
      omega
    case isFalse not_prev =>
      split
      case isTrue curr =>
        have: i.val = j / 8 := by
          apply Nat.div_spec j i.val (show 0 < 8 from by decide) |>.mpr
          simp [Nat.mul_add]
          omega
        simp [curr] at not_prev
        rw [List.getElem!_setSlice!_middle]; case h => simp; omega
        simp +arith [Std.UScalar.getElem!_xor_toBits, List.getElem!_toBits, this, Nat.mod_eq_sub]
      case isFalse not_yet =>
        rw [List.getElem!_setSlice!_same]
        simp
        omega
  · simp_ifs
    simp
termination_by src.toBits.length - i.val
decreasing_by scalar_decr_tac

@[progress]
theorem algos.StateArray.xor_lane.spec(input : Std.U64) (src : Std.Slice Std.U8)
: src.length ≤ 8
→ ∃ output,
  xor_lane input src = .ok output ∧
  ∀ j < output.toBits.length,
    output.toBits[j]! = if j < src.toBits.length then input.toBits[j]! ^^ src.toBits[j]! else input.toBits[j]!
:= by
  intro src_fits_in_lane
  unfold xor_lane inner
  simp [Std.toResult]
  progress*
  simp [Std.Array.toBits] at *
  intro j j_idx
  simp [*]

attribute [scalar_tac_simps] Nat.mul_add

@[progress]
theorem algos.StateArray.xor.inner_loop.spec (input : algos.StateArray) (other : Std.Slice Std.U8) (block_idx : Std.Usize)
: 8*block_idx.val ≤ other.val.length
→ other.toBits.length ≤ input.toBits.length
-- → 8 ∣ other.length
→ ∃ output leftover,
  inner_loop input block_idx other = .ok (output, leftover) ∧
  leftover = other.length / 8 ∧
  ∀ j < output.toBits.length,
  -- TODO: This doesn't cover all of `other`, but those which are not multiples of 8
    output.toBits[j]! = if 64 * block_idx.val ≤ j ∧ j < (other.val.take (8*leftover)).toBits.length then input.toBits[j]! ^^ other.toBits[j]! else input.toBits[j]!
:= by
  intro block_idx_lt input_big_enough
  unfold inner_loop

  simp [Std.toResult, Std.core.slice.index.Slice.index, Std.core.slice.index.SliceIndexRangeUsizeSlice.index]
  progress*
  -- TODO: This progress section is not super smooth, we handle the `index` call a bit crudely
  simp [*, Nat.mul_add]
  simp_ifs
  simp
  progress*
  · simp[*]
    intro j j_idx
    simp [*, Std.Array.set, Std.Array.toBits]
    simp [List.length_take, List.length_toBits, Nat.mul_comm 8, Nat.min_eq_left <| Nat.div_mul_le_self other.val.length 8]
    simp [List.toBits_set]
    split
    case isTrue prev =>
      simp_ifs
      rw [List.getElem!_setSlice!_same]
      simp; omega
    case isFalse not_prev =>
      simp [-not_and, not_and_or] at not_prev
      obtain not_prev | not_prev := not_prev; swap
      · simp_ifs
        have: 64 * block_idx + 64 ≤ j := by
          calc
            _ ≤ other.length / 8 * 8 * 8 := by
              rename i1.val ≤ other.val.length => cond
              simp [*] at cond
              have := Nat.div_le_div_right (c := 8) cond
              simp at this
              have := Nat.mul_le_mul_right 8 this
              simp only [←Nat.mul_comm 8 (_ + _), Nat.mul_add, Nat.mul_one] at this
              have := Nat.mul_le_mul_right 8 this
              simp only [←Nat.mul_comm 8 (_ + _), Nat.mul_add, Nat.mul_one] at this
              conv at this => lhs; simp +arith only
              simp
              assumption
              -- TODO: PAINFUL! Work this out better.
            _ ≤ j := by
              simp [not_prev]
        rw [List.getElem!_setSlice!_suffix]
        simp [←Nat.mul_comm 64, this]
      by_cases 64*block_idx ≤ j ∧ j < other.length * 8
      case pos curr =>
        have block_idx_eq_j: block_idx = j / 64 := by
          apply Nat.div_spec j block_idx (show 0 < 64 from by decide) |>.mpr
          omega
        simp_ifs
        rw [List.getElem!_setSlice!_middle]
        case h => simp [block_idx_eq_j]; omega
        rw [i6_post]; case a => simp; omega
        simp_ifs
        simp [List.getElem!_toBits]
        simp_lists
        simp +arith only [←Nat.mul_add_div, block_idx_eq_j, ←Nat.mod_eq_sub, Nat.div_add_mod]
        congr 2
        rw [Nat.mod_mod_of_dvd]
        decide
      case neg unprocessed =>
        simp_ifs
        rw [List.getElem!_setSlice!_same]
        simp [*, ←Nat.mul_comm 64]
        scalar_tac
  · rename_i block_idx_next_ge
    simp [*] at block_idx_next_ge
    simp [*]
    constructor
    · have := Nat.div_spec other.val.length block_idx.val ‹0 < 8›' |>.mpr (by scalar_tac)
      exact this
    · simp_ifs
termination_by input.length - block_idx.val
decreasing_by scalar_decr_tac

@[simp] theorem List.toBits_take(ls: List (Aeneas.Std.UScalar ty))(n: Nat)
: (ls.take n).toBits = ls.toBits.take (n* ty.numBits)
:= by
  apply List.ext_getElem
  · simp [List.length_toBits]
  simp [List.length_toBits, ←getElem!_pos]
  intro i i_idx
  by_cases cond: n ≤ ls.length
  case pos =>
    simp [cond] at i_idx
    have := Nat.div_lt_of_lt_mul (Nat.mul_comm _ _ ▸ i_idx)
    simp [List.getElem!_toBits]
    simp_lists
    simp [List.getElem!_toBits]
  case neg =>
    simp [not_le.mp] at cond
    simp [cond, le_of_lt] at i_idx
    have := Nat.div_lt_of_lt_mul (Nat.mul_comm _ _ ▸ i_idx)
    have := Nat.mul_lt_mul_left (by cases ty <;> simp : 0 < ty.numBits) |>.mpr cond
    simp [List.getElem!_toBits]
    simp_lists
    rw [List.take_of_length_le, List.getElem!_toBits]
    simp [List.length_toBits, ←Nat.mul_comm ty.numBits, this, le_of_lt]

@[simp] theorem List.toBits_drop(ls: List (Aeneas.Std.UScalar ty))(n: Nat)
: (ls.drop n).toBits = ls.toBits.drop (n* ty.numBits)
:= by
  apply List.ext_getElem
  · simp [List.length_toBits, Nat.sub_mul]
  simp [List.length_toBits, Nat.sub_mul, ←getElem!_pos]
  intro i i_idx
  simp [List.getElem!_toBits, Nat.mul_comm n, Nat.mul_add_div (show 0 < ty.numBits from by cases ty <;> simp)]

@[progress]
theorem Aeneas.Std.core.slice.index.SliceIndexRangeFromUsizeSlice.index.spec{T : Type}
  (r : Std.core.ops.range.RangeFrom Std.Usize)(input : Std.Slice T)
: r.start ≤ input.length
→  ∃ output,
    index r input = .ok output ∧
    output.val = input.val.drop r.start.val
  := by
    intro
    unfold index
    simp [*, Slice.drop]

theorem algos.StateArray.xor.spec'(input : algos.StateArray) (other : Std.Slice Std.U8)
-- /** Assumes `other.len() < self.len() * 8` and `other.len() > 0`. */
: other.toBits.length ≤ input.toBits.length
→ other.length > 0
→ ∃ output,
  xor input other = .ok output ∧
  ∀ j < output.toBits.length,
    output.toBits[j]! = if j < other.toBits.length then input.toBits[j]! ^^ other.toBits[j]! else input.toBits[j]!
:= by
  intro input_big_enough length_other_pos
  unfold xor inner
  simp [Std.core.slice.index.Slice.index]

  let* ⟨ processed, leftover, val_leftover, getElem!_toBits_processed ⟩ ← inner_loop.spec
  replace val_leftover := val_leftover.symm -- To prevent simp [*] from unfolding `val_leftover`
  let* ⟨ leftover_idx, val_leftover_idx ⟩ ← Std.Usize.mul_spec
  split
  case' isTrue =>
    let* ⟨ old_lane, set_lane ⟩ ← Std.Array.index_mut_usize_spec
    let* ⟨ rest_bytes, val_rest_bytes ⟩ ← Std.core.slice.index.SliceIndexRangeFromUsizeSlice.index.spec
    let* ⟨ new_lane, getElem!_toBits_new_lane ⟩ ← xor_lane.spec
  case' isFalse =>
    skip

  case isTrue =>
    intros j j_lt
    simp [*] at *
    simp [*, Std.Array.set, Std.Array.toBits]
    simp [*, List.toBits_set, List.getElem!_setSlice!_eq_ite_getElem!, List.length_toBits, List.toBits_take]

    if j_processed?: j < 64*leftover then
      -- Already processed by xor.inner
      simp_ifs
    else if j_new_lane?: j < 64*leftover + 64 then
      -- This is the new case, we get into `new_lane`.
      simp +decide only [val_leftover, not_lt] at j_processed? j_new_lane?
      have := Nat.div_spec (n := j) (q := leftover) ‹0 < 64›' |>.mpr (by scalar_tac)
      simp_ifs
      simp only [this, ←Nat.mul_comm 64, ←Nat.mod_eq_sub]
      simp [*, Nat.mod_lt]

      have := List.getElem!_toBits processed.val j
      simp at this -- The issue with having UScalar defined this way is that to not have to do these
                    -- manipulations I need to define specialized theorems for each type.
      rw [←this]

      if j_changed_part?: j < other.val.length * 8 then
        -- This is the part where bits were xored
        simp [*, Std.Array.toBits, Std.Slice.toBits]
        simp_ifs
        simp +arith [Nat.div_add_mod]
      else
        -- This is the part where bits were left unchanged
        simp [*, Std.Array.toBits, Std.Slice.toBits]
        simp_ifs
    else
      simp +decide only [val_leftover] at j_processed? j_new_lane?
      -- This section hasn't been processed yet.
      simp_ifs
  · simp
    intros
    simp [*, -val_leftover, ←val_leftover, ‹8 * (other.val.length / 8) = other.val.length›']

def IR.xor(s: List Bool)(r: List Bool): List Bool :=
  s.zipWith (· ^^ ·) r ++ s.drop r.length

@[simp] theorem IR.length_xor(s: List Bool)(r: List Bool)
: (IR.xor s r).length = s.length
:= by simp [IR.xor, Nat.min_def]
      split <;> omega

theorem IR.getElem!_xor(s: List Bool)(r: List Bool)(i: Nat)
: (IR.xor s r)[i]! = if i < r.length ∧ i < s.length then s[i]! ^^ r[i]! else s[i]!
:= by
  assume i < s.length; case otherwise => simp [getElem!_neg, *]
  unfold IR.xor
  if i < r.length then
    simp_lists
    simp_ifs
  else
    simp_lists
    simp_ifs
    congr; omega

@[progress]
theorem algos.StateArray.xor.spec (input : algos.StateArray) (other : Std.Slice Std.U8)
: other.toBits.length ≤ input.toBits.length
→ other.length > 0 
→ 8 ∣ other.length
→ ∃ output,
  xor input other = .ok output ∧
  output.toBits = IR.xor input.toBits other.toBits
:= by
  intro input_big_enough length_other_pos length_other_mult_8
  progress  with spec' as ⟨output,  output_spec⟩
  apply List.ext_getElem
  · simp
  intro j j_idx _
  simp [←getElem!_pos] at j_idx ⊢
  simp [*, IR.getElem!_xor]

-------------------------------------

@[progress]
theorem Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice.index.spec(input: Slice α)(r: ops.range.Range Usize)
: r.start.val ≤ r.end_.val
→ r.end_.val ≤ input.length
→ ∃ output,
  core.slice.index.SliceIndexRangeUsizeSlice.index r input = .ok output ∧
  output.val = input.val.extract r.start.val r.end_.val
:= by
  obtain ⟨start, end_⟩ := r
  intro r_proper end_lt_length
  simp at *
  rw [index]
  simp [List.slice, *]

@[progress]
theorem Aeneas.Std.core.slice.index.Slice.index.slice_index_range_usize_slice_spec(input: Slice α)(r: ops.range.Range Usize)
: r.start.val ≤ r.end_.val
→ r.end_.val ≤ input.length
→ ∃ output,
  core.slice.index.Slice.index (Std.core.slice.index.SliceIndexRangeUsizeSliceInst α) input r = .ok output ∧
  output.val = input.val.extract r.start.val r.end_.val
:= by simpa using SliceIndexRangeUsizeSlice.index.spec input r


@[progress] theorem Aeneas.Std.Array.to_slice_mut.spec'.{u} {α : Type u} {n : Std.Usize} (a : Aeneas.Std.Array α n)
: ∃ old new, Std.toResult a.to_slice_mut = Std.Result.ok (old, new) ∧
  old.val = a.val ∧ ∀ s: Slice α, (new s).val = (a.from_slice s).val
:= by
  progress as ⟨old, new, post⟩
  simp [Std.Array.to_slice, Std.Array.to_slice_mut] at post
  simp [post, Std.Array.to_slice, Std.Array.from_slice]

attribute [-progress] Aeneas.Std.Usize.sub_spec
@[progress] theorem Aeneas.Std.Usize.sub_spec' {x y : Aeneas.Std.Usize} (h : y.val ≤ x.val) :
  ∃ z, x - y = Std.Result.ok z ∧ z.val = x.val - y.val := by
  progress as ⟨z, post⟩
  rw [post]

theorem Aeneas.Std.UScalar.one_ShiftLeft_spec {ty1}(ty0: UScalarTy)(y : UScalar ty1)
  (hy : y.val < ty0.numBits)
: ∃ z, (1#ty0.numBits#uscalar) <<< y = .ok z ∧
  z.val = 2^y.val ∧
  z.bv = 1#ty0.numBits <<< y.val
  := by
  simp only [HShiftLeft.hShiftLeft, shiftLeft_UScalar, shiftLeft, hy, reduceIte, UScalar.size]
  simp only [BitVec.shiftLeft_eq, Result.ok.injEq, _root_.exists_eq_left', and_true, val]
  simp only [HShiftLeft.hShiftLeft, shiftLeft_UScalar, shiftLeft, hy, reduceIte, UScalar.size]
  simp only [bv_toNat, BitVec.shiftLeft_eq, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mod_mul_mod, one_mul]
  apply Nat.mod_eq_of_lt
  apply Nat.pow_lt_pow_of_lt Nat.one_lt_two ‹y.val < ty0.numBits›

@[progress] theorem Aeneas.Std.Usize.one_ShiftLeft_spec (y : UScalar ty1) (hy : y.val < UScalarTy.Usize.numBits)
: ∃ (z : Usize),
  1#usize <<< y = .ok z ∧
  z.val = 2 ^ y.val ∧
  z.bv = (1#usize).bv <<< y.val
:= by
  have: 1#usize = 1#(UScalarTy.Usize.numBits)#uscalar := by
    simp [Usize.ofNat, UScalar.ofNat, UScalar.ofNatCore, BitVec.ofNat, Fin.ofNat']
  rw [this]
  apply UScalar.one_ShiftLeft_spec _ _ hy
