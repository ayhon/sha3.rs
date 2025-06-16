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
attribute [-simp] List.getElem!_eq_getElem?_getD List.ofFn_succ
attribute [simp] Aeneas.Std.Slice.set
attribute [scalar_tac_simps] Nat.mul_add Nat.mul_sub

attribute [-progress] Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice.index_mut.progress_spec

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

@[progress]
theorem Aeneas.Std.core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut.spec {T : Type}
  (r : Std.core.ops.range.RangeFrom Std.Usize) (s : Std.Slice T)
: r.start.val ≤ s.length
→  ∃ old new,
  index_mut r s =  .ok (old, new) ∧
  old.val = s.val.drop r.start.val ∧
  ∀ u, u.length = s.length - r.start.val → (new u).val = s.val.setSlice! r.start.val u.val
:= by
  intro cond
  simp [index_mut, cond]
  intro u cond2
  simp [cond2]

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
theorem Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice.index_mut.spec {T : Type}
  (r : Std.core.ops.range.Range Std.Usize) (s : Std.Slice T)
: r.start.val ≤ r.end_.val
→ r.end_.val ≤ s.length
→ ∃ old new,
  index_mut r s =  .ok (old, new) ∧
  old.val = s.val.slice r.start.val r.end_.val ∧
  ∀ u, u.length = r.end_.val - r.start.val → (new u).val = s.val.setSlice! r.start.val u.val
:= by
  intro cond cond'
  simp [index_mut, cond, cond']
  intro u cond2
  simp [cond2]


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
  progress*
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


@[simp] theorem Aeneas.Std.UScalar.toBits_default (ty: Std.UScalarTy)
: (default: Std.UScalar ty).toBits = (List.replicate ty.numBits false)
:= by cases ty <;> simp +decide [default, Std.UScalar.toBits]

theorem Aeneas.Std.core.num.U64.getElem_toBits_getElem_to_le_bytes(u: Std.U64)(i j: Nat)
: j < 8
→ (U64.to_le_bytes u).val[i]!.toBits[j]! = u.toBits[8*i + j]!
:= by
  intro j_lt
  rw [getElem!_pos]; case h => simp [UScalar.toBits, j_lt]
  assume i_lt: i < 8; case otherwise =>
    simp at i_lt
    conv => lhs; arg 1; rw [getElem!_neg (h := by simp [i_lt])]
    conv => rhs; rw [getElem!_neg (h := by
      simp [UScalar.toBits]
      have: 8 * i ≥ 64 := Nat.mul_le_mul_left 8 i_lt
      omega
    )]
    simp only [UScalar.toBits_default, List.getElem_replicate]
    simp
  rw [getElem!_pos]; case h => simp [i_lt]
  have ij_idx: 8 * i + j < 64 := by
    have: 8 * i ≤ 8 * 7 := Nat.mul_le_mul_left 8 (by omega)
    omega

  rw [getElem!_pos]; case h => simp [UScalar.toBits, ij_idx]
  simp [to_le_bytes]
  unfold Std.UScalar.toBits
  simp
  trans u.bv.toLEBytes[i]!.testBit j
  · congr; rw [←getElem!_pos]
  · rw [BitVec.toLEBytes_getElem!_testBit, ←getElem!_pos]; assumption

section IR

def IR.xor(s: List Bool)(r: List Bool): List Bool :=
  s.zipWith (· ^^ ·) r ++ s.drop r.length

@[simp] theorem IR.length_xor(s r: List Bool): (IR.xor s r).length = s.length := by
  simp [IR.xor, Nat.min_def]
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

theorem IR.xor_assoc(s0 s1 s2: List Bool)
: IR.xor (IR.xor s0 s1) s2 = IR.xor s0 (IR.xor (s1.setWidth s0.length) s2)
:= by
  apply List.ext_getElem
  · simp
  simp [←getElem!_pos]
  intro i i_idx
  simp [IR.getElem!_xor, i_idx]
  by_cases i < s2.length <;> by_cases i < s1.length <;> simp [*, getElem!_neg]

end IR

-- @[progress]
theorem algos.StateArray.xor_byte_at.spec' (input : StateArray) (byte : Std.U8) (pos : Std.Usize)
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
    simp [←j_block_eq_pos_block, ←Nat.mul_comm 64, ←Nat.mod_eq_sub]
    simp [j_block_eq_pos_block, ←Nat.mul_comm 8, ←Nat.mod_eq_sub]
    simp [←j_block_eq_pos_block]

    split
    case isTrue in_byte =>
      simp [Std.UScalar.getElem!_xor_toBits]
      rw [Aeneas.Std.core.num.U64.getElem_toBits_getElem_to_le_bytes]; case a => omega
      simp_ifs
      simp_scalar
      simp [List.getElem!_toBits]
      congr 1
      scalar_tac
    case isFalse =>
      simp_ifs
      simp +arith [List.getElem!_toBits, Nat.mod_eq_sub, j_block_eq_pos_block]
  case isFalse =>
    simp_ifs

@[progress]
theorem algos.StateArray.xor_byte_at.spec (input : StateArray) (byte : Std.U8) (pos : Std.Usize)
: 8 * pos.val < 1600
→ ∃ output,
  xor_byte_at (input : algos.StateArray) (byte : Std.U8) (pos : Std.Usize) = .ok output ∧
  output.toBits = IR.xor input.toBits (List.replicate (8*pos.val) false ++ byte.toBits)
:= by
  intro pos_bit_idx
  progress with spec' as ⟨output, output_post⟩
  apply List.ext_getElem
  · simp
  simp [←getElem!_pos]
  intro i i_idx
  simp [*, IR.getElem!_xor, Std.Array.toBits]
  split
  case isTrue inrange =>
    simp_lists [Std.UScalar.length_toBits, Std.UScalarTy.numBits]
    simp_ifs
  case isFalse not_inrange =>
    simp_lists [Std.UScalar.length_toBits, Std.UScalarTy.numBits]
    split <;> simp

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

@[progress]
theorem algos.StateArray.xor.inner_loop.spec (input : algos.StateArray) (other : Std.Slice Std.U8) (block_idx : Std.Usize)
: 8*block_idx.val ≤ other.val.length
→ other.toBits.length ≤ input.toBits.length
-- → 8 ∣ other.length
→ ∃ output leftover,
  inner_loop input block_idx other = .ok (output, leftover) ∧
  leftover = other.length / 8 ∧
  ∀ j < output.toBits.length,
  -- This doesn't cover all of `other`, but those which are not multiples of 8
    output.toBits[j]! = if 64 * block_idx.val ≤ j ∧ j < (other.val.take (8*leftover)).toBits.length then input.toBits[j]! ^^ other.toBits[j]! else input.toBits[j]!
:= by
  intro block_idx_lt input_big_enough
  unfold inner_loop

  simp [Std.toResult, Std.core.slice.index.Slice.index]
  progress*
  · simp[*]
    intro j j_idx
    simp [*, Std.Array.set, Std.Array.toBits]
    simp [List.length_take, List.length_toBits, Nat.mul_comm 8, Nat.min_eq_left <| Nat.div_mul_le_self other.val.length 8]
    simp [List.toBits_set]
    split
    case isTrue prev =>
      simp_ifs
      -- simp_lists -- TODO: Check how much more inefficient it is with `
      rw [List.getElem!_setSlice!_same]; case h => scalar_tac
    case isFalse not_prev =>
      simp [-not_and, not_and_or] at not_prev
      obtain not_prev | not_prev := not_prev; swap
      · simp_ifs
        have: 64 * block_idx + 64 ≤ j := calc
            _ ≤ 64 * (other.length / 8) := by scalar_tac
            _ ≤ j := by scalar_tac
        rw [List.getElem!_setSlice!_suffix]
        simp [←Nat.mul_comm 64, this]
      by_cases 64*block_idx ≤ j ∧ j < other.length * 8
      case pos curr =>
        have block_idx_eq_j: block_idx = j / 64 := by
          apply Nat.div_spec j block_idx (show 0 < 64 from by decide) |>.mpr
          omega
        simp_ifs
        rw [List.getElem!_setSlice!_middle]; case h => scalar_tac
        rw [i6_post]; case a => scalar_tac
        simp [*]
        simp_ifs
        simp [List.getElem!_toBits]
        simp_lists
        simp +arith only [←Nat.mul_add_div, block_idx_eq_j, ←Nat.mod_eq_sub, Nat.div_add_mod, List.getElem!_toBits, Std.UScalarTy.numBits]
      case neg unprocessed =>
        simp_ifs
        rw [List.getElem!_setSlice!_same]; case h => scalar_tac
  · rename_i block_idx_next_ge
    simp [*, Nat.div_spec other.val.length block_idx.val ‹0 < 8›' |>.symm]
    constructor
    · scalar_tac
    · simp_ifs
termination_by input.length - block_idx.val
decreasing_by scalar_decr_tac

theorem algos.StateArray.xor.spec'(input : algos.StateArray) (other : Std.Slice Std.U8)
: other.toBits.length ≤ input.toBits.length
→ ∃ output,
  xor input other = .ok output ∧
  ∀ j < output.toBits.length,
    output.toBits[j]! = if j < other.toBits.length then input.toBits[j]! ^^ other.toBits[j]! else input.toBits[j]!
:= by
  intro input_big_enough
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

      have := List.getElem!_toBits processed.val j |>.symm
      simp at this -- The issue with having UScalar defined this way is that to not have to do these
                    -- manipulations I need to define specialized theorems for each type. I don't want
                    -- to have the intermediary `ty.numBits` call, or at least have it be abstracted away.
                    -- Perhaps a better handling of `reducible` definitions would allow this.
      rw [this]

      if j_changed_part?: j < other.val.length * 8 then
        -- This is the part where bits were xored
        simp [*]
        simp_ifs
        simp +arith [Nat.div_add_mod]
      else
        -- This is the part where bits were left unchanged
        simp [*]
        simp_ifs
    else
      simp +decide only [val_leftover] at j_processed? j_new_lane?
      -- This section hasn't been processed yet.
      simp_ifs
  · simp
    intros
    simp [*, -val_leftover, ←val_leftover, ‹8 * (other.val.length / 8) = other.val.length›']

@[progress]
theorem algos.StateArray.xor.spec (input : algos.StateArray) (other : Std.Slice Std.U8)
: other.toBits.length ≤ input.toBits.length
→ ∃ output,
  xor input other = .ok output ∧
  output.toBits = IR.xor input.toBits other.toBits
:= by
  intro input_big_enough
  progress  with spec' as ⟨output,  output_spec⟩
  apply List.ext_getElem
  · simp
  intro j j_idx _
  simp [←getElem!_pos] at j_idx ⊢
  simp [*, IR.getElem!_xor]

-- set_option trace.Progress true in
theorem algos.StateArray.copy_to_loop.spec
  (src : StateArray) (input : Std.Slice Std.U8) (i : Std.Usize)
: ∃ output,
  copy_to_loop src input i = .ok output ∧
  output.toBits = input.toBits.setSlice! (64*i.val) (src.toBits.drop (64*i.val))
:= by
  unfold copy_to_loop
  simp [DerefalgosStateArrayArrayU6425.deref, Std.toResult,
        Std.core.array.Array.index,       Std.core.array.Array.index_mut,
        Std.core.slice.index.Slice.index, Std.core.slice.index.Slice.index_mut,
        Aeneas.Std.core.ops.index.Index.index,
        Std.core.ops.index.IndexSliceInst,
      ]
  progress*? by simp [*]; scalar_tac
  · -- Copying over a chunk from `src` to `input`
    simp +arith [*, Std.Array.toBits, Std.Slice.toBits] at *
    simp_lists
  · -- Copying the leftover bits from `src` to `input`
    simp [*, Std.Array.toBits, Std.Slice.toBits] at *
    rw [__discr_post_2]; case a => simp +arith [*]; omega
    simp +arith [*, List.slice]
    simp_lists
    conv => rhs; rw [List.setSlice!_truncate]
    simp +arith [Nat.mul_sub]
  · -- There is no more space at `input`
    simp [*] at *
    rw [List.setSlice!_of_length_le]
    scalar_tac
  . -- There are no bits left to copy from `src`
    have: 64 * i.val ≥ 1600 := by
      change 64 * i.val ≥ 64 * 25
      apply Nat.mul_le_mul_left
      omega
    simp [*]
termination_by input.length - i.val
decreasing_by
  simp [*] -- TODO: Why do I need this `simp [*]`
  scalar_decr_tac

@[progress]
theorem algos.StateArray.copy_to.spec
  (src : StateArray) (input : Std.Slice Std.U8)
: ∃ output,
  copy_to src input = .ok output ∧
  output.toBits = input.toBits.setSlice! 0 src.toBits
:= by
  unfold copy_to
  progress with algos.StateArray.copy_to_loop.spec
  simp [*]

-------------------------------------

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
