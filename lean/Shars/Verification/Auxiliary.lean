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

/- @[simp] -/
/- theorem U64.numBits_eq_w -/
/- : Std.UScalarTy.U64.numBits = Spec.w 6 -/
/- := by simp [Spec.w] -/

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
