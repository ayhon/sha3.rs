import Aeneas
import Shars.BitVec
import Shars.Definitions.Simple
import Sha3.Spec
/- import Sha3.Utils -/
import Aeneas.SimpLists.Init
import Sha3.Facts
import Init.Data.Vector.Lemmas
import Init.Data.Nat.Basic
import Shars.Verification.Simple.Utils
import Shars.Verification.Simple.Refinement

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

@[progress]
theorem simple.binxor.spec(a b: Bool)
: ∃ c, binxor a b = .ok c ∧ c = (a ^^ b)
:= by rw [binxor]; cases a <;> cases b <;> simp

@[progress]
theorem simple.xor_long_at_loop.spec(a b: Std.Slice Bool)(pos n offset: Std.Usize)
: b.length + pos.val ≤ Std.Usize.max
→ n = Nat.min a.length (b.length + ↑pos)
→ offset ≥ pos
→ ∃ output,/- {{{ -/
  xor_long_at_loop a b pos n offset = .ok output ∧
  output.length = a.length ∧
  ∀ j < output.length,
    output.val[j]! =
      if offset ≤ j ∧ j < n then
        (a[j]! ^^ b[j-pos.val]!)
      else a[j]!
:= by
  intro no_overflow n_def i_ge_pos
  rw [xor_long_at_loop]
  progress* <;> simp [*]
  · intro j j_lt
    simp [*]
    split
    case isTrue =>
      simp_ifs
      simp_lists
    case isFalse =>
      split
      case isFalse =>
        simp_ifs
        simp_lists
      case isTrue =>
        simp_lists
        -- simp_all
        simp [‹j = offset.val›']
  · simp_ifs
termination_by n.val - offset.val
decreasing_by scalar_decr_tac/- }}} -/

@[progress]
theorem simple.xor_long_at.spec(a b: Std.Slice Bool)(pos: Std.Usize)
: b.length + pos.val ≤ Std.Usize.max
→ ∃ output,
  xor_long_at a b pos = .ok output ∧
  output.length = a.length ∧
  ∀ j < output.length,
      output.val[j]! =
      if pos.val ≤ j ∧ j < pos.val + b.length then
         (a.val[j]! ^^ b.val[j-pos.val]!)
      else
          a.val[j]!
:= by/- {{{ -/
  intro no_overflowa
  rw [xor_long_at]

  let* ⟨ i2, i2_post ⟩ ← Aeneas.Std.Usize.add_spec
  let* ⟨ n, n_post ⟩ ← Std.core.cmp.impls.OrdUsize.min_spec
  let* ⟨ res, res_post_1, res_post_2 ⟩ ← simple.xor_long_at_loop.spec
  -- simp_lists [*] at *
  simp [*]
  intro j j_lt
  simp [*]
  split <;> simp_ifs

@[simp]
theorem BitVec.setWidth_eq_cast{n m: Nat}(bv: BitVec n)(h: n = m)
: bv.setWidth m = bv.cast h
:= by
  ext i i_lt
  simp only [getElem_setWidth, getElem_cast]
  simp only [GetElem.getElem]
  exact rfl

@[progress]
theorem simple.xor_long.spec(a b: Std.Slice Bool)
: ∃ c,
  xor_long a b = .ok c ∧
  c.length = a.length ∧
  c.val.toBitVec = (a.val.toBitVec ^^^ b.val.toBitVec.setWidth a.length).setWidth c.length
  /- c = a.val.zipWith xor b ++ a.val.drop b.length -/
:= by/- {{{ -/
  rw [xor_long]
  progress*

  simp [*, BitVec.ofNatLT]

  ext j j_idx_res
  replace res_bit := res_post_2 j j_idx_res
  -- NOTE: Replace [·]! with [·] so I can use theorems such as
  --        · `getElem_cast`
  --        · `getElem_xor`
  --        · `getElem_setWidth`
  simp only [Std.Slice.getElem!_Nat_eq] at res_bit
  have j_idx_a: j < a.length := by simpa [*] using j_idx_res
  simp only [getElem!_pos, *] at res_bit
  simp [*]; clear res_bit
  split_all
  · simp [getElem!_pos, getElem?_pos, *]
  · simp [getElem?_neg, *]

@[progress]
theorem  simple.StateArray.index.spec
  (self : StateArray)(x y z: Std.Usize)
(x_idx: x.val < 5)
(y_idx: y.val < 5)
(z_idx: z.val < Spec.w 6)
: ∃ output, self.index (x,y,z) = .ok output ∧
    output = self.toSpec.get x.val y.val z.val
:= by
  rw [index]
  let* ⟨ i, i_post ⟩ ← Aeneas.Std.Usize.mul_spec
  let* ⟨ i1, i1_post ⟩ ← Aeneas.Std.Usize.add_spec
  simp [i_post] at i1_post
  let* ⟨ i2, i2_post ⟩ ← Aeneas.Std.Usize.mul_spec
  let* ⟨ i3, i3_post ⟩ ← Aeneas.Std.Usize.add_spec
  have: Spec.w 6 * (5 * ↑y + ↑x) + ↑z < 1600 := by scalar_tac
  let* ⟨ res, res_post ⟩ ← Aeneas.Std.Array.index_usize_spec
  simp [*, Std.Usize.max]
  simp [Spec.Keccak.StateArray.get, Spec.Keccak.StateArray.encodeIndex]
  simp [Nat.mod_eq_of_lt x_idx, Nat.mod_eq_of_lt y_idx, Nat.mod_eq_of_lt z_idx]
  simp [toSpec, BitVec.getElem_ofBoolListLE]
  simp [getElem_eq_getElem!]

-- set_option trace.ScalarTac true in
-- set_option trace.Saturate true in
@[progress]
theorem simple.StateArray.index_mut.spec
  (self : simple.StateArray)(x y z: Std.Usize)
(x_idx: x.val < 5)
(y_idx: y.val < 5)
(z_idx: z.val < Spec.w 6)
: ∃ val upd, self.index_mut (x,y,z) = .ok (val, upd) ∧
    val = self.toSpec.get x.val y.val z.val ∧
    ∀ b, (upd b).toSpec = self.toSpec.set x.val y.val z.val b
:= by
  rw [index_mut]
  let* ⟨ i, i_post ⟩ ← Aeneas.Std.Usize.mul_spec
  let* ⟨ i1, i1_post ⟩ ← Aeneas.Std.Usize.add_spec
  simp only [*] at i1_post
  let* ⟨ i2, i2_post ⟩ ← Aeneas.Std.Usize.mul_spec
  simp only [*] at i2_post
  let* ⟨ c, c_post ⟩ ← Aeneas.Std.Usize.add_spec
  simp only [*] at c_post
  have c_idx :↑c < Std.Array.length self := by scalar_tac
  let* ⟨ celem, celem_post ⟩ ← Aeneas.Std.Array.index_mut_usize_spec
  simp [-Bool.forall_bool,celem_post]
  simp only [Std.Array.length] at c_idx
  have c_encode: c.val = @Spec.Keccak.StateArray.encodeIndex 6 x.val.cast y.val.cast z.val.cast := by
    simp [Spec.Keccak.StateArray.encodeIndex, Nat.mod_eq_of_lt, *]
  constructor
  · simp [Spec.Keccak.StateArray.get, ←c_encode, toSpec]; rw [getElem_eq_getElem!]
  · intro b
    ext i j k
    simp [Spec.Keccak.StateArray.get, Spec.Keccak.StateArray.set, ←c_encode]
    simp [toSpec, Spec.Keccak.StateArray.set, Std.Array.set]
    simp [BitVec.getElem_set]
    split
    case isTrue h =>
      simp [←h, c_encode]
    case isFalse h =>
      rw [←c_encode] at h
      simp [List.getElem_set_ne h]

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

/- theorem Aeneas.Std.Usize.one_ShiftLeft_spec {ty1}(ty0: UScalarTy)(y : UScalar ty1) (size : Nat) -/
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
