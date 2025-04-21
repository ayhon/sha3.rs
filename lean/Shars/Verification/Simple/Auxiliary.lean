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
theorem simple.add_to_vec_loop.spec(dst: Vec Bool)(other: Vec Bool)(o n i: Std.Usize)
: o.val + n.val < Std.Usize.max
→ n.val < other.length
→ ∃ nb_added output,
  add_to_vec_loop core.marker.CopyBool dst o other n i = .ok (nb_added, output) ∧
  nb_added = Nat.min (n.val) (dst.length - o.val) - i.val + i.val ∧
  ∀ j: Nat, j < dst.length →
    output.val[j]! = if o.val + i.val ≤ j ∧ j < o.val + n.val then other.val[j-o.val]!
    else dst.val[j]!
:= by/- {{{ -/
  intro no_overflow o_other_idx
  rw [add_to_vec_loop]
  split
  case isTrue i_bnd =>
    let* ⟨ oi, oi_post ⟩ ← Aeneas.Std.Usize.add_spec
    split
    case isTrue oi_idx => 
      let* ⟨ t, t_post ⟩ ← Aeneas.Std.Slice.index_usize_spec
      let* ⟨ dst', dst'_post ⟩ ← Aeneas.Std.Slice.update_spec
      fsimp [*] at dst'_post
      let* ⟨ i3, i3_post ⟩ ← Aeneas.Std.Usize.add_spec
      let* ⟨ nb_added, output, nb_added_post, output_post ⟩ ← spec
      simp [*] at *
      constructor
      · scalar_tac
      · intro j j_idx
        rw [output_post j j_idx]; clear output_post
        split_all
        · rfl
        · scalar_tac
        · simp [‹j = o + i›']
          simp_lists
        · simp_lists
    case isFalse oi_oob=>
      simp [*] at *
      constructor
      · scalar_tac
      · intros j _
        simp_ifs
  case isFalse =>
    simp
    constructor
    · scalar_tac
    · intro j _ 
      simp_ifs
termination_by n.val - i.val
decreasing_by scalar_decr_tac/- }}} -/

/- @[reducible] def UScalar.ofNat {ty : UScalarTy} (x : Nat) -/
/-   (hInBounds : x ≤ UScalar.cMax ty := by decide) : UScalar ty := -/


@[progress]
theorem simple.add_to_vec.spec(dst: Std.Slice Bool)(other: Vec Bool)(o n: Std.Usize)
: o.val + n.val < Std.Usize.max
→ n.val < other.length
→ ∃ nb_added output,
  add_to_vec core.marker.CopyBool dst o other n = .ok (nb_added, output) ∧
  nb_added = Nat.min (n.val) (dst.length - o.val) ∧
  ∀ j < dst.length, 
    output.val[j]! = if o.val ≤ j ∧ j < o.val + n.val then other.val[j-o.val]!
    else  dst.val[j]!
:= by simpa using add_to_vec_loop.spec dst other o n (i := 0#usize)

@[progress]
theorem simple.binxor.spec(a b: Bool)
: ∃ c, binxor a b = .ok c ∧ c = (a ^^ b)
:= by rw [binxor]; cases a <;> cases b <;> simp

@[progress]
theorem simple.xor_long_at_loop.spec(a b: Std.Slice Bool)(pos n i: Std.Usize)
: b.length + pos.val ≤ Std.Usize.max
→ n = Nat.min a.length (b.length + ↑pos)
→ i ≥ pos
→ ∃ output,/- {{{ -/
  xor_long_at_loop a b pos n i = .ok output ∧ 
  output.length = a.length ∧
  ∀ j <a.length, 
    if i ≤ j ∧ j < n then output[j]! = (a[j]! ^^ b[j-pos.val]!)
    else output[j]! = a[j]!
:= by
  intro no_overflow n_def i_ge_pos
  rw [xor_long_at_loop]
  progress* <;> simp [*]
  · intro j j_lt
    replace res_post_2 := res_post_2 j (by simp [*])
    simp [*] at res_post_2
    split_all
    · simp_lists [*]
    · scalar_tac
    · simp only [res_post_2]
      simp [‹j = i.val + pos›']
      simp_lists
    · simp only [res_post_2]
      simp_lists
  · scalar_tac
termination_by n.val - i.val
decreasing_by scalar_decr_tac/- }}} -/

@[progress]
theorem simple.xor_long_at.spec(a b: Std.Slice Bool)(pos: Std.Usize)
: b.length + pos.val ≤ Std.Usize.max
→ ∃ output,
  xor_long_at a b pos = .ok output ∧ 
  output.length = a.length ∧
  ∀ j < a.length, 
      output[j]! =
      if pos.val ≤ j ∧ j < pos.val + b.length then 
         (a[j]! ^^ b[j-pos.val]!)
      else 
          a[j]!
:= by/- {{{ -/
  intro no_overflowa
  rw [xor_long_at]

  let* ⟨ i2, i2_post ⟩ ← Aeneas.Std.Usize.add_spec
  let* ⟨ n, n_post ⟩ ← Std.core.cmp.impls.OrdUsize.min_spec
  let* ⟨ res, res_post_1, res_post_2 ⟩ ← simple.xor_long_at_loop.spec
  simp_lists [*] at *
  intro j j_lt
  replace res_post_2 := res_post_2 j j_lt
  split_all
  · simpa using res_post_2
  · scalar_tac
  · scalar_tac
  · simpa using res_post_2


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
  c.toBitVec = (a.toBitVec ^^^ b.toBitVec.setWidth a.length).setWidth c.length
  /- c = a.val.zipWith xor b ++ a.val.drop b.length -/
:= by/- {{{ -/
  rw [xor_long]
  progress*

  simp [*, BitVec.ofNatLt]
  
  ext j j_idx_res
  have j_idx_a: j < a.length := by simpa [*] using j_idx_res
  replace res_bit := res_post_2 j j_idx_a
  -- NOTE: Replace [·]! with [·] so I can use theorems such as 
  --        · `getElem_cast`
  --        · `getElem_xor`
  --        · `getElem_setWidth`
  simp only [Std.Slice.getElem!_Nat_eq] at res_bit
  simp only [getElem!_pos, *] at res_bit
  /- simp only [BitVec.getElem_xor] -/
  simp [Std.Slice.toBitVec, res_bit]; clear res_bit
  split_all
  · simp [getElem!_pos, getElem?_pos, *]
  · simp [getElem?_neg, *]

@[progress]
theorem simple.xor_long.spec'(a b: Std.Slice Bool)
: ∃ c, 
  xor_long a b = .ok c ∧
  c.length = a.length ∧
  c.val = (a.toBitVec ^^^ b.toBitVec.setWidth a.length).toList
  /- c = a.val.zipWith xor b ++ a.val.drop b.length -/
:= by/- {{{ -/
  rw [xor_long]
  progress*
  simp at *

  simp [*, BitVec.ofNatLt, BitVec.toList]

  apply List.ext_getElem (by simp [res_post_1]); intro j j_idx_res j_idx_other
  simp at j_idx_other
  rw [getElem_eq_getElem!]
  rw [res_post_2 j j_idx_other]
  split_all
  · simp [Std.Slice.toBitVec, List.getElem!_eq_getElem?_getD, j_idx_other]
  · simp at *
    simp [Std.Slice.toBitVec, *, getElem_eq_getElem!]

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
  · simp [*, simple.W.spec]
    apply le_of_lt 
    calc Spec.w 6 * (5 * ↑y + ↑x)
     _ ≤ Spec.w 6 * (5 * 5) := by
          apply Nat.mul_le_mul_left (k := Spec.w 6)
          exact Nat.le_of_lt (Nat.lt_packing_right x_idx y_idx)
     _ < 2^32 - 1 := by simp [Spec.w]
     _ ≤ Std.Usize.max := Std.Usize.max_bound
  let* ⟨ i3, i3_post ⟩ ← Aeneas.Std.Usize.add_spec
  · simp [*, simple.W.spec]
    apply le_of_lt 
    calc Spec.w 6 * (5 * ↑y + ↑x) + ↑z
     _ ≤ Spec.w 6 * (5 * 5 - 1) + ↑z := by 
          apply Nat.add_le_add_right (k := ↑z)
          apply Nat.mul_le_mul_left (k := Spec.w 6)
          exact Nat.le_pred_of_lt (Nat.lt_packing_right x_idx y_idx)
     _ < Spec.w 6 * (5 * 5) := by
          apply Nat.lt_packing_right z_idx (by decide: 5*5 - 1 < 5 * 5)
     _ < 2^32 - 1 := by simp [Spec.w]
     _ ≤ Std.Usize.max := Std.Usize.max_bound
  have: Spec.w 6 * (5 * ↑y + ↑x) + ↑z < 1600 := by
    simp [Spec.w]
    calc Spec.w 6 * (5 * ↑y + ↑x) + ↑z
     _ ≤ Spec.w 6 * (5 * 5 - 1) + ↑z := by 
          apply Nat.add_le_add_right (k := ↑z)
          apply Nat.mul_le_mul_left (k := Spec.w 6)
          exact Nat.le_pred_of_lt (Nat.lt_packing_right x_idx y_idx)
     _ < Spec.w 6 * (5 * 5) := by
          apply Nat.lt_packing_right z_idx (by decide: 5*5 - 1 < 5 * 5)
  let* ⟨ res, res_post ⟩ ← Aeneas.Std.Array.index_usize_spec
  · simp [*, W.spec]
  simp [*, simple.W.spec, Std.Usize.max]
  simp [Spec.Keccak.StateArray.get, Spec.Keccak.StateArray.encodeIndex]
  simp [Nat.mod_eq_of_lt x_idx, Nat.mod_eq_of_lt y_idx, Nat.mod_eq_of_lt z_idx]
  simp [toSpec, Std.Array.toBitVec, BitVec.getElem_ofBoolListLE]
  simp [getElem_eq_getElem!]

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
  · simp [*, W.spec]
    -- TODO: Hmm, this should be using transitivity to get <, no?
    apply le_of_lt
    calc Spec.w 6 * (5 * y.val + x.val)
      _ < Spec.w 6 * (5 * 5) := by 
          apply Nat.mul_lt_mul_left (by simp [Spec.w]: 0 < Spec.w 6) |>.mpr
          exact Nat.lt_packing_right x_idx y_idx
      _ < 2^32 - 1 := by decide
      _ ≤ Std.Usize.max := Std.Usize.max_bound
  simp only [*] at i2_post
  let* ⟨ c, c_post ⟩ ← Aeneas.Std.Usize.add_spec
  · simp [*, W.spec]
    apply le_of_lt
    calc Spec.w 6 * (5 * ↑y + ↑x) + ↑z
     _ ≤ Spec.w 6 * (5 * 5 - 1) + ↑z := by 
          apply Nat.add_le_add_right (k := ↑z)
          apply Nat.mul_le_mul_left (k := Spec.w 6)
          exact Nat.le_pred_of_lt (Nat.lt_packing_right x_idx y_idx)
     _ < Spec.w 6 * (5 * 5) := by
          apply Nat.lt_packing_right z_idx (by decide: 5*5 - 1 < 5 * 5)
     _ < 2^32 - 1 := by simp [Spec.w]
     _ ≤ Std.Usize.max := Std.Usize.max_bound
  simp only [*] at c_post
  have c_idx :↑c < Std.Array.length self := by
    simp [*, W.spec]
    calc Spec.w 6 * (5 * ↑y + ↑x) + ↑z
     _ ≤ Spec.w 6 * (5 * 5 - 1) + ↑z := by 
          apply Nat.add_le_add_right (k := ↑z)
          apply Nat.mul_le_mul_left (k := Spec.w 6)
          exact Nat.le_pred_of_lt (Nat.lt_packing_right x_idx y_idx)
     _ < Spec.w 6 * (5 * 5) := by
          apply Nat.lt_packing_right z_idx (by decide: 5*5 - 1 < 5 * 5)
  let* ⟨ celem, celem_post ⟩ ← Aeneas.Std.Array.index_mut_usize_spec
  simp [-Bool.forall_bool,celem_post]
  simp only [Std.Array.length] at c_idx
  have c_encode: c.val = @Spec.Keccak.StateArray.encodeIndex 6 x.val.cast y.val.cast z.val.cast := by
    simp [Spec.Keccak.StateArray.encodeIndex, Nat.mod_eq_of_lt y_idx, Nat.mod_eq_of_lt x_idx, Nat.mod_eq_of_lt z_idx, c_post, W.spec]
  constructor
  · simp [Spec.Keccak.StateArray.get, ←c_encode, toSpec, Std.Array.toBitVec]; rw [getElem_eq_getElem!]
  · intro b
    ext i j k
    simp [Spec.Keccak.StateArray.get, Spec.Keccak.StateArray.set, ←c_encode]
    simp [toSpec, Spec.Keccak.StateArray.set, Std.Array.set]
    simp [BitVec.getElem_set]
    split
    case isTrue h =>
      simp [←h, c_encode, Std.Array.toBitVec]
    case isFalse h =>
      rw [←c_encode] at h
      simp [List.getElem_set_ne h, Std.Array.toBitVec]

