import Aeneas
import Shars.BitVec
import Shars.Definitions.Simple
import Sha3.Spec
/- import Sha3.Utils -/
import Aeneas.SimpLists.Init
import Sha3.Facts
import Init.Data.Vector.Lemmas
import Init.Data.Nat.Basic

section Refinement

set_option maxHeartbeats 1000000

/- section Extras -/
attribute [-simp] List.getElem!_eq_getElem?_getD
attribute [simp] Aeneas.Std.Slice.set

notation "‹" term "›'" => (by scalar_tac: term)

theorem and_imp_of_ite{cond: Prop}[Decidable cond]: (if cond then P else Q) = ((cond → P) ∧ ((¬ cond) → Q)) := by
  split <;> simp [*]

open Aeneas hiding Std.Array in 
@[simp, scalar_tac_simps]
theorem OrdUsize.min_val (x y : Std.Usize) : (Std.core.cmp.impls.OrdUsize.min x y).val = Nat.min x.val y.val := by
  simp [Std.core.cmp.impls.OrdUsize.min]; split <;> simp [*] <;> omega

-- TODO: derive automatically with `progress_pure_def` applied to `Std.core.cmp.impls.OrdUsize.min`
open Aeneas hiding Std.Array in 
@[progress]
theorem Std.core.cmp.impls.OrdUsize.min_spec (x y : Std.Usize) :
  ∃ z, Std.toResult (Std.core.cmp.impls.OrdUsize.min x y) = .ok z ∧ z = Std.core.cmp.impls.OrdUsize.min x y := by
  simp [Std.core.cmp.impls.OrdUsize.min, Std.toResult]

attribute [simp] Id.run Id.pure_eq Id.bind_eq

attribute [simp_lists_simps] lt_inf_iff le_inf_iff true_and and_true not_lt not_le
attribute [simp_lists_simps] List.drop_eq_nil_of_le List.forIn_yield_eq_foldl List.foldl_nil
attribute [simp_lists_simps] List.drop_eq_getElem_cons List.getElem_finRange List.foldl_cons
attribute [simp_lists_simps] List.getElem?_set_eq

@[simp_lists_simps]   
theorem getElem!_zipWith[Inhabited α][Inhabited β](f: α → α → β)(xs ys: List α)
: ∀ i < xs.length.min ys.length,
  (xs.zipWith f ys)[i]! = f xs[i]! ys[i]!
:= by
  intro i i_idx
  cases xs <;> cases ys <;> cases i <;> simp at *
  apply getElem!_zipWith
  apply Nat.le_min.mpr
  assumption

attribute [scalar_tac_simps] Classical.not_and_iff_or_not_not
attribute [scalar_tac_simps] Fin.val_add Fin.val_mul 
attribute [scalar_tac_simps] List.length_finRange List.length_zipWith
attribute [scalar_tac_simps] lt_inf_iff le_inf_iff true_and and_true not_lt not_le
attribute [scalar_tac a.val] Fin.is_le'
attribute [scalar_tac self] Fin.isLt

@[scalar_tac_simps]
theorem Fin.val_ofNat{n: Nat}[NeZero n]{x: Nat}
: (ofNat(x): Fin n).val = x % n
:= by simp [OfNat.ofNat, Fin.instOfNat]

@[scalar_tac x % v]
theorem Nat.zero_mod_or_mod_lt(x v: Nat): v = 0 ∨ x % v < v := by
  match h: v with
  | 0 => left; rfl
  | v'+1 => 
    right
    apply Nat.mod_lt
    exact Nat.zero_lt_succ v'

attribute [scalar_tac_simps] Spec.w Spec.b

@[simp, scalar_tac_simps]
theorem simple.W.spec 
: simple.W = Spec.w 6
:= by native_decide

theorem Nat.lt_packing_right {x y: Nat}(x_lt: x < n)(y_lt: y < m)
: n*y + x < n*m
:= by
  have n_pos: n > 0 := by apply Nat.pos_of_ne_zero; intro h; simp [h] at x_lt
  have m_pos: m > 0 := by apply Nat.pos_of_ne_zero; intro h; simp [h] at y_lt
  calc n*y + x
    _ = n * y + x := rfl
    _ ≤ n * (m-1) + x := by
      apply Nat.add_le_add_right 
      apply Nat.mul_le_mul_left
      apply Nat.le_pred_iff_lt m_pos |>.mpr
      exact y_lt
    _ ≤ n * (m-1) + (n-1) := by
      apply Nat.add_le_add_left
      apply Nat.le_pred_iff_lt n_pos |>.mpr
      exact x_lt
    _ < n * m := by 
      simp [Nat.mul_sub, ←Nat.add_sub_assoc n_pos]
      have: n*m >= n := by 
        conv => arg 2; rw [←Nat.mul_one n]
        apply Nat.mul_le_mul (Nat.le_refl n) m_pos
      simp [Nat.sub_add_cancel this]
      exact And.intro n_pos m_pos


@[scalar_tac 5 * y + x]
theorem something_not_named_yet
: x ≥ 5 ∨ y ≥ 5 ∨ Spec.w 6 * (5 * y + x) ≤ Spec.w 6 * 24
:= by
  if x ≥ 5 then left; assumption
  else if y ≥ 5 then right; left; assumption
  else
    rename_i x_idx y_idx
    simp at x_idx y_idx
    right; right
    apply Nat.mul_le_mul_left (k := Spec.w 6)
    exact Nat.le_pred_of_lt (Nat.lt_packing_right x_idx y_idx)

theorem getElem_eq_getElem! [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
    [Inhabited elem] (c : cont) (i : idx) (h : dom c i) :
    c[i]'h = c[i]! := by
  have : Decidable (dom c i) := .isTrue h
  simp [getElem!_def, getElem?_def, h]

@[ext]
theorem Spec.Keccak.StateArray.ext{a b: StateArray l}
{point_eq: ∀ (x y: Fin 5)(z: Fin (w l)), a.get x y z = b.get x y z}
: a = b
:= by
  obtain ⟨a⟩ := a
  obtain ⟨b⟩ := b
  have bv_point_eq: ∀ (c: Fin (Spec.b l)), a[c] = b[c] := by 
    simp [get] at point_eq
    intro c
    have := point_eq (decodeIndex c).1 (decodeIndex c).2.1 (decodeIndex c).2.2
    simp [Spec.Keccak.StateArray.decode_encode c] at this
    assumption
  simp
  apply BitVec.ext (point_eq := fun i h => bv_point_eq ⟨i, h⟩)

@[simp]
theorem Spec.Keccak.StateArray.get_ofFn{f: Fin 5 × Fin 5 × Fin (w l) → Spec.Bit}(x y: Fin 5)(z: Fin (w l))
: (StateArray.ofFn f).get x y z = f (x,y,z)
:= by simp [ofFn, get, BitVec.ofFn, encode_decode]

theorem Bool.toNat_mod2_self(b: Bool)
: b.toNat % 2 = b.toNat
:= by cases b <;> simp

theorem Spec.Keccak.StateArray.get_set(a: Spec.Keccak.StateArray l)(x x' y y': Fin 5)(z z': Fin (w l))
: (a.set x' y' z' val).get x y z = if x = x' ∧ y = y' ∧ z = z' then val else a.get x y z
:= by
  simp [get, set, BitVec.getElem_set]
  split
  case isTrue h =>
    replace h := encode_inj x x' y y' z z' |>.mp <| Fin.eq_of_val_eq h.symm
    simp [h]
  case isFalse h =>
    have : ¬ (x = x' ∧ y = y' ∧ z = z') := by rintro ⟨rfl,rfl,rfl⟩; exact h rfl
    simp [this]

@[simp]
theorem Spec.Keccak.StateArray.get_set_eq(a: Spec.Keccak.StateArray l)(x y : Fin 5)(z : Fin (w l))
: (a.set x y z val).get x y z = val
:= by simp [get_set]

@[simp]
theorem Spec.Keccak.StateArray.get_set_neq(a: Spec.Keccak.StateArray l)(x x' y y': Fin 5)(z z': Fin (w l))
: (x,y,z) ≠ (x',y',z')
→ (a.set x' y' z' val).get x y z = a.get x y z
:= by 
  intros not_cond
  simp only [ne_eq, Prod.mk.injEq] at not_cond
  simp [not_cond, get_set]

/- @[scalar_tac x % n] -/
/- theorem tmp2(x n: Nat): x % n = x ∨ x ≥ n := by -/
/-   if h: x < n then -/
/-     left; exact Nat.mod_eq_of_lt ‹x < n› -/
/-   else -/
/-     right; simpa using h -/
    
attribute [scalar_tac_simps] Nat.mod_succ 
attribute [scalar_tac_simps] Nat.cast_add Nat.cast_mul Nat.cast_ofNat Nat.cast_inj Nat.cast_le Nat.cast_ite 

def Aeneas.Std.UScalar.ofNatCore' {ty : UScalarTy} (x : Nat) (h : x < 2^ty.numBits) : UScalar ty :=
  { bv := BitVec.ofFin ⟨x,h⟩ }
@[reducible] def Aeneas.Std.UScalar.ofNat' {ty : UScalarTy} (x : Nat)
  (hInBounds : x ≤ UScalar.cMax ty := by decide) : UScalar ty :=
  UScalar.ofNatCore' x (UScalar.bound_suffices ty x hInBounds)
macro:max x:term:max noWs "#usize'" : term => `(@Aeneas.Std.UScalar.ofNat' Aeneas.Std.UScalarTy.Usize $x (by first | decide | scalar_tac))

/- end Extras -/

open Aeneas hiding Std.Array
open Std.alloc.vec 
section Auxiliary/- {{{ -/

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
      if pos.val ≤ j ∧ j < pos.val + b.length then 
        output[j]! = (a[j]! ^^ b[j-pos.val]!)
      else 
        output[j]! = a[j]!
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


@[progress]
theorem simple.xor_long.spec(a b: Std.Slice Bool)
: ∃ c, 
  xor_long a b = .ok c ∧ c = a.val.zipWith xor b ++ a.val.drop b.length
:= by/- {{{ -/
  rw [xor_long]
  progress*

  apply List.ext_getElem!
  · simp [*]; scalar_tac

  intro i
  replace res_post_2 := res_post_2 i
  if i_idx: i < a.length.min (b.length) then
    simp_ifs at res_post_2
    replace res_post_2 := res_post_2 (by scalar_tac)
    simp [*, getElem!_zipWith]
    simpa using res_post_2
  else
    if i_a_idx: i < a.length then
      simp [*] at *
      simp [*] at *
      rw [res_post_2]
      congr
      scalar_tac
    else
      simp_lists

end Auxiliary/- }}} -/


@[simp] def Aeneas.Std.Array.toBitVec{size: Std.Usize}(self: Std.Array Bool size): BitVec (size.val) :=
  (BitVec.ofBoolListLE <| self.val).cast (by simp)

def simple.StateArray.toSpec(self: simple.StateArray): Spec.Keccak.StateArray 6 :=
  Spec.Keccak.StateArray.ofBitVec <| self.toBitVec.cast (by simp [Spec.w, Spec.b])

@[scalar_tac Std.Usize.max]
theorem Aeneas.Std.Usize.max_bound
: 2^32 - 1 <= Std.Usize.max
:= by
  rw [Std.Usize.max_def, Std.Usize.numBits, Std.UScalarTy.numBits]
  cases System.Platform.numBits_eq <;> simp [*]

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

theorem Bool.xor_eq_ne(a b: Bool): (a ^^ b) = (a != b) := by cases a <;> cases b <;> decide

@[progress]
theorem simple.theta.theta_c.spec(input : simple.StateArray)(x z: Std.Usize)
(x_idx: x.val < 5)
(z_idx: z.val < Spec.w 6)
: ∃ output, theta.c input x z = .ok output ∧ output = Spec.Keccak.θ.C input.toSpec x z
:= by rw [theta.c]; progress*; simp [*, Spec.Keccak.θ.C]

@[progress]
theorem simple.theta.theta_d.spec(input : simple.StateArray)(x z: Std.Usize)
(x_idx: x.val < 5)
(z_idx: z.val < Spec.w 6)
: ∃ output, theta.d input x z = .ok output ∧ output = Spec.Keccak.θ.D input.toSpec x z
:= by
  rw [theta.d]
  progress*
  simp [*, Spec.Keccak.θ.D]
  congr 2
  · apply Fin.eq_of_val_eq
    simp [Fin.sub_def, Nat.add_comm]
  · apply Fin.eq_of_val_eq
    simp [Fin.add_def]
  · apply Fin.eq_of_val_eq
    simp [Fin.sub_def, ←i2_post, W.spec]
    have: i2.val = W.val - 1 := by scalar_tac
    simp [this, W.spec, Nat.add_comm]

theorem Fin.cast_of_mk{n: Nat}{x: Nat}(x_lt: x < n)
: Fin.mk x x_lt = @Nat.cast (Fin n) (@Fin.instNatCast n ⟨Nat.not_eq_zero_of_lt x_lt⟩) x := by
    simp only [Nat.cast, NatCast.natCast, Fin.instNatCast, Fin.ofNat', Nat.mod_eq_of_lt x_lt]

@[progress]
theorem simple.theta.inner.inner_loop.spec(input a: simple.StateArray)(x y z: Std.Usize)
(x_idx: x.val < 5)
(y_idx: y.val < 5)
(z_loop_bnd: z.val <= Spec.w 6)
: ∃ output, theta.inner.inner_loop input a x y z = .ok output ∧ 
  ∀ (x' y': Fin 5)(z': Fin (Spec.w 6)),
  output.toSpec.get x' y' z' = 
    if x = x' ∧ y = y' ∧ z.val ≤ z'.val then 
        a.toSpec.get x y z'  ^^ Spec.Keccak.θ.D a.toSpec x z'
      else input.toSpec.get x' y' z'
:= by
  rw [theta.inner.inner_loop]
  split
  case isTrue z_idx =>
    simp [W.spec] at z_idx
    let* ⟨ acc_elem, acc_elem_post ⟩ ← simple.StateArray.index.spec
    let* ⟨ aux, aux_post ⟩ ← simple.theta.theta_d.spec
    let* ⟨ res_elem, res_elem_post ⟩ ← simple.binxor.spec
    let* ⟨ old_val, mk_new, old_val.post, mk_new.post ⟩ ← simple.StateArray.index_mut.spec
    let* ⟨ z_succ, z_succ_post ⟩ ← Aeneas.Std.Usize.add_spec
    let* ⟨ res, res_post ⟩ ← spec
    /- simp only [z_succ_post] at *; clear z_succ_post -/

    /- have norm{n: Nat}{x: Std.Usize}(x_lt: x.val < n)[NeZero n]: x.val.cast = Fin.mk x.val x_lt := by -/
    /-   simp only [Nat.cast, NatCast.natCast, Fin.instNatCast, Fin.ofNat', Nat.mod_eq_of_lt x_lt] -/

    intro x' y' j
    simp [*] at res_post
    rw [res_post]; clear res_post
    /- replace res_post := res_post x' y' j -/
    split_all
    · rfl
    · scalar_tac
    · have: j = z.val.cast := by
        have: j = j.val.cast := by simp
        rw [this]
        rw [‹j.val = z.val›']
      simp [this, *]
    · simp_ifs [Spec.Keccak.StateArray.get_set]
      have: ¬ (x' = x.val.cast ∧ y' = y.val.cast ∧ j = z.val.cast) := by
        simp; intros
        simp [*] at *
        have: j = j.val.cast := by simp
        rintro rfl
        simp at *
        scalar_tac
      simp [this]
  case isFalse z_end =>
    have: z = Spec.w 6 := by simp [W.spec] at z_end; scalar_tac
    simp [this]
    intro x y z'
    simp [Nat.not_le_of_gt z'.isLt]
termination_by (Spec.w 6) - z.val
decreasing_by scalar_decr_tac


@[progress]
theorem simple.theta.inner_loop.spec(input a: simple.StateArray)(x y: Std.Usize)
(x_idx: x.val < 5)
(y_loop_bnd: y.val <= 5)
: ∃ output, theta.inner_loop input a x y = .ok output ∧
  ∀ (x' y': Fin 5)(z': Fin (Spec.w 6)),
  output.toSpec.get x' y' z' = 
    if x = x' ∧ y.val ≤ y'.val then
      a.toSpec.get x y' z'  ^^ Spec.Keccak.θ.D a.toSpec x z'
    else input.toSpec.get x' y' z'
:= by 
  rw [inner_loop, inner.inner]
  split
  case isTrue y_idx =>
    let* ⟨ res_z, res_z_post ⟩ ← simple.theta.inner.inner_loop.spec
    let* ⟨ y_succ, y_succ_post ⟩ ← Aeneas.Std.Usize.add_spec
    let* ⟨ res, res_post ⟩ ← spec  -- (y := y_succ) -- ← I do this instead of `· exact a`

    intro x' y' z'
    simp [res_post, y_succ_post, res_z_post]

    if h: x = x' ∧ y.val ≤ y'.val then
      obtain ⟨rfl,y'_range?⟩ := h
      simp [y'_range?]
      intro j_upper_bnd
      have y_y' : y.val = y'.val := by scalar_tac
      simp [y_y']
    else
      rw [not_and_or] at h
      obtain h | j_range? := h
      · simp [h, res_z_post]

      have: ¬ y.val + 1 <= y'.val := by scalar_tac
      simp [j_range?, this]
      rintro rfl rfl
      scalar_tac
  case isFalse y_oob =>
    simp
    have: y.val = 5 := by scalar_tac
    simp [this]
    intro x' y' z'
    simp [Nat.not_le_of_gt y'.isLt]
termination_by (5 +1) - y.val
decreasing_by 
  
  scalar_decr_tac

@[progress]
theorem simple.theta_loop.spec(input a: simple.StateArray)(x: Std.Usize)
(x_loop_bnd: x.val <= 5)
: ∃ output, theta_loop a input x = .ok output ∧ 
  ∀ (x' y': Fin 5)(z': Fin (Spec.w 6)),
    output.toSpec.get x' y' z' = 
      if x.val ≤ x'.val then 
        a.toSpec.get x' y' z'  ^^ Spec.Keccak.θ.D a.toSpec x' z'
      else 
        input.toSpec.get x' y' z'
:= by
  rw [theta_loop, theta.inner]
  split
  case isTrue x_idx =>
    let* ⟨ res_y, res_y_post ⟩ ← simple.theta.inner_loop.spec
    let* ⟨ x_succ, x_succ_post ⟩ ← Aeneas.Std.Usize.add_spec
    let* ⟨ res, res_post ⟩ ← spec
    intro x' y' z'
    simp [res_post, res_y_post, x_succ_post]
    if h: x.val <= x'.val then
      simp [h]; intro _
      have x_x' : x.val = x'.val := by scalar_tac
      simp [x_x']
    else
      have: ¬ x.val + 1 <= x'.val := by scalar_tac
      simp [h, this]; rintro rfl
      scalar_tac
  case isFalse x_oob =>
    have : x.val = 5 := by scalar_tac
    simp [this]
    intro x' y' z'
    simp [Nat.not_le_of_gt x'.isLt]
termination_by 5+1 - x.val
decreasing_by scalar_decr_tac

@[progress]
theorem simple.theta.spec(input: simple.StateArray)
: ∃ output, theta input = .ok output ∧ output.toSpec = Spec.Keccak.θ input.toSpec
:= by 
  rw [theta, Spec.Keccak.θ, DefaultsimpleStateArray.default]
  let* ⟨ res, res_post ⟩ ← simple.theta_loop.spec
  ext x y z
  simp [res_post x y z, Spec.Keccak.StateArray.get_ofFn]

def Spec.Keccak.ρ.sequence_point(n: Nat): Fin 5 × Fin 5 := n.repeat (fun (x,y) => (y, 2 * x + 3 * y)) (1, 0)

def Spec.Keccak.ρ.sequence := Vector.range 24 |>.map sequence_point


@[progress]
theorem simple.rho_offset.spec (t : Std.Usize)
: t.val < 24
→ ∃ output,
  rho_offset t = .ok output ∧
  output.val = (@Spec.Keccak.ρ.offset 6 t.val).val
:= by
  intro bounded
  unfold rho_offset Spec.Keccak.ρ.offset
  progress* by scalar_tac
  · calc i.val * i1.val
    _ ≤ 200 * i1.val := by
      apply Nat.mul_le_mul_right
      scalar_tac
    _ ≤ 200 * 200 := by
      apply Nat.mul_le_mul_left
      scalar_tac
    _ ≤ Std.Usize.max := by scalar_tac
  scalar_tac

def Spec.Keccak.ρ.inner_loop(input res: Spec.Keccak.StateArray 6)(t: Fin 24)(x y: Fin 5)(z: Nat) := Id.run do
    let mut res' := res
    for z in List.finRange (Spec.w 6) |>.drop z do
      res' := res'.set x y z.val <| input.get x y (z - Spec.Keccak.ρ.offset t)
    return res'

def Spec.Keccak.ρ.loop(input res: Spec.Keccak.StateArray 6)(t : Nat)(x y: Fin 5) := Id.run do
    let mut (x',y') := (x,y)
    let mut res' := res
    for t in List.finRange 24 |>.drop t do
      res' := ρ.inner_loop input res' t x' y' 0
      (x',y') := (y', 2*x' + 3*y')
    return res'

theorem Spec.Keccak.ρ.loop.spec(input: Spec.Keccak.StateArray 6)
: ρ.loop input input 0 1 0 = ρ input
:= by simp [ρ,ρ.loop, ρ.inner_loop]

@[progress]
theorem simple.rho.inner_loop.spec(input res : StateArray) (t x y z : Std.Usize)
: t.val < 24
→ x.val < 5
→ y.val < 5
→ z.val ≤ Spec.w 6
→ ∃ output,
  rho.inner_loop res input t x y z = .ok output ∧ 
  output.toSpec = Spec.Keccak.ρ.inner_loop input.toSpec res.toSpec t.val.cast x.val.cast y.val.cast z.val.cast
:= by 
  intro t_lt x_lt y_lt z_lt
  rw [rho.inner_loop, Spec.Keccak.ρ.inner_loop]
  split
  . let* ⟨ i, i_post ⟩ ← rho_offset.spec
    let* ⟨ i1, i1_post ⟩ ← Std.Usize.sub_spec
    let* ⟨ i2, i2_post ⟩ ← Std.Usize.add_spec
    let* ⟨ z2, z2_post ⟩ ← Std.Usize.rem_spec
    let* ⟨ b, b_post ⟩ ← StateArray.index.spec
    let* ⟨ x_1, x_2, x_post_1, x_post_2 ⟩ ← StateArray.index_mut.spec
    let* ⟨ z1, z1_post ⟩ ← Std.Usize.add_spec
    let* ⟨ res, res_post ⟩ ← spec
    simp [*, Spec.Keccak.ρ.inner_loop]
    simp_lists
    rw [Fin.cast_of_mk ‹z.val < Spec.w 6›']
    congr 3
    apply Fin.eq_of_val_eq
    simp [*]
    have i1_val: i1.val = W - (@Spec.Keccak.ρ.offset 6 t).val := by scalar_tac
    simp [i1_val, Nat.mod_eq_of_lt t_lt, Fin.sub_def]
    have: W.val >= @Spec.Keccak.ρ.offset 6 t.val := by scalar_tac
    simp [Spec.Keccak.ρ.offset, W.spec]
    simp [Nat.add_comm]
  case isFalse =>
    simp [‹z.val = Spec.w 6›']
    simp_lists 
termination_by Spec.w 6 - z.val
decreasing_by scalar_decr_tac

@[progress]
theorem simple.rho_loop.spec(input: simple.StateArray)
(x y : Std.Usize) (res: simple.StateArray) (t: Std.Usize)
: t.val <= 24
→ x.val < 5
→ y.val < 5
→ ∃ output,
  rho_loop input x y res t = .ok output ∧ 
  output.toSpec = Spec.Keccak.ρ.loop input.toSpec res.toSpec t.val.cast x.val.cast y.val.cast
:= by 
  intro t_loop_bnd x_idx y_idx
  rw [rho_loop]
  split
  case isTrue t_lt =>
    let* ⟨ res1, res1_post ⟩ ← rho.inner_loop.spec
    let* ⟨ i, i_post ⟩ ← Std.Usize.mul_spec
    let* ⟨ i1, i1_post ⟩ ← Std.Usize.mul_spec
    let* ⟨ i2, i2_post ⟩ ← Std.Usize.add_spec
    let* ⟨ lhs, lhs_post ⟩ ← Std.Usize.rem_spec
    let* ⟨ t1, t1_post ⟩ ← Std.Usize.add_spec
    let* ⟨ rest, rest_post ⟩ ← spec input
    simp [*, Spec.Keccak.ρ.loop]
    simp_lists
    congr 4
    · simp [Fin.val_eq_of_eq, Fin.cast_of_mk]
    · apply Fin.eq_of_val_eq
      scalar_tac
  case isFalse => 
    simp [‹t.val = 24›', Spec.Keccak.ρ.loop]
termination_by 24 - t.val
decreasing_by scalar_decr_tac

@[progress]
theorem simple.rho.spec(input: simple.StateArray)
: ∃ output,
  simple.rho input = .ok output ∧ output.toSpec = Spec.Keccak.ρ input.toSpec
:= by 
  /- rw [Spec.Keccak.ρ.loop] -/
  simp [rho, ClonesimpleStateArray.clone]
  progress as ⟨res, res_post⟩
  simp [res_post, Spec.Keccak.ρ.loop.spec]

#print Spec.Keccak.π
#print simple.pi_loop
#print simple.pi.inner_loop
#print simple.pi.inner.inner_loop

@[progress]
theorem simple.pi.inner.inner_loop.spec(res input : simple.StateArray) (x y z : Std.Usize)
: x.val < 5
→ y.val < 5
→ z.val <= Spec.w 6
→ ∃ output,
  inner_loop res input x y z = .ok output ∧
  ∀ (x' y': Fin 5)(z': Fin (Spec.w 6)),
    output.toSpec.get x' y' z' = 
      if x.val = x' ∧ y.val = y' ∧ z.val ≤ z'.val then
        input.toSpec.get (x + 3*y) x z'
      else
        res.toSpec.get x' y' z'
:= by
  intro x_idx y_idx z_loop_bnd
  rw [inner_loop]
  split
  . let* ⟨ i, i_post ⟩ ← Std.Usize.mul_spec
    let* ⟨ i1, i1_post ⟩ ← Std.Usize.add_spec
    let* ⟨ x2, x2_post ⟩ ← Std.Usize.rem_spec
    let* ⟨ b, b_post ⟩ ← StateArray.index.spec
    let* ⟨ x_1, x_2, x_post_1, x_post_2 ⟩ ← StateArray.index_mut.spec
    let* ⟨ z1, z1_post ⟩ ← Std.Usize.add_spec
    let* ⟨ rest, rest_post ⟩ ← spec
    intro x' y' z'
    rw [rest_post]
    simp [*]
    split_all
    · rfl
    · scalar_tac
    · simp [*, ‹z.val = z'.val›']
      congr 1
      apply Fin.eq_of_val_eq
      scalar_tac
    · rw [Spec.Keccak.StateArray.get_set_neq]
      simp
      intro xx' yy' zz'
      scalar_tac
  case isFalse z_oob =>
    simp; intros; simp_ifs
termination_by Spec.w 6 - z.val
decreasing_by scalar_decr_tac
      
@[progress]
theorem simple.pi.inner_loop.spec(input res : simple.StateArray) (x y: Std.Usize)
: x.val < 5
→ y.val <= 5
→ ∃ output,
  inner_loop res input x y = .ok output ∧
  ∀ (x' y': Fin 5)(z': Fin (Spec.w 6)),
    output.toSpec.get x' y' z' = 
      if x.val = x' ∧ y.val ≤ y' then
        input.toSpec.get (x' + 3*y') x' z'
      else
        res.toSpec.get x' y' z'
:= by
  intro x_lt y_loop_bnd
  rw [inner_loop]
  split
  . let* ⟨ res1, res1_post ⟩ ← inner.inner_loop.spec
    let* ⟨ y1, y1_post ⟩ ← Std.Usize.add_spec
    let* ⟨ rest, rest_post ⟩ ← spec
    simp [y1_post, rest_post]
    intro x' y' z'
    split_all
    · rfl
    · scalar_tac
    · simp [‹y.val = y'.val›', *]
    · simp [*]
      intro xx' yy'
      scalar_tac
  . simp
    simp_ifs [implies_true]
termination_by 5 - y.val
decreasing_by scalar_decr_tac

@[progress]
theorem simple.pi_loop.spec(input res : simple.StateArray) (x : Std.Usize)
: ∃ output,
  simple.pi_loop input res x = .ok output ∧
  ∀ (x' y': Fin 5)(z': Fin (Spec.w 6)),
    output.toSpec.get x' y' z' = 
      if x.val ≤ x' then
        input.toSpec.get (x' + 3*y') x' z'
      else
        res.toSpec.get x' y' z'
:= by
  rw [pi_loop]
  progress*
  · intro x' y' z'
    simp [res_post]
    split_all
    · rfl
    · scalar_tac
    · simp [‹x.val = x'.val›', *]
    · simp [*]; intro; scalar_tac
  · simp
    simp_ifs
    simp only [implies_true]
termination_by 5 - x.val
decreasing_by scalar_decr_tac

@[progress]
theorem simple.pi.spec(input: simple.StateArray)
: ∃ output,
  pi input = .ok output ∧
  output.toSpec = Spec.Keccak.π input.toSpec
:= by
  simp [pi, Spec.Keccak.π, ClonesimpleStateArray.clone]
  let* ⟨ res, res_post ⟩ ← pi_loop.spec
  ext x' y' z'
  simp [res_post]

theorem simple.IOTA_RC_POINTS.spec
: ∀ t < 255, IOTA_RC_POINTS.val[t]! = Spec.Keccak.ι.rc t
:= by native_decide

attribute [scalar_tac_simps] Nat.mod_mod Fin.ofNat'

@[progress]
theorem simple.iota_rc_point.spec(t: Std.Usize)
: ∃ output, 
  iota_rc_point t = .ok output ∧
  output = Spec.Keccak.ι.rc t.val
:= by
  simp [iota_rc_point]
  progress*
  simp [*, IOTA_RC_POINTS.spec (t.val % 255) (by scalar_tac)]
  rw [
    Spec.Keccak.ι.rc,
    ‹Fin.ofNat' 255 (↑t % 255) = Fin.ofNat' 255 ↑t›',
    ←Spec.Keccak.ι.rc
  ]

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
:= UScalar.one_ShiftLeft_spec _ _ hy

/- @[scalar_tac 2 ^ n] -/ 
/- theorem Nat.one_lt_two_pow''(n: Nat): 1 ≤ 2^n := @Nat.one_le_two_pow n -/
attribute [scalar_tac_simps] Nat.one_le_two_pow

@[simp, scalar_tac_simps] theorem simple.L.spec : L.val = 6 := by native_decide

def simple.iota_rc_init_loop.ref(ir: Nat)(rc: BitVec (Spec.w 6))(j: Nat) := 
  if j <= 6
  then
    let i := 7 * ir
    let i1 := j + i
    let b := Spec.Keccak.ι.rc i1
    let i2 := 1 <<< j
    let i3 := i2 - 1
    let rc1 := rc.set i3 b
    let j1 := j + 1
    iota_rc_init_loop.ref ir rc1 j1
  else rc
termination_by 7 - j

@[scalar_tac Std.UScalarTy.Usize.numBits]
theorem Std.UScalarTy.Usize_numBits_le: Std.UScalarTy.Usize.numBits ≥ 32 := by
  rcases System.Platform.numBits_eq with h | h <;> simp [h]

theorem Aeneas.Std.Array.toBitVec_set{size: Std.Usize}(arr: Std.Array Bool size)(i: Std.Usize)(b: Bool)
(i_idx: i < arr.length)
: (arr.set i b).toBitVec = arr.toBitVec.set ⟨i.val, by simpa using i_idx⟩ b
:= by 
  simp [toBitVec]
  rw [←BitVec.cast_set (i_idx := i_idx)]
  ext j j_idx
  simp only [BitVec.getElem_cast]
  simp
  simp at j_idx
  have: size.val > 0 := by scalar_tac -- cases h: size.val <;> simp [h] at *
  if h: i = j then
    simp [h, BitVec.getElem_set]
  else
    simp [h, BitVec.getElem_set]

theorem simple.iota_rc_init_loop.ref_spec(ir : Std.Usize) (input : Aeneas.Std.Array Bool 64#usize)(j: Std.Usize)
: ir.val < 24
→ j.val ≤ 6 + 1
→ ∃ output,
  iota_rc_init_loop ir input j = .ok output ∧
  output.toBitVec.cast (by simp [Spec.w]) = simple.iota_rc_init_loop.ref ir.val (input.toBitVec.cast (by simp [Spec.w])) j.val
:= by
  intro ir_lt j_loop_bound
  rw [iota_rc_init_loop, iota_rc_init_loop.ref]
  split
  case isTrue j_lt =>
    let* ⟨ i, i_post ⟩ ← Std.Usize.mul_spec
    let* ⟨ i1, i1_post ⟩ ← Std.Usize.add_spec
    let* ⟨ b, b_post ⟩ ← iota_rc_point.spec
    simp [i1_post, i_post] at b_post
    let* ⟨ i2, i2_post_1, i2_post_2 ⟩ ← Std.Usize.one_ShiftLeft_spec
    let* ⟨ i3, i3_post ⟩ ← Std.Usize.sub_spec
    have i3_val: i3.val = i2.val - 1 := by 
      rw [i3_post, Nat.add_sub_cancel]
    simp [i2_post_1] at i3_val
    have i3_idx: i3.val < input.length := by 
      simp [*]
      calc  2 ^ ↑j - 1
          _ < 2 ^ ↑j := Nat.pred_lt (Nat.ne_of_gt (Nat.two_pow_pos j.val))
          _ ≤ 2 ^ 6 := Nat.pow_le_pow_right Nat.two_pos (by simpa using j_lt)
    let* ⟨ rc1, rc1_post ⟩ ← Std.Array.update_spec
    let* ⟨ j1, j1_post ⟩ ← Std.Usize.add_spec
    let* ⟨ res, res_post ⟩ ← ref_spec
    -- END PROGRESS
    rw [res_post, ←BitVec.cast_set (i_idx := ?first)]
    rw [rc1_post, Std.Array.toBitVec_set (i_idx := by assumption)]
    case first =>
      simp [Nat.shiftLeft_eq, NatCast.natCast, Fin.ofNat']
      rw [Nat.mod_eq_of_lt] <;> simpa [i3_val] using i3_idx
    simp_ifs
    congr 3
    simp [i3_val]
    rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.mod_eq_of_lt]
    simpa [i3_val] using i3_idx
  case isFalse => simp [‹j.val = 7›']
termination_by 7 - j.val
decreasing_by scalar_decr_tac

theorem simple.iota_rc_init_loop.ref.foldWhile_spec(iᵣ: Nat)(input: BitVec (Spec.w 6))(j: Nat)
: iota_rc_init_loop.ref iᵣ input j = SRRange.foldWhile 
    (i    := j) 
    (max  := 6 + 1) 
    (step := 1) (hStep := Nat.one_pos) 
    (init := input) 
    (f    := fun input j => input.set (↑(1 <<< j - 1)) (Spec.Keccak.ι.rc (j + 7 * iᵣ)))
:= by
  rw [ref, SRRange.foldWhile]
  if h: j < 7 then
    simp only
    simp [h, ‹j ≤ 6›']
    rw [simple.iota_rc_init_loop.ref.foldWhile_spec]
  else simp [h, ‹¬ (j ≤ 6)›']

def Spec.Keccak.ι.RC.loop (iᵣ: Nat)(init: BitVec (w 6))(start: Nat): BitVec (w 6) := Id.run do
  let mut RC := init
  for j in List.finRange (6 + 1) |>.drop start do
    have j_valid_idx := calc  2 ^ ↑j - 1
        _ < 2 ^ ↑j := Nat.pred_lt (Nat.ne_of_gt (Nat.two_pow_pos j.val))
        _ ≤ 2 ^ 6 := Nat.pow_le_pow_right Nat.two_pos <| Fin.is_le j
    RC := RC.set ⟨2^j.val - 1, j_valid_idx⟩ (ι.rc (↑j + 7*iᵣ)) 
  return RC

def BitVec.set!{n: Nat}(i: Nat)(b: Bool)(bv: BitVec n): BitVec n := 
  if _: i < n then
    bv.set ⟨i, ‹i < n›⟩ b
  else bv

theorem BitVec.set!_eq_set{n: Nat}(i: Nat)(b: Bool)(bv: BitVec n)⦃i_idx: i < n⦄
: bv.set! i b = bv.set ⟨i, i_idx⟩ b
:= by simp only [set!, reduceDIte, i_idx]

theorem List.foldl_of_foldl_map(f: α' → α)(upd: β → α → β)(upd' : β → α' → β)(init: β)(ls: List α')
: upd' = (upd · <| f ·)
→ List.foldl upd' init ls = List.foldl upd init (ls.map f) 
:= by rintro rfl; revert init; induction ls <;> simp [*]

theorem List.val_finRange_eq_range(n: Nat)
: (List.finRange n).map Fin.val = List.range n
:= by cases n <;> simp

def Spec.Keccak.ι.RC.loop.spec(iᵣ: Nat)
: RC.loop iᵣ (0#(w 6)) 0 = RC iᵣ
:= by simp [loop, RC]; congr

def Spec.Keccak.ι.RC.loop.foldl_spec(iᵣ: Nat)(init: BitVec (w 6))(start: Nat)
: RC.loop iᵣ init start =
    List.foldl (fun RC j => RC.set! (2^j - 1) (ι.rc (j + 7*iᵣ))) init (List.range (6 + 1) |>.drop start)
:= by
  simp [RC.loop]
  rw [
    ←List.val_finRange_eq_range 7,
    ←List.map_drop,
    ←List.foldl_of_foldl_map (f := Fin.val)
  ]
  ext RC j : 2
  rw [BitVec.set!_eq_set]

theorem List.drop_range'(i s n: Nat): (List.range' s n |>.drop i) = List.range' (s + i) (n - i) := by
  cases i 
  case zero => simp
  case succ i' => 
    cases n
    case zero => simp
    case succ n' => 
      rw [List.range'_succ, List.drop_succ_cons, Nat.add_comm i', ←Nat.add_assoc, Nat.sub_add_eq, Nat.add_sub_cancel]
      apply List.drop_range'

theorem List.drop_range(i n: Nat): (List.range n |>.drop i) = List.range' i (n-i) := by
  simp [List.range_eq_range', List.drop_range' (s := 0)]

theorem Aeneas.SRRange.foldWhile_eq_foldWhile'{α : Type u} 
(i max step : Nat) (hStep : 0 < step) (f : α → Nat → α) (init : α)
: foldWhile max step hStep f i init = SRRange.foldWhile' {
    start := i
    stop  := max
    step  := step
    step_pos := hStep
  } (fun acc e _ => f acc e) i init (hi := by simp)
:= by
  sorry


def simple.iota_rc_init_loop.foldWhile.spec(iᵣ: Nat)(init: BitVec (Spec.w 6))(start: Nat)
: SRRange.foldWhile 
    (i    := start) 
    (max  := 6 + 1) 
    (step := 1) (hStep := Nat.one_pos) 
    (init := init) 
    (f    := fun input j => BitVec.set (1 <<< j - 1).cast (Spec.Keccak.ι.rc (j + 7 * iᵣ)) input)
= Spec.Keccak.ι.RC.loop iᵣ init start
:= by
  rw [Spec.Keccak.ι.RC.loop.foldl_spec, List.drop_range, SRRange.foldl_range' (hStep := Nat.one_pos)]
  simp
  if start_idx: start < 7 then
    rw [‹start  + (7 - start) = 7›']
    rw [SRRange.foldWhile_eq_foldWhile', SRRange.foldWhile_eq_foldWhile']
    congr
    ext input j j_idx : 3
    rw [←BitVec.set!_eq_set]
    congr 2
    simp
    simp only [Nat.shiftLeft_eq, Nat.one_mul]
    simp [Membership.mem] at j_idx
    have j_valid_idx := calc  2 ^ j - 1
        _ < 2 ^ j := Nat.pred_lt (Nat.ne_of_gt (Nat.two_pow_pos j))
        _ ≤ 2 ^ 6 := Nat.pow_le_pow_right Nat.two_pos (by scalar_tac)
    rw [Nat.mod_eq_of_lt]; simpa using j_valid_idx
  else
    rw [SRRange.foldWhile_id (h := start_idx), SRRange.foldWhile_id (h := by simpa using start_idx)]

@[progress]
theorem simple.iota_rc_init_loop.spec(ir : Std.Usize) (input : Aeneas.Std.Array Bool 64#usize)(i: Std.Usize)
: ir.val < 24
→ i.val ≤ 6 + 1
→ ∃ output,
  simple.iota_rc_init_loop ir input i = .ok output ∧
  output.toBitVec.cast (by simp [Spec.w]) = Spec.Keccak.ι.RC.loop ir.val (input.toBitVec.cast (by simp [Spec.w])) i.val
:= by
  intro ir_lt i_loop_bound
  let* ⟨ output, output_post⟩ ← iota_rc_init_loop.ref_spec
  rw [
    output_post,
    simple.iota_rc_init_loop.ref.foldWhile_spec,
    simple.iota_rc_init_loop.foldWhile.spec,
  ]

theorem repeat_false_toBitVec_eq_zero(size: Std.Usize)
: (Std.Array.repeat size false).toBitVec = 0#(size.val)
:= by ext i; simp only [Std.Array.toBitVec, Std.Array.repeat, BitVec.getElem_cast,
  BitVec.getElem_ofBoolListLE, List.getElem_replicate, BitVec.getElem_zero]

@[progress]
theorem simple.iota_rc_init.spec(ir: Std.Usize)
: ir.val < 24
→ ∃ output,
  simple.iota_rc_init ir (Std.Array.repeat 64#usize false) = .ok output ∧
  output.toBitVec.cast (by simp [Spec.w]) = (Spec.Keccak.ι.RC ir.val : BitVec (Spec.w 6))
:= by 
  intro ir_lt
  simp [iota_rc_init, -Std.Array.toBitVec]
  let* ⟨output , output_post⟩ ← iota_rc_init_loop.spec
  rw [output_post, ←Spec.Keccak.ι.RC.loop.spec]
  congr
  ext i i_idx
  simp only [Std.Array.toBitVec, Std.Array.repeat, BitVec.getElem_cast,
    BitVec.getElem_ofBoolListLE, List.getElem_replicate, BitVec.getElem_zero]

@[scalar_tac (x.cast : Fin n)]
theorem asfd(x: Nat){n: Nat}[NeZero n]
: (x.cast : Fin n).val = x ∨ x ≥ n
:= by 
  simp
  if x < n then
    left; rw [Nat.mod_eq_of_lt]; assumption
  else
    right; simpa using ‹¬ x < n›

@[progress]
theorem simple.iota_a_loop.spec(res : StateArray) (a : StateArray) (rc : Aeneas.Std.Array Bool 64#usize)(z: Std.Usize) 
: ∃ output,
  simple.iota_a_loop res a rc z = .ok output ∧
  ∀ (x y: Fin 5)(z': Fin (Spec.w 6)),
  output.toSpec.get x y z' = 
    if x = 0 ∧ y = 0 ∧ z.val ≤ z'.val then
      a.toSpec.get 0 0 z' ^^ rc.toBitVec[z'.val]!
    else
      res.toSpec.get x y z'
:= by
  rw [simple.iota_a_loop]
  split
  case isTrue =>
    let* ⟨ b, b_post ⟩ ← StateArray.index.spec
    let* ⟨ b1, b1_post ⟩ ← Std.Array.index_usize_spec
    let* ⟨ b2, b2_post ⟩ ← binxor.spec
    simp [b_post, b1_post] at b2_post
    let* ⟨ old_res, set_res, old_res_post, set_res_post ⟩ ← StateArray.index_mut.spec
    let* ⟨ z1, z1_post ⟩ ← Std.Usize.add_spec
    let* ⟨ rest, rest_post ⟩ ← spec
    simp [*] at rest_post
    intro x y z'
    rw [rest_post]
    split_all
    · simp [Spec.Keccak.StateArray.get_set]
    · scalar_tac
    · simp [Spec.Keccak.StateArray.get_set, -Std.Array.toBitVec]
      have zz' := ‹z.val = z'.val›'
      simp [zz', -Std.Array.toBitVec]
      simp_ifs
      rw [getElem!_pos (h := by scalar_tac)]
      rw [getElem!_pos (h := by scalar_tac)]
      simp [BitVec.getElem_ofBoolListLE]
    · rw [Spec.Keccak.StateArray.get_set]
      have: ¬ (x = 0 ∧ y = 0 ∧ z' = z.val.cast) := by 
        -- TODO: Could we modify `scalar_tac` so that it handles this case?
        -- The issue is with `Fin` inequalities being hiden behind `And`, `Or` or `Not`.
        -- It would be nice to have `scalar_tac` transform these using the lemmas
        --  · Fin.val_fin_le
        --  · Fin.val_inj
        -- I was thinking of using a `simproc`, but I don't think these work with
        -- implications, since they're supposed to do rewritings.
        -- Perhaps I could have it 
        rename_i h1 h2
        simp [not_and_or, -not_and] at h1 h2 ⊢
        rcases h1 with (h1 | h1 | h1) <;> try (simp [h1]; done)
        rcases h2 with (h1 | h1 | h1) <;> try (simp [h1]; done)
        right;right
        intro
        scalar_tac
      simp_ifs
  case isFalse z_oob =>
    simp at z_oob ⊢
    intro x y z'
    simp_ifs

@[progress]
theorem simple.iota.spec(ir: Std.Usize)(input: StateArray)
: ir.val < 24
→ ∃ output,
  iota ir input = .ok output ∧
  output.toSpec = Spec.Keccak.ι (iᵣ:= ir.val) input.toSpec
:= by
  intro ir_lt
  simp [iota, iota_a, ClonesimpleStateArray.clone]
  let* ⟨rc, rc_post⟩ ← iota_rc_init.spec
  let* ⟨res, res_post⟩ ← iota_a_loop.spec
  ext x y z
  simp only [Spec.Keccak.ι, Spec.Keccak.StateArray.get_ofFn, res_post]
  split
  case isTrue h =>
    simp only [Fin.isValue, h, id_eq, Id.run, Fin.getElem_fin, Id.pure_eq, Spec.Keccak.StateArray.get_ofFn, Bool.bne_right_inj]
    replace rc_post := BitVec.cast_left _ rc_post
    rw [rc_post, ←getElem_eq_getElem! (h := by scalar_tac)]
    simp
  case isFalse h =>
    simp
    split
    · simp [*] at *
      simp [*] at *
    rename_i h; simp at h; obtain ⟨rfl, rfl, rfl⟩ := h
    rfl

theorem Array.getElem?_chunks_exact(k: Nat)(arr: Array α)(i: Nat)
: i < arr.size / k
→ Vector.toArray <$> (arr.chunks_exact k)[i]? = some (arr.extract (k*i) (k*(i+1)))
:= by 
  sorry

@[progress]
private theorem auxiliary.Slice.index(start stop: Std.Usize)(arr: Std.Slice α)(k i: Nat)
: start.val = k * i
→ stop.val = k * (i + 1)
→ i < arr.length / k
→ k > 0
→ ∃ output,
  Std.core.slice.index.SliceIndexRangeUsizeSlice.index {start, end_ := stop} arr = .ok output ∧
  output.val = arr.val.slice start.val stop.val
:= by
  intro start_def stop_def i_bnd k_pos
  simp [Std.core.slice.index.SliceIndexRangeUsizeSlice.index]

  have start_lt_stop: start.val < stop.val := by simp [start_def, stop_def, Nat.mul_lt_mul_left k_pos |>.mpr]
  have stop_le_len: stop.val ≤ arr.length := 
    calc stop.val
      _ = k * (i + 1) := stop_def
      _ ≤ k * (arr.length / k) := Nat.mul_le_mul_left k i_bnd
      _ ≤ arr.length := Nat.mul_div_le arr.length k
  
  simp [le_of_lt start_lt_stop, stop_le_len]

/- @[progress] -/
theorem simple.sponge_absorb_loop.spec
  (bs : Std.Slice Bool) (r : Std.Usize) [NeZero r.val](output : Aeneas.Std.Array Bool 1600#usize)
  (suffix : Std.Slice Bool)(n i : Std.Usize)
: n = bs.length / r
→ ∃ output,
  sponge_absorb_loop bs r output suffix n i = .ok output ∧
  output.val = (Spec.sponge.absorb (f:=Spec.Keccak.P 6 24) (pad:=Spec.«pad10*1») r.val (Array.mk <| bs.val ++ suffix.val)).toArray.toList
:= by
  intro n_def
  unfold simple.sponge_absorb_loop
  split
  case isTrue h =>
    let* ⟨ i1, i1_post ⟩ ← Aeneas.Std.Usize.mul_spec
    · simp [n_def] at h
      calc r * i.val
        _ ≤ r * (bs.length / r) := Nat.mul_le_mul_left r.val (le_of_lt h)
        _ ≤ bs.length := Nat.mul_div_le bs.length r.val
        _ ≤ Std.Usize.max := bs.property
    let* ⟨ i2, i2_post ⟩ ← Aeneas.Std.Usize.add_spec
    let* ⟨ i3, i3_post ⟩ ← Aeneas.Std.Usize.mul_spec
    · simp [n_def, i2_post] at h ⊢
      calc r * (i.val + 1)
        _ ≤ r * (bs.length / r) := Nat.mul_le_mul_left r.val h
        _ ≤ bs.length := Nat.mul_div_le bs.length r.val
        _ ≤ Std.Usize.max := bs.property
    -- TODO: Should probably use a separate progress theorem for this.
    simp [Std.core.slice.index.Slice.index]
    let* ⟨ chunk, chunk_post ⟩ ← auxiliary.Slice.index
    · exact r.val.pos_of_neZero
    progress
  case isFalse h =>
    let* ⟨ i1, i1_post ⟩ ← Aeneas.Std.Usize.mul_spec
    · sorry
    sorry

@[progress]
theorem simple.sponge_absorb.spec
  (bs : Std.Slice Bool) (r : Std.Usize) [NeZero r.val](output : Aeneas.Std.Array Bool 1600#usize)
  (suffix : Std.Slice Bool)
: ∃ output,
  sponge_absorb bs r output suffix = .ok output ∧
  output.val = (Spec.sponge.absorb (f:=Spec.Keccak.P 6 24) (pad:=Spec.«pad10*1») r.val (Array.mk <| bs.val ++ suffix.val)).toArray.toList
:= by
  sorry

-- @[progress]
theorem simple.sponge.spec (r : Std.Usize) (bs output suffix: Std.Slice Bool) 
[NeZero r.val]
/- (r_ne_zero: r.val ≠ 0) -/
: ∃ output,
  simple.sponge r bs output suffix = .ok output ∧
  output.val = (Spec.sponge (f := Spec.Keccak.P 6 (nᵣ := 24)) (pad := Spec.«pad10*1») r.val (Array.mk <| bs.val ++ suffix.val ) output.length).toArray.toList
:= by

  sorry


section FinalResult

@[progress]
theorem sha3_224.spec(input: Vec Bool)
: ∃ output,
  sha3.simple.sha3_224 input = .ok (output) ∧
  output.val = (Spec.SHA3_224 input.toBitArray).toList
:= by
  sorry

@[progress]
theorem sha3_256.spec(input: Vec Bool)
: ∃ output,
  sha3.simple.sha3_256 input = .ok (output) ∧
  output.val = (Spec.SHA3_256 input.toBitArray).toList
:= by
  sorry

@[progress]
theorem sha3_384.spec(input: Vec Bool)
: ∃ output,
  sha3.simple.sha3_384 input = .ok (output) ∧
  output.val = (Spec.SHA3_384 input.toBitArray).toList
:= by
  sorry

@[progress]
theorem sha3_512.spec(input: Vec Bool)
: ∃ output,
  sha3.simple.sha3_512 input = .ok (output) ∧
  output.val = (Spec.SHA3_512 input.toBitArray).toList
:= by
  sorry
end FinalResult

end Refinement
