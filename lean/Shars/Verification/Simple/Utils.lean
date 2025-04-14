import Aeneas
import Shars.BitVec
import Shars.Definitions.Simple
import Sha3.Spec
/- import Sha3.Utils -/
import Aeneas.SimpLists.Init
import Sha3.Facts
import Init.Data.Vector.Lemmas
import Init.Data.Nat.Basic

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

@[scalar_tac_simps] theorem Fin.val_eq_iff_eq{n : ℕ} {a b : Fin n} : a = b ↔ a.val = b.val := @Fin.val_inj n a b |>.symm

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

theorem Spec.Keccak.StateArray.get_set_pos(a: Spec.Keccak.StateArray l)(x x' y y': Fin 5)(z z': Fin (w l))
(eq: (x,y,z) = (x',y',z'))
: (a.set x y z val).get x' y' z' = val
:= by simp at eq; simp [eq]

/- @[scalar_tac x % n] -/
/- theorem tmp2(x n: Nat): x % n = x ∨ x ≥ n := by -/
/-   if h: x < n then -/
/-     left; exact Nat.mod_eq_of_lt ‹x < n› -/
/-   else -/
/-     right; simpa using h -/
    
attribute [scalar_tac_simps] Nat.mod_succ 
attribute [scalar_tac_simps] Nat.cast_add Nat.cast_mul Nat.cast_ofNat Nat.cast_inj Nat.cast_le Nat.cast_ite 

@[scalar_tac Std.Usize.max]
theorem Aeneas.Std.Usize.max_bound
: 2^32 - 1 <= Std.Usize.max
:= by
  rw [Std.Usize.max_def, Std.Usize.numBits, Std.UScalarTy.numBits]
  cases System.Platform.numBits_eq <;> simp [*]

def Aeneas.Std.Array.toBitVec{size: Std.Usize}(self: Std.Array Bool size): BitVec (size.val) :=
  (BitVec.ofBoolListLE <| self.val).cast (by simp)

def simple.StateArray.toSpec(self: simple.StateArray): Spec.Keccak.StateArray 6 :=
  Spec.Keccak.StateArray.ofBitVec <| self.toBitVec.cast (by simp [Spec.w, Spec.b])

theorem Bool.xor_eq_ne(a b: Bool): (a ^^ b) = (a != b) := by cases a <;> cases b <;> decide


@[scalar_tac_simps]
theorem Fin.cast_of_mk{n: Nat}{x: Nat}(x_lt: x < n)
: Fin.mk x x_lt = @Nat.cast (Fin n) (@Fin.instNatCast n ⟨Nat.not_eq_zero_of_lt x_lt⟩) x := by
    simp only [Nat.cast, NatCast.natCast, Fin.instNatCast, Fin.ofNat', Nat.mod_eq_of_lt x_lt]

