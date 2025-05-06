import Aeneas
import Shars.BitVec
import Shars.Definitions.Simple
import Sha3.Spec
/- import Sha3.Utils -/
import Aeneas.SimpLists.Init
import Sha3.Facts
import Init.Data.Vector.Lemmas
import Init.Data.Nat.Basic

open Aeneas hiding Std.Array in
@[simp, scalar_tac_simps]
theorem OrdUsize.min_val (x y : Std.Usize) : (Std.core.cmp.impls.OrdUsize.min x y).val = Nat.min x.val y.val := by
  simp [Std.core.cmp.impls.OrdUsize.min]; split <;> simp [*] <;> omega

attribute [scalar_tac_simps] Classical.not_and_iff_or_not_not
attribute [scalar_tac_simps] Fin.val_add Fin.val_mul
attribute [scalar_tac_simps] List.length_finRange List.length_zipWith
attribute [scalar_tac_simps] lt_inf_iff le_inf_iff true_and and_true not_lt not_le

attribute [scalar_tac_simps] Nat.mod_succ
attribute [scalar_tac_simps] Nat.cast_add Nat.cast_mul Nat.cast_ofNat Nat.cast_inj Nat.cast_le Nat.cast_ite
attribute [scalar_tac a.val] Fin.is_le'
attribute [scalar_tac self] Fin.isLt

@[scalar_tac_simps] theorem Fin.val_eq_iff_eq{n : ℕ} {a b : Fin n} : a = b ↔ a.val = b.val := @Fin.val_inj n a b |>.symm

@[scalar_tac_simps, simp]
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


@[scalar_tac Std.Usize.max]
theorem Aeneas.Std.Usize.max_bound
: 2^32 - 1 <= Std.Usize.max
:= by
  rw [Std.Usize.max_def, Std.Usize.numBits, Std.UScalarTy.numBits]
  cases System.Platform.numBits_eq <;> simp [*]


@[scalar_tac_simps]
theorem Fin.cast_of_mk{n: Nat}{x: Nat}(x_lt: x < n)
: Fin.mk x x_lt = @Nat.cast (Fin n) (@Fin.instNatCast n ⟨Nat.not_eq_zero_of_lt x_lt⟩) x := by
    simp only [Nat.cast, NatCast.natCast, Fin.instNatCast, Fin.ofNat', Nat.mod_eq_of_lt x_lt]

@[scalar_tac inst]
def Nat.pos_of_neZero'{n: Nat}(inst: NeZero n): n > 0 := @Nat.pos_of_neZero n inst

attribute [scalar_tac_simps] Nat.one_le_two_pow

@[scalar_tac Aeneas.Std.UScalarTy.Usize.numBits]
theorem Std.UScalarTy.Usize_numBits_le: Aeneas.Std.UScalarTy.Usize.numBits ≥ 32 := by
  rcases System.Platform.numBits_eq with h | h <;> simp [h]
