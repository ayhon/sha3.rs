import Aeneas
/- import Shars.BitVec -/
import Shars.Definitions.Algos
import Shars.Verification.Utils.SimpLikeTactics
import Aeneas.SimpLists.Init
import Sha3.Facts
/- import Init.Data.Vector.Lemmas -/
/- import Init.Data.Nat.Basic -/

section SimpLemmas

attribute [scalar_tac_simps] Classical.not_and_iff_or_not_not
attribute [scalar_tac_simps] Fin.val_add Fin.val_mul
attribute [scalar_tac_simps] List.length_finRange List.length_zipWith
attribute [scalar_tac_simps] lt_inf_iff le_inf_iff true_and and_true not_lt not_le
attribute [scalar_tac_simps] Nat.mod_succ
attribute [scalar_tac_simps] Nat.cast_add Nat.cast_mul Nat.cast_ofNat Nat.cast_inj Nat.cast_le Nat.cast_ite
attribute [scalar_tac_simps] Fin.val_ofNat
attribute [scalar_tac_simps] Spec.w Spec.b
attribute [scalar_tac_simps] Nat.one_le_two_pow
attribute [scalar_tac_simps] Nat.mul_add Nat.mul_sub

@[scalar_tac_simps]
theorem Nat.div_sub_self(a b: Nat)
:(a - b) / b = a / b - 1 := by
  by_cases b > 0
  case neg h => simp at h; subst h; simp
  by_cases a >= b
  case pos h =>
    have: a = (a - b) + b := (Nat.sub_eq_iff_eq_add h).mp rfl
    rw [this, Nat.add_sub_cancel, Nat.add_div_right, Nat.add_sub_cancel]
    assumption
  case neg h =>
    simp at h
    simp [Nat.div_eq_of_lt h, Nat.sub_eq_zero_of_le (le_of_lt h)]

@[scalar_tac_simps]
theorem Nat.div_sub_mult_left(a b: Nat)
:(a - b*i) / b = a / b - i := by
  by_cases b > 0
  case neg h => simp at h; subst h; simp
  case pos =>
    cases i
    case zero => simp
    case succ i' =>
      simp [Nat.mul_add, Nat.sub_add_eq, Nat.div_sub_self]
      rw [Nat.div_sub_mult_left]


open Aeneas hiding Std.Array in
@[simp, scalar_tac_simps]
theorem OrdUsize.min_val (x y : Aeneas.Std.Usize) : (Aeneas.Std.core.cmp.impls.OrdUsize.min x y).val = Nat.min x.val y.val := by
  simp [Aeneas.Std.core.cmp.impls.OrdUsize.min]; split <;> simp [*] <;> omega

@[scalar_tac_simps]
theorem Fin.val_eq_iff_eq{n : ℕ} {a b : Fin n} : a = b ↔ a.val = b.val := @Fin.val_inj n a b |>.symm

@[scalar_tac_simps, simp]
theorem algos.W.val: algos.W = Spec.w 6 := by native_decide

@[scalar_tac_simps]
theorem Fin.cast_of_mk{n: Nat}{x: Nat}(x_lt: x < n)
: Fin.mk x x_lt = @Nat.cast (Fin n) (@Fin.instNatCast n ⟨Nat.ne_zero_of_lt x_lt⟩) x := by
    simp only [Nat.cast, NatCast.natCast, Fin.instNatCast, Fin.ofNat', Nat.mod_eq_of_lt x_lt]

end SimpLemmas

section SaturationRules

attribute [scalar_tac a.val] Fin.is_le'
attribute [scalar_tac self] Fin.isLt

@[scalar_tac x % m]
theorem Nat.over_mod_or_mod_eq(x m: Nat): m ≤ x ∨ x % m = x := by
  by_cases m ≤ x
  · left; assumption
  · right; simp at *; simp [Nat.mod_eq_of_lt, *]

@[scalar_tac x % v]
theorem Nat.zero_mod_or_mod_lt(x v: Nat): v = 0 ∨ x % v < v := by
  match h: v with
  | 0 => left; rfl
  | v'+1 =>
    right
    apply Nat.mod_lt
    exact Nat.zero_lt_succ v'

/-
This rule adds the "implication" x < 5 → y < 5 → w * (5 * y + x) ≤ w * 24
for scalar_tac when it detects that there is a term of the form 5 * ?y + ?x
in the hypothesis. Useful when reasoning about indices to Keccak's state
array.
-/
-- @[nonlin_scalar_tac 5 * y + x] -- TODO: Probably, this is better
@[scalar_tac 5 * y + x]
theorem scalar_tac_specific_lemma_for_sha3_keccak_state_packing(x: Fin 5)(y: Fin 5)
: Spec.w 6 * (5 * y + x) ≤ Spec.w 6 * 24
:= by
  apply Nat.mul_le_mul_left (k := Spec.w 6)
  exact Nat.le_pred_of_lt (Nat.lt_packing_right x.isLt y.isLt)

@[scalar_tac Std.Usize.max]
theorem Aeneas.Std.Usize.max_bound
: 2^32 - 1 <= Std.Usize.max
:= by
  rw [Std.Usize.max_def, Std.Usize.numBits, Std.UScalarTy.numBits]
  cases System.Platform.numBits_eq <;> simp [*]

/-
Allows scalar_tac to reason about instances of `NeZero`. It translates it to pos.
-/
@[scalar_tac inst]
def Nat.pos_of_neZero'{n: Nat}(inst: NeZero n): n > 0 := @Nat.pos_of_neZero n inst

@[scalar_tac Aeneas.Std.UScalarTy.Usize.numBits]
theorem Aeneas.Std.UScalarTy.Usize_numBits_le: Aeneas.Std.UScalarTy.Usize.numBits ≥ 32 := by
  rcases System.Platform.numBits_eq with h | h <;> simp [h]

end SaturationRules
