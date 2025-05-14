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
import Shars.Verification.Simple.Auxiliary

set_option maxHeartbeats 1000000
attribute [-simp] List.getElem!_eq_getElem?_getD
attribute [simp] Aeneas.Std.Slice.set

open Aeneas hiding Std.Array
open Std.alloc.vec

#check Fin.val_natCast
attribute [scalar_tac_simps] Fin.val_natCast
-- attribute [-scalar_tac_simps] Nat.mod_eq_of_lt
-- attribute [scalar_tac x % m] Nat.over_mod_or_mod_eq

@[simp]
theorem Fin.natCast_mod(x n: Nat)[NeZero n]: ((x % n : Nat) : Fin n) = (x : Fin n) := by
  simp only [Nat.cast, NatCast.natCast, Fin.ofNat', Nat.mod_mod]

@[progress]
theorem simple.chi.inner.inner_loop.spec(res a: StateArray)(x y z: Std.Usize)
: x.val < 5
→ y.val < 5
→ z.val <= Spec.w 6
→ ∃ output,
  inner_loop res a x y z = .ok output ∧
  (∀ (x' y': Fin 5)(z': Fin (Spec.w 6)),
    output.toSpec.get x' y' z' =
      if x = x' ∧ y = y' ∧ z.val ≤ z'  then
        (a.toSpec.get x' y' z' ^^ ((a.toSpec.get (x' + 1) y' z' ^^ true) && a.toSpec.get (x' + 2) y' z'))
      else
        res.toSpec.get x' y' z')
  /- (∀ (x' y': Fin 5)(z': Fin (Spec.w 6)), x = x' ∧ y = y' ∧ z.val ≤ z' → -/
  /-   output.toSpec.get x' y' z' = (a.toSpec.get x' y' z' ^^ ((a.toSpec.get (x + 1) y' z' ^^ true) && a.toSpec.get (x' + 2) y' z'))) ∧ -/
  /- (∀ (x' y': Fin 5)(z': Fin (Spec.w 6)), ¬ (x = x' ∧ y = y' ∧ z ≤ z') → -/
  /-   output.toSpec.get x' y' z' = res.toSpec.get x' y' z') -/
:= by
  intro x_lt y_lt z_loop_bound
  rw [inner_loop]
  progress*
  · -- z < W
    -- b2 = true
    simp at ‹z < W›
    simp [*, Spec.Keccak.StateArray.get_set] --, Fin.ext_iff, Nat.mod_eq_of_lt]
    intro x' y' z'
    split
    case isTrue => simp_ifs
    case isFalse =>
      split
      case isFalse =>
        simp_ifs
      case isTrue h =>
        simp only [h, Fin.cast_val_eq_self]
        simp [x1_post, i_post, h, Fin.cast_val_eq_self] at b1_post b2_post
        simp_ifs
        simp [*, -b1_post, ←b1_post, ←b2_post]
  · -- z < W
    -- b2 = false
    simp [*, Spec.Keccak.StateArray.get_set]
    intro x' y' z'
    split
    case isTrue => simp_ifs
    case isFalse =>
      split
      case isFalse => simp_ifs
      case isTrue h =>
        simp_ifs
        simp [x1_post, i_post, h, Fin.cast_val_eq_self] at b1_post b2_post
        simp [*, -b1_post, ←b1_post, ←b2_post]
  · -- z ≥ W
    simp [‹z.val = Spec.w 6›']
    intros
    simp_ifs
termination_by Spec.w 6 - z.val
decreasing_by
  scalar_decr_tac
  simp [*]
  scalar_tac

/- theorem asdf(z: Std.Usize): z.val < Spec.w 6 → Spec.w 6 - (z.val + 1) < Spec.w 6 - z.val := by -/
/-   intro z_idx -/
/-   apply Nat.sub_lt_left_of_lt_add z_idx -/
/-   rw [←Nat.add_sub_assoc <| le_of_lt z_idx, Nat.add_comm, Nat.succ_eq_add_one, Nat.add_comm z.val, Nat.add_sub_assoc (by omega), Nat.add_sub_cancel] -/
/-   exact lt_add_one (Spec.w 6) -/

@[progress]
theorem simple.chi.inner_loop.spec(res a: StateArray)(x y : Std.Usize)
: x.val < 5
→ y.val <= 5
→ ∃ output,
  inner_loop res a x y = .ok output ∧
  ∀ (x' y': Fin 5)(z': Fin (Spec.w 6)),
    output.toSpec.get x' y' z' =
      if x = x' ∧ y.val ≤ y' then
        (a.toSpec.get x' y' z' ^^ ((a.toSpec.get (x' + 1) y' z' ^^ true) && a.toSpec.get (x' + 2) y' z'))
      else
        res.toSpec.get x' y' z'
:= by
  intro x_lt y_loop_bnd
  rw [inner_loop, inner.inner]
  split
  case isTrue h =>
    let* ⟨ res1, res1_post ⟩ ← inner.inner_loop.spec
    simp at res1_post
    let* ⟨ y1, y1_post ⟩ ← Std.Usize.add_spec
    let* ⟨ rest, rest_post ⟩ ← spec

    intro x' y' z'
    simp [*]
    split
    case isTrue already => simp_ifs
    case isFalse =>
      split
      case isFalse unprocessed => simp_ifs
      case isTrue new_case => simp_ifs
  case isFalse h =>
    simp_ifs
    simp [*]
termination_by 5 - y.val
decreasing_by scalar_decr_tac

@[progress]
theorem simple.chi_loop.spec(res a: StateArray)(x: Std.Usize)
: x.val <= 5
→ ∃ output,
  chi_loop a res x = .ok output ∧
  ∀ (x' y': Fin 5)(z': Fin (Spec.w 6)),
    output.toSpec.get x' y' z' =
      if x.val ≤ x'.val then
        (a.toSpec.get x' y' z' ^^ ((a.toSpec.get (x' + 1) y' z' ^^ true) && a.toSpec.get (x' + 2) y' z'))
      else
        res.toSpec.get x' y' z'
:= by
  intro x_loop_bound
  rw [chi_loop]
  split
  case isTrue x_idx =>
    simp at x_idx

    let* ⟨ res1, res1_post ⟩ ← chi.inner_loop.spec
    let* ⟨ x1, x1_post ⟩ ← Std.Usize.add_spec
    let* ⟨ res, res_post ⟩ ← spec

    intro x' y' z'
    simp [*]
    split
    case isTrue already => simp_ifs
    case isFalse =>
      split
      case isFalse unprocessed => simp_ifs
      case isTrue new_case => simp_ifs
  case isFalse x_oob =>
    simp [‹x.val = 5›']
    intro x' y' z'
    simp_ifs
termination_by 5 - x.val
decreasing_by scalar_decr_tac

@[progress]
theorem simple.chi.spec(input: StateArray)
: ∃ output,
  chi input = .ok output ∧
  output.toSpec = Spec.Keccak.χ input.toSpec
:= by
  simp [chi, ClonesimpleStateArray.clone]
  progress as ⟨output, output_post⟩
  ext x' y' z'
  simp [output_post, Spec.Keccak.χ]
