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
  split
  case isTrue z_lt =>
    progress as ⟨ i, i_post ⟩
    progress as ⟨ x1, x1_post ⟩
    fsimp only [*] at x1_post; clear i_post i
    progress as ⟨ i1, i1_post ⟩
    progress as ⟨ x2, x2_post ⟩
    fsimp only [*] at x2_post; clear i1_post i1
    progress as ⟨ b, b_post ⟩
    progress as ⟨ b1, b1_post ⟩
    fsimp only [*] at b1_post; clear x1_post x1
    progress as ⟨ b2, b2_post ⟩
    fsimp only [*] at b2_post; clear b1_post b1
    split <;> rename_i b2_val
    . progress as ⟨ b3, b3_post ⟩
      fsimp only [*] at b3_post; clear x2_post x2
      progress as ⟨ b4, b4_post ⟩
      rw [←Bool.true_and b3, ←b2_val] at b4_post
      fsimp only [*] at b4_post; clear b3_post b3 b_post b b2_post b2_val b2
      progress as ⟨ old_res, new_res, old_res_post, new_res_post ⟩
      progress as ⟨ z1, z1_post ⟩
      progress as ⟨ rest, rest_post ⟩
      /- progress as ⟨ rest, rest_post_1, rest_post_2 ⟩ -/
      fsimp only [*] at rest_post; clear old_res_post new_res_post old_res new_res z1 z1_post b4 b4_post
      intro x' y' z'
      rw [rest_post]
      split_all
      · rfl
      · scalar_tac
      · simp [‹z.val.cast = z'›', *]
        rename_i h; obtain ⟨h, h2, h3⟩ := h
        congr 2
        · congr 1
          scalar_tac
        · scalar_tac
      · rw [Spec.Keccak.StateArray.get_set_neq]
        scalar_tac_preprocess
        scalar_tac
    · simp at b2_val
      simp [b2_val] at b2_post
      progress as ⟨b4, b4_post⟩
      fsimp only [b_post] at b4_post; clear b_post b
      progress as ⟨old_res, new_res, old_res_post, new_res_post⟩
      progress as ⟨z1, z1_post⟩
      progress as ⟨rest, rest_post⟩
      fsimp only [*] at rest_post; clear old_res new_res old_res_post new_res_post z1_post z1
      intro x' y' z'
      rw [rest_post]
      split_all
      · rfl
      · scalar_tac
      · simp [‹z.val.cast = z'›', *] at b2_post ⊢
        have: Spec.Keccak.StateArray.get (x' + 1) y' z' a.toSpec = true := by
          rw [←b2_post]
          congr 2
          scalar_tac
        simp [this]
      · rw [Spec.Keccak.StateArray.get_set_neq]
        scalar_tac_preprocess
        scalar_tac
  case isFalse z_oob =>
    simp [‹z.val = Spec.w 6›']
    intros
    simp_ifs
termination_by Spec.w 6 - z.val
decreasing_by 
  /- rw [z1_post] -/
  /- apply Nat.sub_lt_left_of_lt_add z_idx -/
  /- rw [←Nat.add_sub_assoc <| le_of_lt z_idx, Nat.add_comm, Nat.succ_eq_add_one, Nat.add_comm z.val, Nat.add_sub_assoc (by omega), Nat.add_sub_cancel] -/
  /- exact lt_add_one (Spec.w 6) -/
  scalar_decr_tac
  simp [z1_post]
  scalar_tac
  /- sorry -/

theorem asdf(z: Std.Usize): z.val < Spec.w 6 → Spec.w 6 - (z.val + 1) < Spec.w 6 - z.val := by
  intro z_idx
  apply Nat.sub_lt_left_of_lt_add z_idx
  rw [←Nat.add_sub_assoc <| le_of_lt z_idx, Nat.add_comm, Nat.succ_eq_add_one, Nat.add_comm z.val, Nat.add_sub_assoc (by omega), Nat.add_sub_cancel]
  exact lt_add_one (Spec.w 6)


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
    rw [rest_post, y1_post]
    split_all
    · rfl
    · scalar_tac
    · simp [‹y.val.cast = y'›', *]
    · simp [*]
      intro xx' yy'
      scalar_tac
  case isFalse h =>
    simp
    intros
    simp_ifs
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

    simp [res_post, x1_post]
    intro x' y' z'
    split_all
    · rfl
    · scalar_tac
    · simp [*, ‹x.val.cast = x'›']
    · simp [*]
      intro xx'
      scalar_tac
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
