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

    intro x' y' j
    simp [*] at res_post
    rw [res_post]; clear res_post
    split_all
    · rfl
    · scalar_tac
    · simp [‹j= z.val.cast›', *]
    · simp_ifs [Spec.Keccak.StateArray.get_set]
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
