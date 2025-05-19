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
import Shars.Verification.Auxiliary

set_option maxHeartbeats 1000000
attribute [-simp] List.getElem!_eq_getElem?_getD
attribute [simp] Aeneas.Std.Slice.set

open Aeneas hiding Std.Array
open Std.alloc.vec


@[progress]
theorem algos.theta.theta_c.spec(input : algos.StateArray)(x z: Std.Usize)
(x_idx: x.val < 5)
(z_idx: z.val < Spec.w 6)
: ∃ output, theta.c input x z = .ok output ∧ output = Spec.Keccak.θ.C input.toSpec x z
:= by rw [theta.c]; progress*; simp [*, Spec.Keccak.θ.C]

@[progress]
theorem algos.theta.theta_d.spec(input : algos.StateArray)(x z: Std.Usize)
(x_idx: x.val < 5)
(z_idx: z.val < Spec.w 6)
: ∃ output, theta.d input x z = .ok output ∧ output = Spec.Keccak.θ.D input.toSpec x z
:= by
  rw [theta.d]
  progress*
  simp [*, Spec.Keccak.θ.D, Spec.w]

  congr 2
  all_goals zmodify; try ring_nf
  rfl

@[progress]
theorem algos.theta.inner.inner_loop.spec(input a: algos.StateArray)(x y z: Std.Usize)
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
    simp at z_idx
    let* ⟨ acc_elem, acc_elem_post ⟩ ← algos.StateArray.index.spec
    let* ⟨ aux, aux_post ⟩ ← algos.theta.theta_d.spec
    let* ⟨ res_elem, res_elem_post ⟩ ← algos.binxor.spec
    let* ⟨ old_val, mk_new, old_val.post, mk_new.post ⟩ ← algos.StateArray.index_mut.spec
    let* ⟨ z_succ, z_succ_post ⟩ ← Aeneas.Std.Usize.add_spec
    let* ⟨ res, res_post ⟩ ← spec

    intro x' y' j
    simp [*, Spec.Keccak.StateArray.get_set, Fin.ext_iff, Nat.mod_eq_of_lt]
    split
    case isTrue prev_case => simp_ifs
    case isFalse curr_case =>
      split
      case isFalse unprocessed =>
        simp_ifs
      case isTrue new_case =>
        simp_ifs
        simp [*]
        -- done
  case isFalse z_oob =>
    simp
    try simp_ifs -- TODO: Doesn't work from here, nor just after the split.
    intro x' y' z'
    simp_ifs
termination_by (Spec.w 6) - z.val
decreasing_by scalar_decr_tac


@[progress]
theorem algos.theta.inner_loop.spec(input a: algos.StateArray)(x y: Std.Usize)
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
  progress*
  · simp at ‹y.val < 5›
    intro x' y' z'
    simp [*, Fin.ext_iff, Nat.mod_eq_of_lt]
    split
    case isTrue prev_case => simp_ifs
    case isFalse curr_case =>
      split
      case isFalse unprocessed => simp_ifs
      case isTrue new_processed =>
        simp_ifs
        simp [*]
  · simp_ifs; simp[*]
termination_by (5 +1) - y.val
decreasing_by

  scalar_decr_tac

@[progress]
theorem algos.theta_loop.spec(input a: algos.StateArray)(x: Std.Usize)
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
  progress*
  · simp at ‹x.val < 5›
    intro x' y' z'
    simp [*, Nat.mod_eq_of_lt, Fin.ext_iff]
    split
    case isTrue prev_case => simp_ifs
    case isFalse curr_case =>
      split
      case isFalse unprocessed => simp_ifs
      case isTrue new_processed => simp_ifs; simp [*]
  · simp_ifs; simp
termination_by 5+1 - x.val
decreasing_by scalar_decr_tac

@[progress]
theorem algos.theta.spec(input: algos.StateArray)
: ∃ output, theta input = .ok output ∧ output.toSpec = Spec.Keccak.θ input.toSpec
:= by
  rw [theta, Spec.Keccak.θ, DefaultalgosStateArray.default]
  let* ⟨ res, res_post ⟩ ← algos.theta_loop.spec
  ext x y z
  simp [res_post x y z, Spec.Keccak.StateArray.get_ofFn]
