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

-- #check simple.pi
-- #check Spec.Keccak.StateArray.encodeIndex
-- def simple.pi.panic_free(a: List Bool): List Bool := Id.run do
--   let mut a := a
--   for x in List.finRange 5 do
--     for y in List.finRange 5 do
--       for z in List.finRange (Spec.w 6) do
--         a := a.set (Spec.Keccak.StateArray.encodeIndex x y z) 0
--   return a


@[progress]
theorem simple.pi.inner.inner_loop.spec(res input : simple.StateArray) (x y z : Std.Usize)
: x.val < 5
→ y.val < 5
→ z.val <= Spec.w 6
→ ∃ output,
  inner_loop res input x y z = .ok output ∧
  ∀ (x' y': Fin 5)(z': Fin (Spec.w 6)),
    output.toSpec.get x' y' z' =
      if x.val = x'.val ∧ y.val = y'.val ∧ z.val ≤ z'.val then
        input.toSpec.get (x + 3*y) x z'
      else
        res.toSpec.get x' y' z'
:= by
  intro x_idx y_idx z_loop_bnd
  rw [inner_loop]
  split
  case isTrue z_lt =>
    simp at z_lt
    let* ⟨ i, i_post ⟩ ← Std.Usize.mul_spec
    let* ⟨ i1, i1_post ⟩ ← Std.Usize.add_spec
    let* ⟨ x2, x2_post ⟩ ← Std.Usize.rem_spec
    let* ⟨ b, b_post ⟩ ← StateArray.index.spec
    let* ⟨ x_1, x_2, x_post_1, x_post_2 ⟩ ← StateArray.index_mut.spec
    let* ⟨ z1, z1_post ⟩ ← Std.Usize.add_spec
    let* ⟨ rest, rest_post ⟩ ← spec
    intro x' y' z'
    simp [*, Spec.Keccak.StateArray.get_set, Fin.ext_iff, Nat.mod_eq_of_lt]
    split
    case isTrue already => simp_ifs
    case isFalse =>
      split
      case isFalse unprocessed =>
        simp_ifs
      case isTrue just_updated =>
        simp_ifs
        simp [*]
        congr 1
        zmodify

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
    simp [*]
    intro x' y' z'
    split
    case isTrue already => simp_ifs
    case isFalse =>
      split
      case isFalse unprocessed => simp_ifs
      case isTrue new_case =>
        simp [*]
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
    simp [*]
    split
    · simp_ifs
    · split
      · simp [*]
      · simp_ifs
  · simp
    simp_ifs
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
