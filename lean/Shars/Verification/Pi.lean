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

set_option maxHeartbeats 100000
set_option Elab.async false
attribute [-simp] List.getElem!_eq_getElem?_getD
attribute [simp] Aeneas.Std.Slice.set
attribute [ext (iff := false)] List.ext_getElem

open Aeneas hiding Std.Array
open Std.alloc.vec

set_option maxHeartbeats 1000000 in
@[progress]
theorem algos.pi.inner_loop.spec(res input : algos.StateArray) (x y : Std.Usize)
: x.val < 5
→ y.val ≤ 5
→ ∃ output,
  inner_loop res input x y = .ok output ∧
  ∀ (x' y': Fin 5)(z': Fin (Spec.w 6)),
    let idx := IR.encodeIndex x' y' z'
    output.toBits[idx]! =
      if x.val = x'.val ∧ y.val ≤ y'.val then
        input.toBits[IR.encodeIndex ((x' + 3*y') % 5) x' z']!
      else
        res.toBits[idx]!
:= by
  intro x_idx y_loop_bnd
  rw [inner_loop]
  progress*
  · intro x' y' z'
    simp only [*, List.getElem!_encodeIndex_toBits, z'.isLt]
    split
    case isTrue already => simp_ifs
    case isFalse =>
      split
      case isFalse unprocessed =>
        simp_ifs
        simp_lists
      case isTrue just_updated =>
        simp_lists
        simp [*, ‹y.val = y'.val›']

  case isFalse z_oob =>
    simp; intros; simp_ifs
termination_by 5 - y.val
decreasing_by scalar_decr_tac

@[progress]
theorem algos.pi_loop.spec(input res : algos.StateArray) (x: Std.Usize)
: x.val ≤ 5
→ ∃ output,
   pi_loop input res  x = .ok output ∧
  ∀ (x' y': Fin 5)(z': Fin (Spec.w 6)),
    let idx := IR.encodeIndex x' y' z'
    output.toBits[idx]! =
      if x.val ≤ x'.val then
        input.toBits[IR.encodeIndex ((x' + 3*y') % 5) x' z']!
      else
        res.toBits[idx]!
:= by
  intro x_loop_bnd
  rw [pi_loop]
  progress*
  · simp [*]
    intro x' y' z'
    split
    case isTrue => simp_ifs
    case isFalse =>
      split <;> simp_ifs
  · simp_ifs; simp
termination_by 5 - x.val
decreasing_by scalar_decr_tac

@[progress]
theorem algos.pi.spec(input: algos.StateArray)
: ∃ output,
  pi input = .ok output ∧
  output.toBits = (Spec.Keccak.π input.toSpec).toBits
:= by
  simp [pi, Spec.Keccak.π, ClonealgosStateArray.clone]
  let* ⟨ res, res_post ⟩ ← pi_loop.spec
  apply List.ext_toBits <;> simp +decide [←getElem!_pos]
  intro x' y' z'
  simp [res_post, Spec.Keccak.StateArray.ofFn]
  rw [Spec.Keccak.StateArray.Vector.getElem!_ofFn', ←Spec.Keccak.StateArray.encodeIndex]
  simp
  congr 2; zmodify
