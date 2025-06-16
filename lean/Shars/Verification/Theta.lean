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
import Shars.Verification.Refinement

/- set_option maxHeartbeats 100000 -/
attribute [-simp] List.getElem!_eq_getElem?_getD List.ofFn_succ
attribute [simp] Aeneas.Std.Slice.set Aeneas.Std.toResult
attribute [-simp] Aeneas.Std.UScalarTy.U64_numBits_eq
attribute [simp] U64.numBits_eq_w
attribute [ext (iff := false)] List.ext_getElem!

open Aeneas hiding Std.Array
open Std.alloc.vec

def IR.theta.C(state: List Bool)(x: Nat)(z: Nat): Bool :=
  let encode y := encodeIndex x y z
  state[encode 0]! ^^ (state[encode 1]! ^^ (state[encode 2]! ^^ (state[encode 3]! ^^ state[encode 4]!)))

def IR.theta.D(state: List Bool)(x: Nat)(z: Nat): Bool :=
  IR.theta.C state ((x + 4) % 5) z ^^ IR.theta.C state ((x + 1) % 5) ((z + Spec.w 6 - 1) % Spec.w 6)

theorem IR.theta.C.refinement(state: Spec.Keccak.StateArray 6)(x: Fin 5)(z: Fin (Spec.w 6))
: Spec.Keccak.θ.C state x z = IR.theta.C state.toVector.toList x.val z.val
:= by
  simp [Spec.Keccak.θ.C, Spec.Keccak.StateArray.get, IR.theta.C, Bool.bne_eq_xor, ←getElem!_pos]

@[progress]
theorem algos.theta.c.spec(input : algos.StateArray)(x : Std.Usize)
(x_idx: x.val < 5)
: ∃ output, theta.c input x = .ok output ∧
  ∀ z < Spec.w 6, output.toBits[z]! = IR.theta.C input.toBits x z
:= by
  simp [theta.c]
  progress*
  intro z z_idx
  simp [*, Std.UScalar.getElem!_xor_toBits]
  simp [IR.theta.C, List.getElem!_encodeIndex_toBits, z_idx]

theorem IR.theta.D.refinement(state: Spec.Keccak.StateArray 6)(x: Fin 5)(z: Fin (Spec.w 6))
: Spec.Keccak.θ.D state x z = IR.theta.D state.toBits x.val z.val
:= by simp +arith [Spec.Keccak.θ.D, IR.theta.C.refinement, IR.theta.D, Fin.val_sub, Fin.val_add, Spec.w]

@[progress]
theorem algos.theta.d.spec(input : algos.StateArray)(x: Std.Usize)
(x_idx: x.val < 5)
: ∃ output,
    theta.d input x = .ok output ∧
    ∀ z < Spec.w 6, output.toBits[z]! = IR.theta.D input.toBits x z
:= by
  rw [theta.d]
  progress*
  intro z z_idx
  simp +decide only [*, Spec.Keccak.θ.D, IR.theta.D,
    Aeneas.Std.UScalar.getElem!_xor_toBits,
    Std.core.num.U64.rotate_left,
    Aeneas.Std.U64.getElem!_toBits_rotate_left,
    Nat.mod_lt,
    Spec.w
    ]
  rw [i3_post]
  case a => scalar_tac
  simp [*, Spec.w]

set_option maxHeartbeats 1000000 in
@[progress]
theorem algos.theta.inner_loop.spec(input a: algos.StateArray)(x1 y: Std.Usize)
(x_idx: x1.val < 5)
(y_loop_bnd: y.val <= 5)
: ∃ output, theta.inner_loop input a x1 y = .ok output ∧
  ∀ (x' y': Fin 5)(z': Fin (Spec.w 6)),
  let idx := IR.encodeIndex x' y' z'
  output.toBits[idx]! =
    if x1 = x' ∧ y.val ≤ y'.val then
      a.toBits[idx]!  ^^ IR.theta.D a.toBits x' z'
    else input.toBits[idx]!
:= by
  rw [inner_loop, inner.inner]
  simp
  progress*
  · intro x' y' z'
    have z_idx: z'.val < Spec.w 6 := z'.isLt
    simp only [*, Fin.ext_iff, Nat.mod_eq_of_lt, List.getElem!_encodeIndex_toBits, z'.isLt, Fin.val_natCast]
    split
    case isTrue prev_case => simp_ifs
    case isFalse =>
      split
      case isTrue curr_case =>
        simp [*, ‹y.val = y'.val›']
        simp_lists
        simp [Std.UScalar.getElem!_xor_toBits, *]
      case isFalse unprocessed => simp_lists
  · simp_ifs; simp[*]
termination_by 5 - y.val
decreasing_by scalar_decr_tac

@[progress]
theorem algos.theta_loop.spec(a input: algos.StateArray)(x: Std.Usize)
: x.val ≤ 5 → ∃ output,
theta_loop a input x = .ok output ∧
(
  ∀ (x' y': Fin 5)(z': Fin (Spec.w 6)),
    let idx := IR.encodeIndex x' y' z'
    output.toBits[idx]! =
      if x.val ≤ x'.val then
        a.toBits[idx]!  ^^ IR.theta.D a.toBits x' z'
      else
        input.toBits[idx]!)
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
      case isTrue new_processed => simp_ifs
  · simp_ifs; simp
termination_by 5 - x.val
decreasing_by scalar_decr_tac

@[progress]
theorem algos.theta.spec(input: algos.StateArray)
: ∃ output, theta input = .ok output ∧
  output.toBits = (Spec.Keccak.θ (l := 6) input.toSpec).toBits
:= by
  rw [theta, Spec.Keccak.θ, DefaultalgosStateArray.default]
  simp [theta, Spec.Keccak.θ, DefaultalgosStateArray.default, IR.theta.D.refinement]
  have ⟨res, step, res_post⟩ := algos.theta_loop.spec input (Std.Array.repeat 25#usize 0#u64) 0#usize (by simp)
  simp [step]
  apply List.ext_toBits <;> try (simp; done)
  intro x y z
  have idx_lt: IR.encodeIndex x y z < Spec.b 6 := by simp [←IR.encodeIndex_spec]
  rw [Spec.Keccak.StateArray.getElem!_toBits_encodeIndex, Spec.Keccak.StateArray.get_ofFn]
  simp [*]
