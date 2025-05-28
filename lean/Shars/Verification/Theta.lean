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
  simp only [Spec.Keccak.θ.C, Spec.Keccak.StateArray.get, Fin.isValue,
    Spec.Keccak.StateArray.encodeIndex, Fin.val_ofNat, Nat.zero_mod, mul_zero, zero_add, ←
    getElem!_pos, Fin.getElem!_fin, Nat.one_mod, mul_one, Nat.reduceMod, Nat.reduceMul,
    Bool.bne_assoc, Nat.mod_succ, C, encodeIndex, Array.getElem!_toList, Vector.getElem!_toArray]

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
  simp [IR.theta.C, Std.Array.toBits, List.getElem!_toBits, ←show Spec.w 6 = 64 from rfl,
    IR.encodeIndex_xy, IR.encodeIndex_z, z_idx, Nat.mod_eq_of_lt]

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
    ] -- Std.core.num.U64.rotate_left, ←getElem!_pos]
  rw [i3_post]
  case a => scalar_tac
  simp [*, Spec.w]

/- @[progress] -/
/- theorem algos.theta.inner.inner_loop.spec(input a: algos.StateArray)(x y z: Std.Usize) -/
/- (x_idx: x.val < 5) -/
/- (y_idx: y.val < 5) -/
/- (z_loop_bnd: z.val <= Spec.w 6) -/
/- : ∃ output, theta.inner.inner_loop input a x y z = .ok output ∧ -/
/-   ∀ (x' y': Fin 5)(z': Fin (Spec.w 6)), -/
/-   output.toSpec.get x' y' z' = -/
/-     if x = x' ∧ y = y' ∧ z.val ≤ z'.val then -/
/-         a.toSpec.get x y z'  ^^ Spec.Keccak.θ.D a.toSpec x z' -/
/-       else input.toSpec.get x' y' z' -/
/- := by -/
/-   rw [theta.inner.inner_loop] -/
/-   split -/
/-   case isTrue z_idx => -/
/-     simp at z_idx -/
/-     let* ⟨ acc_elem, acc_elem_post ⟩ ← algos.StateArray.index.spec -/
/-     let* ⟨ aux, aux_post ⟩ ← algos.theta.theta_d.spec -/
/-     let* ⟨ res_elem, res_elem_post ⟩ ← algos.binxor.spec -/
/-     let* ⟨ old_val, mk_new, old_val.post, mk_new.post ⟩ ← algos.StateArray.index_mut.spec -/
/-     let* ⟨ z_succ, z_succ_post ⟩ ← Aeneas.Std.Usize.add_spec -/
/-     let* ⟨ res, res_post ⟩ ← spec -/

/-     intro x' y' j -/
/-     simp [*, Spec.Keccak.StateArray.get_set, Fin.ext_iff, Nat.mod_eq_of_lt] -/
/-     split -/
/-     case isTrue prev_case => simp_ifs -/
/-     case isFalse curr_case => -/
/-       split -/
/-       case isFalse unprocessed => -/
/-         simp_ifs -/
/-       case isTrue new_case => -/
/-         simp_ifs -/
/-         simp [*] -/
/-         -- done -/
/-   case isFalse z_oob => -/
/-     simp -/
/-     try simp_ifs -- TODO: Doesn't work from here, nor just after the split. -/
/-     intro x' y' z' -/
/-     simp_ifs -/
/- termination_by (Spec.w 6) - z.val -/
/- decreasing_by scalar_decr_tac -/

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

@[simp] theorem Vector.getElem!_mk {xs : Array α}[Inhabited α] {size : xs.size = n} {i : Nat} :
    (Vector.mk xs size)[i]! = xs[i]! := by 
    if h : i < n then
      simp only [getElem!_pos, h, size, Vector.getElem_mk]
    else
      rw [getElem!_neg]
      case h => assumption
      rw [getElem!_neg]
      case h => exact size ▸ h

theorem Spec.Keccak.StateArray.toBits_set(state: Spec.Keccak.StateArray 6)(x y: Fin 5)(z: Fin (Spec.w 6))(b: Bool)
: (state.set x y z b).toBits = state.toBits.set (IR.encodeIndex x y z) b
:= by simp [toBits, StateArray.set]

@[progress]
theorem algos.theta.spec(input: algos.StateArray)
: ∃ output, theta input = .ok output ∧ 
  output.toBits = (Spec.Keccak.θ (l := 6) input.toSpec).toBits
:= by
  rw [theta, Spec.Keccak.θ, DefaultalgosStateArray.default]
  simp [theta, Spec.Keccak.θ, DefaultalgosStateArray.default, IR.theta.D.refinement]
  have ⟨res, step, res_post⟩ := algos.theta_loop.spec input (Std.Array.repeat 25#usize 0#u64) 0#usize (by simp)
  simp [step]
  ext idx
  · simp
  simp at res_post

  by_cases idx_lt: idx < Spec.b 6; case neg =>
    simp [Spec.b, Spec.w] at idx_lt
    simp [getElem!_neg, Spec.Keccak.StateArray.ofFn, Spec.Keccak.StateArray.decodeIndex, Spec.b, Spec.w,  *]

  obtain ⟨x, y, z, encode_xyz_idx⟩ := IR.decode_surjective idx idx_lt

  simp only [←encode_xyz_idx] at idx_lt ⊢
  simp only [res_post, Spec.Keccak.StateArray.getElem!_toBits, idx_lt]
  simp only [Fin.eta, ←IR.encodeIndex_spec, Spec.Keccak.StateArray.encode_decode, Spec.Keccak.StateArray.get_ofFn]
