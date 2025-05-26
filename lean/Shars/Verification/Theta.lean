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

set_option maxHeartbeats 1000000
attribute [-simp] List.getElem!_eq_getElem?_getD List.ofFn_succ
attribute [simp] Aeneas.Std.Slice.set Aeneas.Std.toResult
attribute [local simp] Aeneas.Std.UScalarTy.U64_numBits_eq
attribute [ext (iff := false)] List.ext_getElem!

open Aeneas hiding Std.Array
open Std.alloc.vec


def IR.theta.C(state: List Bool)(x: Nat)(z: Nat): Bool := 
  let encode y := encodeIndex x y z
  state[encode 0]! ^^ (state[encode 1]! ^^ (state[encode 2]! ^^ (state[encode 3]! ^^ state[encode 4]!)))

theorem IR.theta.C.refinement(state: Spec.Keccak.StateArray 6)(x: Fin 5)(z: Fin (Spec.w 6))
: Spec.Keccak.θ.C state x z = IR.theta.C state.toVector.toList x.val z.val
:= by
  simp only [Spec.Keccak.θ.C, Spec.Keccak.StateArray.get, Fin.isValue,
    Spec.Keccak.StateArray.encodeIndex, Fin.val_ofNat, Nat.zero_mod, mul_zero, zero_add, ←
    getElem!_pos, Fin.getElem!_fin, Nat.one_mod, mul_one, Nat.reduceMod, Nat.reduceMul,
    Bool.bne_assoc, Nat.mod_succ, C, encodeIndex, Array.getElem!_toList, Vector.getElem!_toArray]

@[simp] theorem BitVec.getElem!_xor(b1 b2: BitVec n)(i: Nat)
: (b1 ^^^ b2)[i]! = (b1[i]! ^^ b2[i]!)
:= by
  assume i < n; case otherwise h => simp [h, getElem!_neg]
  simp only [getElem!_pos, getElem_xor, *]

@[simp]
theorem Aeneas.Std.UScalar.bv_xor(u1 u2: UScalar ty): (u1 ^^^ u2).bv = u1.bv ^^^ u2.bv := by
  simp only [HXor.hXor, Aeneas.Std.UScalar.xor]

@[progress]
theorem algos.theta.c.spec(input : algos.StateArray)(x : Std.Usize)
(x_idx: x.val < 5)
: ∃ output, theta.c input x = .ok output ∧ 
  ∀ z < 64, output.toBits[z]! = IR.theta.C input.toBits x z
:= by 
  simp [theta.c]
  progress*
  intro z z_idx
  simp [IR.encodeIndex, IR.theta.C, Std.Array.toBits, List.getElem!_toBits, Spec.w, Nat.mul_add_div, Nat.div_eq_of_lt, Nat.mod_eq_of_lt, *]


def IR.theta.D(state: List Bool)(x: Nat)(z: Nat): Bool :=
  IR.theta.C state ((x + 4) % 5) z ^^ IR.theta.C state ((x + 1) % 5) ((z + Spec.w 6 - 1) % Spec.w 6)

theorem IR.theta.D.refinement(state: Spec.Keccak.StateArray 6)(x: Fin 5)(z: Fin (Spec.w 6))
: Spec.Keccak.θ.D state x z = IR.theta.D state.toVector.toList x.val z.val
:= by simp +arith [Spec.Keccak.θ.D, IR.theta.C.refinement, IR.theta.D, Fin.val_sub, Fin.val_add, Spec.w]

@[progress]
theorem algos.theta.d.spec(input : algos.StateArray)(x: Std.Usize)
(x_idx: x.val < 5)
: ∃ output,
    theta.d input x = .ok output ∧ 
    ∀ z < 64, output.toBits[z]! = IR.theta.D input.toBits x z
:= by
  rw [theta.d]
  progress*
  intro z z_idx
  simp at *
  simp [*, Spec.Keccak.θ.D, Spec.w, IR.theta.D, Std.core.num.U64.rotate_left]
  simp only [Std.UScalar.rotate_left, Std.U64.bv, z_idx,
      Std.U32.ofNat, Std.UScalar.ofNat, Std.UScalar.ofNatCore,
      Std.UScalar.val, BitVec.toNat, BitVec.getElem!_rotateLeft]
  rw [BitVec.getElem!_rotateLeft _ _ _ z_idx, i3_post, x2_post, i1_post, Std.UScalar.val, BitVec.toNat]
  case a => simp [Nat.mod_lt]
  rfl

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
    have z_idx: z'.val < 64 := z'.isLt
    simp only [Std.Array.toBits] at *
    simp only [*, Fin.ext_iff, Nat.mod_eq_of_lt, List.getElem!_encodeIndex_toBits, z'.isLt, Fin.val_natCast]
    simp only [Fin.isValue, Std.UScalar.getElem!_toBits, Std.UScalarTy.U64_numBits_eq, Bvify.U64.UScalar_bv]
    /- simp [*, Fin.ext_iff, Nat.mod_eq_of_lt, List.getElem!_toBits, Std.U64.bv] -/
    split
    case isTrue prev_case => simp_ifs
    case isFalse curr_case =>
      /- rw [List.getElem!_set] -/
      if h: x1.val = x'.val ∧ y.val = y'.val then
        /- simp [h] -/
        simp at *
        simp_lists
        simp_ifs
        simp [*]
      else
        simp_lists
        simp_ifs
  · simp_ifs; simp[*]
termination_by (5 +1) - y.val
decreasing_by

  scalar_decr_tac

@[progress]
theorem algos.theta_loop.spec(a input: algos.StateArray)(x: Std.Usize)
(x_loop_bnd: x.val <= 5)
: ∃ output, theta_loop a input x = .ok output ∧
  ∀ (x' y': Fin 5)(z': Fin (Spec.w 6)),
    let idx := IR.encodeIndex x' y' z'
    output.toBits[idx]! =
      if x.val ≤ x'.val then
        a.toBits[idx]!  ^^ IR.theta.D a.toBits x' z'
      else
        input.toBits[idx]!
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
termination_by 5+1 - x.val
decreasing_by scalar_decr_tac



/- set_option trace.Progress true in -/
@[progress]
theorem algos.theta.spec(input: algos.StateArray)
: ∃ output, theta input = .ok output ∧ output.toBits = (Spec.Keccak.θ (l := 6) input.toSpec).toVector.toList
:= by
  /- rw [theta, Spec.Keccak.θ, DefaultalgosStateArray.default] -/
  simp [theta, Spec.Keccak.θ, DefaultalgosStateArray.default, Spec.Keccak.StateArray.get,
    Spec.Keccak.StateArray.encodeIndex, IR.theta.D.refinement]
  have ⟨res, step, res_post⟩:= algos.theta_loop.spec input (Std.Array.repeat 25#usize 0#u64) 0#usize (by simp)
  simp [step, Spec.Keccak.StateArray.ofFn]
  ext idx
  · simp +decide

  by_cases idx_lt: idx < Spec.b 6; case neg => 
    simp [Spec.b, Spec.w] at idx_lt
    simp [getElem!_neg, Spec.Keccak.StateArray.ofFn, Spec.Keccak.StateArray.decodeIndex, Spec.b, Spec.w,  *]
  let xyz := Spec.Keccak.StateArray.decodeIndex ⟨idx, idx_lt⟩
  have: idx = Spec.Keccak.StateArray.encodeIndex xyz.1 xyz.2.1 xyz.2.2 := by
    have := Spec.Keccak.StateArray.decode_encode ⟨idx, idx_lt⟩
    simp at this
    simp [xyz, this]
  rw [this]

  conv => lhs; simp only [Spec.Keccak.StateArray.encodeIndex, res_post]

  simp [List.getElem!_ofFn, Spec.Keccak.StateArray.encode_decode, ←getElem!_pos]
