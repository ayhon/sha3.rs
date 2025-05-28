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

attribute [scalar_tac_simps] Fin.val_natCast
@[simp]
theorem Fin.natCast_mod(x n: Nat)[NeZero n]: ((x % n : Nat) : Fin n) = (x : Fin n) := by
  simp only [Nat.cast, NatCast.natCast, Fin.ofNat', Nat.mod_mod]

@[simp]
theorem Aeneas.Std.UScalar.getElem!_and_toBits(u1 u2: Std.UScalar ty)(i: Nat)
: (u1 &&& u2).toBits[i]! = (u1.toBits[i]! && u2.toBits[i]!)
:= by
  if i_idx: i < ty.numBits then
    simp [toBits, List.getElem!_ofFn, i_idx]
  else
    rw [getElem!_neg]
    rw [getElem!_neg]
    rw [getElem!_neg]
    simp [default]
    simpa using i_idx
    simpa using i_idx
    simpa using i_idx

@[simp]
theorem Aeneas.Std.core.num.U64.getElem!_toBits_MAX
: U64.MAX.toBits = List.replicate (Spec.w 6) true
:= by native_decide

/- set_option trace.profiler true in -/
set_option maxHeartbeats 1000000 in
@[progress]
theorem algos.chi.inner_loop.spec(res a: StateArray)(x y: Std.Usize)
: x.val < 5
→ y.val ≤ 5
→ ∃ output,
  inner_loop res a x y = .ok output ∧
  (∀ (x' y': Fin 5)(z': Fin (Spec.w 6)),
    let idx := IR.encodeIndex x' y' z'
    output.toBits[idx]! =
      if x = x' ∧ y.val <= y'.val  then
        (a.toBits[idx]! ^^ ((a.toBits[Spec.Keccak.StateArray.encodeIndex (x' + 1) y' z']! ^^ true) && a.toBits[Spec.Keccak.StateArray.encodeIndex (x' + 2) y' z']!))
      else
        res.toBits[idx]!)
  /- (∀ (x' y': Fin 5)(z': Fin (Spec.w 6)), x = x' ∧ y = y' ∧ z.val ≤ z' → -/
  /-   output.toSpec.get x' y' z' = (a.toSpec.get x' y' z' ^^ ((a.toSpec.get (x + 1) y' z' ^^ true) && a.toSpec.get (x' + 2) y' z'))) ∧ -/
  /- (∀ (x' y': Fin 5)(z': Fin (Spec.w 6)), ¬ (x = x' ∧ y = y' ∧ z ≤ z') → -/
  /-   output.toSpec.get x' y' z' = res.toSpec.get x' y' z') -/
:= by
  intro x_lt y_loop_bnd
  rw [inner_loop]
  simp [Std.toResult]
  progress*
  · -- z < W
    -- b2 = true
    intro x' y' z'
    simp [*, Std.Array.toBits]
    simp [List.getElem!_toBits, show 64 = Spec.w 6 from rfl,
      ←IR.encodeIndex_spec, IR.encodeIndex_xy, IR.encodeIndex_z,
      Nat.mod_eq_of_lt, z'.isLt]

    /- simp [*, Spec.Keccak.StateArray.get_set] --, Fin.ext_iff, Nat.mod_eq_of_lt] -/
    split
    case isTrue => simp_ifs
    case isFalse =>
      by_cases cond: x.val = x'.val ∧ y.val = y'.val
      case pos =>
        simp [cond, List.getElem!_toBits, IR.encodeIndex_xy, IR.encodeIndex_z]
        simp_lists
        simp [Aeneas.Std.UScalar.getElem!_xor_toBits,
              Aeneas.Std.UScalar.getElem!_and_toBits,
              Std.core.num.U64.getElem!_toBits_MAX, 
              List.getElem!_replicate, Nat.mod_eq_of_lt, z'.isLt,
              Fin.val_add]
      case neg =>
        simp [cond, IR.encodeIndex_xy, IR.encodeIndex_z, ‹5*y'.val + x'.val ≠ 5*y + x›']
        simp_ifs
  · -- z ≥ W
    simp [‹y.val = 5›']
    intros
    simp_ifs
termination_by 5 - y.val
decreasing_by scalar_decr_tac

/- theorem asdf(z: Std.Usize): z.val < Spec.w 6 → Spec.w 6 - (z.val + 1) < Spec.w 6 - z.val := by -/
/-   intro z_idx -/
/-   apply Nat.sub_lt_left_of_lt_add z_idx -/
/-   rw [←Nat.add_sub_assoc <| le_of_lt z_idx, Nat.add_comm, Nat.succ_eq_add_one, Nat.add_comm z.val, Nat.add_sub_assoc (by omega), Nat.add_sub_cancel] -/
/-   exact lt_add_one (Spec.w 6) -/

@[progress]
theorem algos.chi_loop.spec(res a: StateArray)(x: Std.Usize)
: x.val <= 5
→ ∃ output,
  chi_loop a res x = .ok output ∧
  ∀ (x' y': Fin 5)(z': Fin (Spec.w 6)),
    let idx := IR.encodeIndex x' y' z'
    output.toBits[idx]! =
      if x.val ≤ x'.val then
        (a.toBits[idx]! ^^ ((a.toBits[Spec.Keccak.StateArray.encodeIndex (x' + 1) y' z']! ^^ true) && a.toBits[Spec.Keccak.StateArray.encodeIndex (x' + 2) y' z']!))
      else
        res.toBits[idx]!
:= by
  intro x_loop_bound
  rw [chi_loop]
  simp [Std.toResult]
  progress*
  · intro x' y' z'
    simp [*]
    split
    case isTrue already => simp_ifs
    case isFalse =>
      split
      case isFalse unprocessed => simp_ifs
      case isTrue new_case => simp_ifs
  · simp [‹x.val = 5›']
    intro x' y' z'
    simp_ifs
termination_by 5 - x.val
decreasing_by scalar_decr_tac

@[progress]
theorem algos.chi.spec(input: StateArray)
: ∃ output,
  chi input = .ok output ∧
  output.toSpec = Spec.Keccak.χ input.toSpec
:= by
  simp [chi, ClonealgosStateArray.clone]
  progress as ⟨output, output_post⟩
  ext x' y' z'
  rw [List.get_toStateArray (len_ls := by simp +decide)]
  simp [List.get_toStateArray, output_post, Spec.Keccak.χ]
  rw [List.get_toStateArray (len_ls := by simp +decide)]
  rw [List.get_toStateArray (len_ls := by simp +decide)]
  rw [List.get_toStateArray (len_ls := by simp +decide)]
  simp [IR.encodeIndex_spec]
