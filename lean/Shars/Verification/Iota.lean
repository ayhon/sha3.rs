import Aeneas
import Shars.BitVec
import Shars.Definitions.Algos
import Sha3.Spec
/- import Sha3.Utils -/
import Aeneas.SimpLists.Init
import Sha3.Facts
import Init.Data.Vector.Lemmas
import Init.Data.Nat.Basic
import Shars.Verification.Constants
import Shars.Verification.Utils
import Shars.Verification.Auxiliary

open Aeneas hiding Std.Array
open Std.alloc.vec

attribute [-simp] List.getElem!_eq_getElem?_getD
attribute [ext (iff := false)] List.ext_getElem!

theorem algos.IOTA_RC.spec
: ∀ iᵣ < 24, IOTA_RC.val[iᵣ]!.toBits = (Spec.Keccak.ι.RC (l := 6) iᵣ).toList
:= by native_decide

theorem List.ext_toBits{bs1 bs2: List (Bool)}
  (len_bs1: bs1.length = Spec.b 6)
  (len_bs2: bs2.length = Spec.b 6)
  (point_eq: ∀ (x y: Fin 5)(z: Fin (Spec.w 6)), bs1[Spec.Keccak.StateArray.encodeIndex x y z]! = bs2[Spec.Keccak.StateArray.encodeIndex x y z]!)
: bs1 = bs2
:= by
  apply List.ext_getElem
  · simp [len_bs1, len_bs2]
  intro idx idx_lt _
  simp [len_bs1] at idx_lt
  have ⟨x, y, z, encode_xyz⟩ := IR.decode_surjective idx idx_lt
  simp [←encode_xyz, ←getElem!_pos, List.getElem!_encodeIndex_toBits]
  apply point_eq

@[progress]
theorem algos.iota.spec(ir: Std.Usize)(input: StateArray)
: ir.val < 24
→ ∃ output,
  iota ir input = .ok output ∧
  output.toBits = (Spec.Keccak.ι (iᵣ:= ir.val) input.toSpec).toBits
:= by
  intro ir_lt
  rw [iota]
  simp only [Std.toResult, Std.bind_tc_ok, StateArray.toSpec]
  progress*
  simp [*, Std.Array.toBits, Spec.Keccak.ι]
  apply List.ext_toBits
  · simp +decide [List.length_toBits]
  · simp
  intro x y z
  rw [Fin.getElem!_fin, IR.encodeIndex_spec, List.getElem!_encodeIndex_toBits (z_lt := z.isLt)]
  rw [Spec.Keccak.StateArray.getElem!_toBits_encodeIndex, Spec.Keccak.StateArray.get_ofFn]
  if cond: x = 0 ∧ y = 0 then
    simp +decide [cond, List.length_toBits, List.get_toStateArray, List.getElem!_encodeIndex_toBits, Std.UScalar.getElem!_xor_toBits]
    rw [IOTA_RC.spec ir ir_lt]
    simp [←getElem!_pos]
  else
    simp only [not_and_or] at cond
    obtain h | h := cond
    all_goals (
      simp [h]
      simp +decide [cond, List.length_toBits, List.get_toStateArray, List.getElem!_encodeIndex_toBits]
    )
