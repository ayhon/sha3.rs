import Aeneas
import Sha3.Spec
import Shars.BitVec
import Shars.Definitions.Simple
import Shars.Verification.Simple.Theta
import Shars.Verification.Simple.Rho
import Shars.Verification.Simple.Pi
import Shars.Verification.Simple.Chi
import Shars.Verification.Simple.Iota

set_option maxHeartbeats 10000000
attribute [-simp] List.getElem!_eq_getElem?_getD
attribute [simp] Aeneas.Std.Slice.set

open Aeneas hiding Std.Array
open Std.alloc.vec 


@[progress]
theorem simple.round.spec(ir: Std.Usize)(input: StateArray)
: ir.val < 24
→ ∃ output,
  round input ir = .ok output ∧
  output.toSpec = Spec.Keccak.Rnd input.toSpec ir.val
:= by
  intro ir_valid
  rw [round]
  progress*
  simp [Spec.Keccak.Rnd, *]

def Spec.Keccak.P.loop(l: Fin 7)(nᵣ: Nat)(S: StateArray l)(start: Nat) := Id.run do
  let mut A := S
  for iᵣ in [(12 + 2*↑l) - nᵣ+ start: (12 + 2*↑l) - 1 + 1] do
    A := Rnd A iᵣ
  return A

def Spec.Keccak.P.loop.spec(l: Fin 7)(nᵣ: Nat)(S: BitVec (Spec.b l))
: P  l nᵣ S = (P.loop l nᵣ (StateArray.ofBitVec S) 0).toBitVec
:= by congr

@[progress]
theorem simple.keccak_p_aux_loop.spec(input: StateArray)(ir: Std.Usize)
: ir.val ≤ 24
→ ∃ output,
  keccak_p_aux_loop input ir = .ok output ∧
  output.toSpec = Spec.Keccak.P.loop 6 24 input.toSpec ir.val
:= by 
  intro ir_loop_bound
  rw [keccak_p_aux_loop]
  split
  case isTrue ir_lt =>
    let* ⟨ a1, a1_post ⟩ ← round.spec
    let* ⟨ ir1, ir1_post ⟩ ← Std.Usize.add_spec
    let* ⟨ res, res_post ⟩ ← spec
    rw [res_post, a1_post, ir1_post]
    simp [Spec.Keccak.P.loop]
    symm
    simp [←Nat.add_sub_assoc ir_loop_bound, ←Nat.add_sub_assoc (‹ir.val ≤ 23›')]
    rw [Nat.add_comm, ←Nat.add_assoc, Nat.add_comm, ←Nat.add_assoc, Nat.add_sub_cancel]
    rw [SRRange.foldWhile_step (h := by simpa using ir_lt)] 
  case isFalse ir_oob =>
    simp [‹ir.val = 24›', Spec.Keccak.P.loop]
termination_by 24 - ir.val
decreasing_by scalar_decr_tac

theorem Spec.Keccak.StateArray.ofBitVec_inj(bv bv' : BitVec (Spec.b l))
: bv = bv' ↔ StateArray.ofBitVec bv = StateArray.ofBitVec bv'
:= by apply Iff.intro <;> intro h <;> simpa using h

theorem Spec.Keccak.StateArray.ofBitVec_toBitVec(S: StateArray l)
: { toBitVec := S.toBitVec } = S
:= by simp

@[progress]
theorem simple.keccak_p.spec(input: Aeneas.Std.Array Bool 1600#usize)
: ∃ output,
  keccak_p input = .ok output ∧
  output.val.toBitVec.cast (by simp [Spec.b, Spec.w]) = Spec.Keccak.P 6 24 (input.val.toBitVec.cast (by simp [Spec.b, Spec.w]))
:= by
  rw [keccak_p, keccak_p_aux]
  progress as ⟨res, res_post⟩
  cases bv_val: res.toSpec 
  rw [bv_val] at res_post
  case ofBitVec bv =>
    simp [StateArray.toSpec] at bv_val
    rw [bv_val, Spec.Keccak.P]
    apply Spec.Keccak.StateArray.ofBitVec_inj bv _ |>.mpr
    rw [res_post]
    congr
    -- NOTE: Does `congr` unfold definitions?

@[progress]
theorem simple.keccak_p.spec'(input: Aeneas.Std.Array Bool 1600#usize)
: ∃ output,
  keccak_p input = .ok output ∧
  output.length = input.length ∧
  output.val = (Spec.Keccak.P 6 24 (input.val.toBitVec.cast (by simp [Spec.b, Spec.w]))).toList
:= by
  rw [keccak_p, keccak_p_aux]
  progress as ⟨res, res_post⟩
  conv at res_post => arg 2; rw [StateArray.toSpec]
  rw [Spec.Keccak.P.loop.spec]
  rw [←res_post]
  simp [StateArray.toSpec, BitVec.toList]
  apply List.ext_getElem
  · simp [Spec.b, Spec.w]
  intro j j_idx_res j_idx_other
  simp only [List.getElem_map, List.getElem_finRange]
  simp only [BitVec.getElem_cast, BitVec.getElem_ofBoolListLE, Fin.cast_mk]
