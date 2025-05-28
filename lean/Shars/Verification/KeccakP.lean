import Aeneas
import Sha3.Spec
import Shars.BitVec
import Shars.Definitions.Algos
import Shars.Verification.Theta
import Shars.Verification.Rho
import Shars.Verification.Pi
import Shars.Verification.Chi
import Shars.Verification.Iota
/- import Shars.Verification.ListIR -/

set_option maxHeartbeats 10000000
attribute [-simp] List.getElem!_eq_getElem?_getD
attribute [simp] Aeneas.Std.Slice.set

open Aeneas hiding Std.Array
open Std.alloc.vec


@[progress]
theorem algos.round.spec(ir: Std.Usize)(input: StateArray)
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

def Spec.Keccak.P.loop.refinement(l: Fin 7)(nᵣ: Nat)(S: Bitstring (Spec.b l))
: P  l nᵣ S = (P.loop l nᵣ (StateArray.ofVector S) 0).toVector
:= by congr

@[progress]
theorem algos.keccak_p_loop.spec(input: StateArray)(ir: Std.Usize)
: ir.val ≤ 24
→ ∃ output,
  keccak_p_loop input ir = .ok output ∧
  output.toBits = (Spec.Keccak.P.loop 6 24 input.toSpec ir.val).toBits
:= by
  intro ir_loop_bound
  rw [keccak_p_loop]
  progress*
  · simp +arith [*, Spec.Keccak.P.loop, SRRange.foldl_range'_eq_foldWhile]
    conv => rhs; rw [SRRange.foldWhile_step (h := by scalar_tac)]
    congr
    scalar_tac
  · simp +decide [‹ir.val = 24›', Spec.Keccak.P.loop, Spec.Keccak.StateArray.toBits_toStateArray]
termination_by 24 - ir.val
decreasing_by scalar_decr_tac

@[progress]
theorem algos.keccak_p.spec(input: StateArray)
: ∃ output,
  keccak_p input = .ok output ∧
  output.toBits = (Spec.Keccak.P 6 24 (input.toSpec.toVector)).toList
:= by
  rw [keccak_p]
  progress as ⟨res, res_post⟩
  simp [res_post, Spec.Keccak.P.loop.refinement, res_post]
