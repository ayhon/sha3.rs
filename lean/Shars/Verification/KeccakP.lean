import Aeneas
import Sha3.Spec
import Shars.BitVec
import Shars.Definitions.Algos
import Shars.Verification.Theta
import Shars.Verification.Rho
import Shars.Verification.Pi
import Shars.Verification.Chi
import Shars.Verification.Iota
import Shars.Verification.ListIR

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

def Spec.Keccak.P.loop.refinement(l: Fin 7)(nᵣ: Nat)(S: BitVec (Spec.b l))
: P  l nᵣ S = (P.loop l nᵣ (StateArray.ofBitVec S) 0).toBitVec
:= by congr


@[progress]
theorem algos.keccak_p_aux_loop.spec(input: StateArray)(ir: Std.Usize)
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

    simp +arith [*, Spec.Keccak.P.loop, SRRange.foldl_range'_eq_foldWhile]
    conv => rhs; rw [SRRange.foldWhile_step (h := by simpa using ir_lt)]
    congr
    scalar_tac
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
theorem algos.keccak_p.spec(input: Aeneas.Std.Array Bool 1600#usize)
: ∃ output,
  keccak_p input = .ok output ∧
  output.val.toBitVec.cast (by simp [Spec.b, Spec.w]) = Spec.Keccak.P 6 24 (input.val.toBitVec.cast (by simp [Spec.b, Spec.w]))
:= by
  rw [keccak_p, keccak_p_aux]
  progress as ⟨res, res_post⟩
  replace res_post := congrArg (f := Spec.Keccak.StateArray.toBitVec) res_post
  simp [StateArray.toSpec] at res_post
  simp [Spec.Keccak.P.loop.refinement, res_post]

@[progress]
theorem algos.keccak_p.spec'(input: Aeneas.Std.Array Bool 1600#usize)
: ∃ output,
  keccak_p input = .ok output ∧
  output.val = ListIR.list_keccak_p input.val
:= by
  rw [keccak_p, keccak_p_aux]
  progress as ⟨res, res_post⟩
  replace res_post := congrArg (f := BitVec.toList ∘ Spec.Keccak.StateArray.toBitVec) res_post
  simp [StateArray.toSpec] at res_post
  simp [*, ListIR.list_keccak_p, Spec.Keccak.P.loop.refinement, BitVec.setWidth_eq_cast, Spec.b, Spec.w, res_post]
