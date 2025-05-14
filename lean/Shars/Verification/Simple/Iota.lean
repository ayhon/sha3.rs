import Aeneas
import Shars.BitVec
import Shars.Definitions.Simple
import Sha3.Spec
/- import Sha3.Utils -/
import Aeneas.SimpLists.Init
import Sha3.Facts
import Init.Data.Vector.Lemmas
import Init.Data.Nat.Basic
import Shars.Verification.Simple.Constants
import Shars.Verification.Simple.Utils
import Shars.Verification.Simple.Auxiliary

set_option maxHeartbeats 1000000

open Aeneas hiding Std.Array
open Std.alloc.vec

theorem simple.IOTA_RC_POINTS.spec
: ∀ t < 255, IOTA_RC_POINTS.val[t]! = Spec.Keccak.ι.rc t
:= by native_decide

attribute [scalar_tac_simps] Nat.mod_mod Fin.ofNat'

@[progress]
theorem simple.iota_rc_point.spec(t: Std.Usize)
: ∃ output,
  iota_rc_point t = .ok output ∧
  output = Spec.Keccak.ι.rc t.val
:= by
  simp [iota_rc_point]
  progress*
  simp [*, IOTA_RC_POINTS.spec (t.val % 255) (by scalar_tac), Spec.Keccak.ι.rc_mod_eq_rc]

def simple.iota_rc_init_loop.ref(ir: Nat)(rc: BitVec (Spec.w 6))(j: Nat) :=
  if j <= 6
  then
    let i := 7 * ir
    let i1 := j + i
    let b := Spec.Keccak.ι.rc i1
    let i2 := 1 <<< j
    let i3 := i2 - 1
    let rc1 := rc.set i3 b
    let j1 := j + 1
    iota_rc_init_loop.ref ir rc1 j1
  else rc
termination_by 7 - j

theorem simple.iota_rc_init_loop.ref_spec(ir : Std.Usize) (input : Aeneas.Std.Array Bool 64#usize)(j: Std.Usize)
: ir.val < 24
→ j.val ≤ 6 + 1
→ ∃ output,
  iota_rc_init_loop ir input j = .ok output ∧
  output.val.toBitVec.cast (by simp [Spec.w]) = simple.iota_rc_init_loop.ref ir.val (input.val.toBitVec.cast (by simp [Spec.w])) j.val
:= by
  intro ir_lt j_loop_bound
  rw [iota_rc_init_loop, iota_rc_init_loop.ref]
  split
  case isTrue j_lt =>
    let* ⟨ i, i_post ⟩ ← Std.Usize.mul_spec
    let* ⟨ i1, i1_post ⟩ ← Std.Usize.add_spec
    let* ⟨ b, b_post ⟩ ← iota_rc_point.spec
    simp [i1_post, i_post] at b_post
    let* ⟨ i2, i2_post_1, i2_post_2 ⟩ ← Std.Usize.one_ShiftLeft_spec
    · have:= Std.UScalarTy.Usize_numBits_le
      scalar_tac
    let* ⟨ i3, i3_post ⟩ ← Std.Usize.sub_spec
    have i3_idx: i3.val < input.length := by
      simp [*]
      calc  2 ^ ↑j - 1
          _ < 2 ^ ↑j := Nat.pred_lt (Nat.ne_of_gt (Nat.two_pow_pos j.val))
          _ ≤ 2 ^ 6 := Nat.pow_le_pow_right Nat.two_pos (by simpa using j_lt)
    let* ⟨ rc1, rc1_post ⟩ ← Std.Array.update_spec
    let* ⟨ j1, j1_post ⟩ ← Std.Usize.add_spec
    let* ⟨ res, res_post ⟩ ← ref_spec
    -- END PROGRESS
    rw [res_post, ←BitVec.cast_set (i_idx := ?first)]
    case first =>
      simp [Nat.shiftLeft_eq, NatCast.natCast, Fin.ofNat']
      rw [Nat.mod_eq_of_lt] <;> simpa [*] using i3_idx
    rw [rc1_post, List.toBitVec, Std.Array.set, BitVec.ofBoolListLE_set (i_idx := by simpa using i3_idx)]
    simp
    simp_ifs
    congr 3
    simp [*]
    rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.mod_eq_of_lt]
    simpa [*] using i3_idx
  case isFalse => simp [‹j.val = 7›']
termination_by 7 - j.val
decreasing_by scalar_decr_tac

theorem simple.iota_rc_init_loop.ref.foldWhile_spec(iᵣ: Nat)(input: BitVec (Spec.w 6))(j: Nat)
: iota_rc_init_loop.ref iᵣ input j = SRRange.foldWhile
    (i    := j)
    (max  := 6 + 1)
    (step := 1) (hStep := Nat.one_pos)
    (init := input)
    (f    := fun input j => input.set (↑(1 <<< j - 1)) (Spec.Keccak.ι.rc (j + 7 * iᵣ)))
:= by
  rw [ref, SRRange.foldWhile]
  if h: j < 7 then
    simp only
    simp [h, ‹j ≤ 6›']
    rw [simple.iota_rc_init_loop.ref.foldWhile_spec]
  else simp [h, ‹¬ (j ≤ 6)›']

def Spec.Keccak.ι.RC.loop (iᵣ: Nat)(init: BitVec (w 6))(start: Nat): BitVec (w 6) := Id.run do
  let mut RC := init
  for j in List.finRange (6 + 1) |>.drop start do
    have j_valid_idx := calc  2 ^ ↑j - 1
        _ < 2 ^ ↑j := Nat.pred_lt (Nat.ne_of_gt (Nat.two_pow_pos j.val))
        _ ≤ 2 ^ 6 := Nat.pow_le_pow_right Nat.two_pos <| Fin.is_le j
    RC := RC.set ⟨2^j.val - 1, j_valid_idx⟩ (ι.rc (↑j + 7*iᵣ))
  return RC

theorem Spec.Keccak.ι.RC.loop_refinement(iᵣ: Nat)
: RC.loop iᵣ (0#(w 6)) 0 = RC iᵣ
:= by simp [loop, RC]; congr

theorem Spec.Keccak.ι.RC.loop.foldl_spec(iᵣ: Nat)(init: BitVec (w 6))(start: Nat)
: RC.loop iᵣ init start =
    List.foldl (fun RC j => RC.set! (2^j - 1) (ι.rc (j + 7*iᵣ))) init (List.range (6 + 1) |>.drop start)
:= by
  simp [RC.loop]
  rw [
    ←List.val_finRange_eq_range 7,
    ←List.map_drop,
    ←List.foldl_of_foldl_map (f := Fin.val)
  ]
  ext RC j : 2
  rw [BitVec.set!_eq_set]

theorem Aeneas.SRRange.foldWhile_eq_foldWhile'{α : Type u}
(i max step : Nat) (hStep : 0 < step) (f : α → Nat → α) (init : α)(start: Nat)
: (cond: start ≤ i ∧ (i - start) % step = 0)
→ foldWhile max step hStep f i init = SRRange.foldWhile' {
    start := start
    stop  := max
    step  := step
    step_pos := hStep
  } (fun acc e _ => f acc e) i init (hi := by simp [cond])
:= by
  intro ⟨start_le, start_modeq_i⟩
  unfold foldWhile foldWhile'
  simp
  split
  · rw [Aeneas.SRRange.foldWhile_eq_foldWhile']
    constructor
    · omega
    · rw [Nat.add_comm i, Nat.add_sub_assoc (start_le)]
      simp [start_modeq_i]
  · rfl
termination_by max - i

def simple.iota_rc_init_loop.foldWhile.spec(iᵣ: Nat)(init: BitVec (Spec.w 6))(start: Nat)
: SRRange.foldWhile
    (i    := start)
    (max  := 6 + 1)
    (step := 1) (hStep := Nat.one_pos)
    (init := init)
    (f    := fun input j => BitVec.set (1 <<< j - 1).cast (Spec.Keccak.ι.rc (j + 7 * iᵣ)) input)
= Spec.Keccak.ι.RC.loop iᵣ init start
:= by
  rw [Spec.Keccak.ι.RC.loop.foldl_spec, List.drop_range, SRRange.foldl_range'_eq_foldWhile (hStep := Nat.one_pos)]
  simp
  if start_idx: start < 7 then
    rw [‹start  + (7 - start) = 7›']
    rw [SRRange.foldWhile_eq_foldWhile' (start:=start) (cond := by simp)]
    rw [SRRange.foldWhile_eq_foldWhile' (start:=start) (cond := by simp)]
    congr
    ext input j j_idx : 3
    rw [←BitVec.set!_eq_set]
    congr 2
    simp
    simp only [Nat.shiftLeft_eq, Nat.one_mul]
    simp [Membership.mem] at j_idx
    have j_valid_idx := calc  2 ^ j - 1
        _ < 2 ^ j := Nat.pred_lt (Nat.ne_of_gt (Nat.two_pow_pos j))
        _ ≤ 2 ^ 6 := Nat.pow_le_pow_right Nat.two_pos (by scalar_tac)
    rw [Nat.mod_eq_of_lt]; simpa using j_valid_idx
  else
    rw [SRRange.foldWhile_id (h := start_idx), SRRange.foldWhile_id (h := by simpa using start_idx)]

@[progress]
theorem simple.iota_rc_init_loop.spec(ir : Std.Usize) (input : Aeneas.Std.Array Bool 64#usize)(i: Std.Usize)
: ir.val < 24
→ i.val ≤ 6 + 1
→ ∃ output,
  simple.iota_rc_init_loop ir input i = .ok output ∧
  output.val.toBitVec.cast (by simp [Spec.w]) = Spec.Keccak.ι.RC.loop ir.val (input.val.toBitVec.cast (by simp [Spec.w])) i.val
:= by
  intro ir_lt i_loop_bound
  let* ⟨ output, output_post⟩ ← iota_rc_init_loop.ref_spec
  rw [
    output_post,
    simple.iota_rc_init_loop.ref.foldWhile_spec,
    simple.iota_rc_init_loop.foldWhile.spec,
  ]

set_option maxRecDepth 1000000 in
@[progress]
theorem simple.iota_rc_init.spec(ir: Std.Usize)
: ir.val < 24
→ ∃ output,
  simple.iota_rc_init ir (Std.Array.repeat 64#usize false) = .ok output ∧
  output.val.toBitVec.cast (by simp [Spec.w]) = (Spec.Keccak.ι.RC ir.val : BitVec (Spec.w 6))
:= by
  intro ir_lt
  simp [iota_rc_init]
  let* ⟨output , output_post⟩ ← iota_rc_init_loop.spec
  rw [output_post, ←Spec.Keccak.ι.RC.loop_refinement]
  rfl

@[progress]
theorem simple.iota_a_loop.spec(res : StateArray) (a : StateArray) (rc : Aeneas.Std.Array Bool 64#usize)(z: Std.Usize)
: ∃ output,
  simple.iota_a_loop res a rc z = .ok output ∧
  ∀ (x y: Fin 5)(z': Fin (Spec.w 6)),
  output.toSpec.get x y z' =
    if x = 0 ∧ y = 0 ∧ z.val ≤ z'.val then
      a.toSpec.get 0 0 z' ^^ rc.val.toBitVec[z'.val]!
    else
      res.toSpec.get x y z'
:= by
  rw [simple.iota_a_loop]
  split
  case isTrue =>
    let* ⟨ b, b_post ⟩ ← StateArray.index.spec
    let* ⟨ b1, b1_post ⟩ ← Std.Array.index_usize_spec
    let* ⟨ b2, b2_post ⟩ ← binxor.spec
    simp [b_post, b1_post] at b2_post
    let* ⟨ old_res, set_res, old_res_post, set_res_post ⟩ ← StateArray.index_mut.spec
    let* ⟨ z1, z1_post ⟩ ← Std.Usize.add_spec
    let* ⟨ rest, rest_post ⟩ ← spec
    simp [*] at rest_post
    intro x y z'
    rw [rest_post]
    split_all
    · simp [Spec.Keccak.StateArray.get_set]
    · scalar_tac
    · simp [Spec.Keccak.StateArray.get_set]
      have zz' := ‹z.val = z'.val›'
      simp only [Fin.isValue, zz', Fin.cast_val_eq_self, and_true]--, ite_eq_left_iff, not_and]
      simp_ifs
    · rw [Spec.Keccak.StateArray.get_set]
      have: ¬ (x = 0 ∧ y = 0 ∧ z' = z.val.cast) := by
        -- TODO: Could we modify `scalar_tac` so that it handles this case?
        -- The issue is with `Fin` inequalities being hiden behind `And`, `Or` or `Not`.
        -- It would be nice to have `scalar_tac` transform these using the lemmas
        --  · Fin.val_fin_le
        --  · Fin.val_inj
        -- I was thinking of using a `simproc`, but I don't think these work with
        -- implications, since they're supposed to do rewritings.
        -- Perhaps I could have it
        rename_i h1 h2
        simp [not_and_or, -not_and] at h1 h2 ⊢
        rcases h1 with (h1 | h1 | h1) <;> try simp [h1]
        rcases h2 with (h1 | h1 | h1) <;> try simp [h1]
        right;right
        intro aux
        replace aux := Fin.val_eq_of_eq aux
        simp [Nat.mod_eq_of_lt, ‹z.val < Spec.w 6›'] at aux
        scalar_tac
      simp_ifs
  case isFalse z_oob =>
    simp at z_oob ⊢
    intro x y z'
    simp_ifs
termination_by (Spec.w 6 + 1) - z.val
decreasing_by scalar_decr_tac

@[progress]
theorem simple.iota.spec(ir: Std.Usize)(input: StateArray)
: ir.val < 24
→ ∃ output,
  iota ir input = .ok output ∧
  output.toSpec = Spec.Keccak.ι (iᵣ:= ir.val) input.toSpec
:= by
  intro ir_lt
  simp [iota, iota_a, ClonesimpleStateArray.clone]
  let* ⟨rc, rc_post⟩ ← iota_rc_init.spec
  let* ⟨res, res_post⟩ ← iota_a_loop.spec
  ext x y z
  simp only [Spec.Keccak.ι, Spec.Keccak.StateArray.get_ofFn, res_post]
  split
  case isTrue h =>
    simp only [Fin.isValue, h, id_eq, Id.run, Fin.getElem_fin, Id.pure_eq, Spec.Keccak.StateArray.get_ofFn, Bool.bne_right_inj]
    replace rc_post := BitVec.cast_left _ rc_post
    rw [rc_post, ←getElem_eq_getElem! (h := by scalar_tac)]
    simp
  case isFalse h =>
    simp
    split
    · simp [*] at *
      simp [*] at *
    rename_i h; simp at h; obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
