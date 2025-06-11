import Aeneas
import Shars.BitVec
import Shars.ArrayExtract
import Shars.Definitions.Algos
import Sha3.Spec
import Aeneas.SimpLists.Init
import Sha3.Facts
import Init.Data.Vector.Lemmas
import Init.Data.Nat.Basic
import Init.Data.Array
import Shars.Verification.Utils
import Shars.Verification.Refinement
import Shars.Verification.Auxiliary
import Shars.Verification.KeccakP
-- import Shars.Verification.ListIR

set_option maxHeartbeats 100000
attribute [-simp] List.getElem!_eq_getElem?_getD
attribute [ext (iff:=false)] List.ext_getElem!

open Aeneas

-- attribute [scalar_tac_simps] Nat.pos_of_neZero

/-- The shape of the sponge_squeeze algorithm, operating on bits -/
def algos.sponge_squeeze.panic_free(r: Nat)[NeZero r](dst s: List Bool)(offset: Nat): List Bool :=
  -- assert! s.length ≥ r
  if offset + r < dst.length then
    let dst' := dst.setSlice! offset (s.take r)
    let s' := IR.keccak_p s
    panic_free r dst' s' (offset + r)
  else
    let nb_left := dst.length - offset
    dst.setSlice! offset (s.take nb_left)
termination_by dst.length - offset
decreasing_by scalar_decr_tac

@[simp] theorem algos.sponge.squeeze.length_panic_free(r: Nat)(dst s: List Bool)(offset: Nat)
  (r_pos: r > 0)
: have: NeZero r := {out := Nat.ne_zero_of_lt r_pos}
  (algos.sponge_squeeze.panic_free r dst s offset).length = dst.length
:= by
  unfold algos.sponge_squeeze.panic_free
  simp only [↓reduceIte]
  split
  case isTrue h =>
    rw [algos.sponge.squeeze.length_panic_free]
    all_goals simp +decide [*, le_of_lt, Spec.b, Spec.w]
  case isFalse h =>
    simp
termination_by dst.length - offset
decreasing_by scalar_tac

-- @[simp]
theorem List.toBits_slice(ls: List (Std.UScalar ty))
: (ls.slice i j).toBits = ls.toBits.slice (i * ty.numBits) (j * ty.numBits)
:= by simp only [slice, toBits_take, toBits_drop, Nat.sub_mul]

@[simp]
theorem List.setSlice!_zero_of_length_le(ls s: List α)
: ls.length ≤ s.length
→ ls.setSlice! 0 s = s.take (ls.length)
:= by intro cond; simp [List.setSlice!, cond]

theorem List.length_slice(ls: List α): (ls.slice a b).length = (b - a) ⊓  (ls.length - a) := by simp [List.slice]

attribute [scalar_tac ls.toBits] List.length_toBits
attribute [scalar_tac_simps] Std.UScalarTy.numBits

-- theorem algos.sponge_squeeze.panic_free.extracted_1 (r i : Std.Usize) (dst : Std.Slice Std.U8) (s : StateArray)
--   (r_pos : 0 < (↑r : ℕ))

--   (i1 : Std.Usize)
--   (i1_post : (↑i1 : ℕ) = (↑i : ℕ) + (↑r : ℕ))
--   (h : (↑i1 : ℕ) < (↑dst : List Std.U8).length) -- Needed by A and C

--   (__discr_1 : Std.Slice Std.U8) (__discr_2 : Std.Slice Std.U8 → Std.Slice Std.U8) -- Needed by ↓ and 2↓
--   (__discr_post_1 : (↑__discr_1 : List Std.U8) = List.slice (↑i : ℕ) (↑i1 : ℕ) (↑dst : List Std.U8)) -- Needed by A
--   (__discr_post_2 : -- Needed by B
--     ∀ (u : Std.Slice Std.U8),
--       u.length = (↑i1 : ℕ) - (↑i : ℕ) →
--         (↑(__discr_2 u) : List Std.U8) = (↑dst : List Std.U8).setSlice! (↑i : ℕ) (↑u : List Std.U8))

--   (s2 : Std.Slice Std.U8) -- Needed by ↓
--   (s2_post : s2.toBits = __discr_1.toBits.setSlice! 0 (Std.Array.toBits s)) -- Needed by A
-- : (↑i1 : ℕ) ≤ (__discr_2 s2).length := by
--     have: s2.length = r := by scalar_tac -- A
--     have: (__discr_2 s2).length = dst.length := by scalar_tac
--     scalar_tac -- C
--     done

set_option pp.coercions.types true in
set_option maxHeartbeats 1000000 in
/-- We prove that the algorithm, under certain preconditions, does not panic -/
theorem algos.sponge_squeeze.panic_free.refinement(r i d: Std.Usize)
  (dst: Std.Slice Std.U8)(s: StateArray)
: (r_bnd: 0 < r.val ∧ r.val < 200)
→ i ≤ dst.length
→ dst.length + r.val < Std.Usize.max
→ d = Std.Usize.ofNatCore dst.length (by have := dst.property; scalar_tac)
→ let _: NeZero r.val := {out:= Nat.ne_zero_of_lt r_bnd.left}
  ∃ output,
  sponge_squeeze_loop r dst s i d = .ok output ∧
  output.toBits = panic_free (8*r.val) dst.toBits s.toBits (8*i.val)
:= by
  rintro ⟨r_pos, r_bnd⟩ i_loop_bnd no_overflow rfl
  unfold algos.sponge_squeeze_loop panic_free
  simp [DerefalgosStateArrayArrayU6425.deref, Std.toResult,
        Std.core.array.Array.index,       Std.core.array.Array.index_mut,
        Std.core.slice.index.Slice.index, Std.core.slice.index.Slice.index_mut,
        Aeneas.Std.core.ops.index.Index.index,
        Std.core.ops.index.IndexSliceInst,
      ]
  progress* by simp; scalar_tac
  · have: s2.length = r := by scalar_tac
    have: (__discr_2 s2).length = dst.length := by simp [*]
    progress as ⟨res, res_post⟩
    simp [*, le_of_lt]
    simp_ifs
    simp only [*, List.toBits_slice, Std.UScalarTy.numBits]
    rw [List.setSlice!_zero_of_length_le]; case a => simp [List.length_slice]; omega
    have: (List.slice (i.val * 8) ((i.val + r.val)* 8) dst.toBits).length = 8*r.val := by
      scalar_tac
    simp [*, this, IR.keccak_p, Nat.mul_add]
  · rw [__discr_post_2]
    case a =>
      have: s2.toBits.length = dst.toBits.length - 8*i := by simp +arith [*]
      simpa [Nat.mul_comm 8, ←Nat.sub_mul] using this
    simp [*]
    simp_ifs
    rw [List.setSlice!_zero_of_length_le]; case a => simp; scalar_tac
    simp [Nat.mul_comm 8]
termination_by dst.length - i.val
decreasing_by scalar_decr_tac

attribute [local scalar_tac_simps] not_le in
/-- This is a representation of squeeze which is closer to the Spec -/
def IR.squeeze(d: Nat)(r: Nat)[NeZero r](dst s: List Bool): List Bool :=
  if d ≤ dst.length then
    dst.take d
  else
    squeeze d r (dst ++ s.setWidth r) (IR.keccak_p s)
termination_by d - dst.length
decreasing_by scalar_decr_tac

@[simp]
theorem IR.length_squeeze(d: Nat)(r: Nat)[NeZero r](dst s: List Bool)
: (squeeze d r dst s).length = d
:= by
  unfold squeeze
  split
  case isTrue h => simp [h]
  case isFalse h => rw [IR.length_squeeze]
termination_by d - dst.length
decreasing_by scalar_decr_tac

private theorem List.getElem!_take_eq_ite[Inhabited α](ls: List α)(n i: Nat)
: (ls.take n)[i]! = if i < n then ls[i]! else default
:= by split <;> simp_lists

private theorem List.getElem!_setSlice!_eq_ite[Inhabited α](ls slice: List α)(offset i: Nat)
: i < ls.length
→ offset < ls.length
→ (ls.setSlice! offset slice)[i]! =
  if i < offset then ls[i]!
  else if i  < offset + slice.length then slice[i - offset]!
  else ls[i]!
:= by
  intro i_idx offset_idx
  split_ifs <;> simp_lists

attribute [local simp_lists_simps] List.getElem!_take_eq_ite in
set_option maxHeartbeats 1000000 in
/-- We show that the Spec-similar function is equivalent to the algo-similar function -/
theorem algos.sponge_squeeze.panic_free.spec(r: Nat)
  (r_bnd: 0 < r ∧ r < 1600)
  (dst s: List Bool)(offset : Nat)
: s.length = 1600
→ offset ≤ dst.length
→ have : NeZero r := {out := Nat.ne_zero_of_lt r_bnd.left}
  panic_free r dst s offset = IR.squeeze dst.length r (dst.take offset) s
:= by
  obtain ⟨r_pos, r_lt⟩ := r_bnd
  intro len_s offset_idx
  simp
  unfold panic_free IR.squeeze
  simp [*, le_of_lt]
  split
  case isTrue next_offset_lt =>
    simp_ifs
    rw [spec r]
    all_goals simp +decide [*, le_of_lt]
    congr 1
    apply List.ext_getElem <;> simp [*, le_of_lt, ←getElem!_pos]
    intro i i_lt
    simp [List.setSlice!, *]
    assume i < offset + r; case otherwise => simp_lists
    simp_lists [List.getElem!_take_eq_ite, List.getElem!_setSlice!_eq_ite]
  case isFalse end_of_processing =>
    unfold IR.squeeze
    simp_ifs
    split
    · simp [‹offset = dst.length›', List.setSlice!]
    · ext i
      · simp [*, List.setSlice!]; scalar_tac
      assume i < dst.length; case otherwise => simp_lists
      simp_lists [List.getElem!_take_eq_ite, List.getElem!_setSlice!_eq_ite]
      simp_ifs
termination_by dst.length - offset
decreasing_by scalar_decr_tac

@[simp]
theorem Aeneas.Std.Slice.val_drop{T: Type}(s: Slice T)(k: Usize)
: (s.drop k).val = s.val.drop k.val
:= by simp [Slice.drop]

attribute [simp_ifs_simps] dite_eq_ite
@[simp_ifs_simps]
theorem dite_eq_then {α : Sort u} (c : Prop) [h : Decidable c] (t : c → α) (e : ¬c → α) (h : c) :
  dite c t e = t h := by simp only [↓reduceDIte, h]

@[simp_ifs_simps]
theorem dite_eq_else {α : Sort u} (c : Prop) [h : Decidable c] (t : c → α) (e : ¬c → α) (h : ¬ c) :
  dite c t e = e h := by simp only [↓reduceDIte, h]

@[simp]
theorem Vector.toList_setWidth[Inhabited α](v: Vector α n)(m: Nat)
: (v.setWidth m).toList = v.toList.setWidth m
:= by simp [Vector.setWidth, List.setWidth]

def IR.squeeze.refinement(r: { x // 0 < x ∧ x < Spec.b 6 })
    (Z: Spec.Bitstring m)
    (S: Spec.Bitstring (Spec.b 6))
: have: NeZero r.val := {out:= by omega}
  (Spec.sponge.squeeze (d := d) (f := Spec.Keccak.P 6 24) r Z S).toList =
  (squeeze d r Z.toList S.toList)
:= by
  unfold squeeze Spec.sponge.squeeze
  simp
  split
  case isTrue base_case =>
    simp [base_case, Vector.setWidth]
  case isFalse _ =>
    rw [IR.squeeze.refinement]
    simp [IR.keccak_p, List.toStateArray]
termination_by d - m
decreasing_by scalar_decr_tac

/-- The final theorem, putting everything together -/
theorem algos.sponge_squeeze.spec(r: Std.Usize)
  (dst: Std.Slice Std.U8)(s: StateArray)
: (r_bnd: 0 < r.val ∧ r.val < 200)
→ dst.length + r.val < Std.Usize.max
→ have _: NeZero r.val := {out:= Nat.ne_zero_of_lt r_bnd.left}
  ∃ output,
  sponge_squeeze r dst s = .ok output ∧
  output.toBits = IR.squeeze dst.toBits.length (8*r) [] s.toBits
:= by
  intros
  rw [sponge_squeeze]
  progress with algos.sponge_squeeze.panic_free.refinement as ⟨res, res_post⟩
  rw [res_post]
  rw [algos.sponge_squeeze.panic_free.spec]
  all_goals simp [*]; try omega
