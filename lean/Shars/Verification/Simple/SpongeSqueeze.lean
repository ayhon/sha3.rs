import Aeneas
import Shars.BitVec
import Shars.ArrayExtract
import Shars.Definitions.Simple
import Sha3.Spec
import Aeneas.SimpLists.Init
import Sha3.Facts
import Init.Data.Vector.Lemmas
import Init.Data.Nat.Basic
import Init.Data.Array
import Shars.Verification.Simple.Utils
import Shars.Verification.Simple.Refinement
import Shars.Verification.Simple.Auxiliary
import Shars.Verification.Simple.KeccakP
import Shars.Verification.Simple.ListIR

set_option maxHeartbeats 100000
attribute [-simp] List.getElem!_eq_getElem?_getD
attribute [ext (iff:=false)] List.ext_getElem!

open Aeneas

-- attribute [scalar_tac_simps] Nat.pos_of_neZero

def simple.sponge_squeeze.panic_free(r: Nat)[NeZero r](dst s: List Bool)(offset: Nat): List Bool :=
  assert! s.length ≥ r
  if offset + r < dst.length then
    let dst' := dst.replace_slice offset (offset + r) (s.take r)
    let s' := ListIR.list_keccak_p s
    panic_free r dst' s' (offset + r)
  else
    let nb_left := dst.length - offset
    dst.replace_slice offset (offset + nb_left) (s.take nb_left)
termination_by dst.length - offset
decreasing_by simp [List.replace_slice]; scalar_tac

def simple.sponge.squeeze.length_panic_free(r: Nat)(dst s: List Bool)(offset: Nat)
  (r_pos: r > 0)
  (r_lt: r < 1600)
: s.length ≥ r
→ have: NeZero r := {out := Nat.not_eq_zero_of_lt r_pos}
  (simple.sponge_squeeze.panic_free r dst s offset).length = dst.length
:= by
  intro s_big_enough
  unfold simple.sponge_squeeze.panic_free
  simp only [s_big_enough, reduceIte]
  split
  case isTrue h =>
    rw [simple.sponge.squeeze.length_panic_free]
    case r_pos => assumption
    case r_lt => assumption
    case a => simp; omega
    simp [List.replace_slice, h, le_of_lt, s_big_enough, ←Nat.add_assoc, ‹offset ≤ dst.length›',]
  case isFalse h =>
    simp [List.replace_slice, h, le_of_lt, s_big_enough, ←Nat.add_assoc]
    simp only [Nat.min_def]
    simp_ifs
    split <;> simp at * <;> simp [*, Nat.sub_eq_zero_of_le, le_of_lt]
termination_by dst.length - offset
decreasing_by simp [List.replace_slice]; scalar_tac

attribute [local scalar_tac_simps] not_le in
def ListIR.sponge.squeeze(d: Nat)(r: Nat)[NeZero r](dst s: List Bool): List Bool :=
  if d ≤ dst.length then
    dst.take d
  else
    squeeze d r (dst ++ s.setWidth r) (ListIR.list_keccak_p s)
termination_by d - dst.length
decreasing_by scalar_decr_tac

@[simp]
theorem ListIR.sponge.length_squeeze(d: Nat)(r: Nat)[NeZero r](dst s: List Bool)
: (squeeze d r dst s).length = d
:= by
  unfold squeeze
  split
  case isTrue h => simp [h]
  case isFalse h =>
    rw [ListIR.sponge.length_squeeze]
termination_by d - dst.length
decreasing_by scalar_decr_tac


theorem List.getElem!_replace_slice[Inhabited α](ls ls2: List α)(s e: Nat)
: s ≤ e -- Proper range
→ e ≤ ls.length -- e goes up to end
→ s < ls.length -- s goes up to last
→ (ls.replace_slice s e ls2)[i]! =
    if       i < s              then ls[i]!
    else if  i - s < ls2.length then ls2[i - s]!
    else ls[i - (s + ls2.length) + e]!
:= by
  intros
  simp [replace_slice]
  split_ifs <;> simp_lists
  rw [Nat.add_comm, Nat.sub_add_eq]


attribute [scalar_tac_simps] List.length_setWidth

theorem List.getElem!_take_eq_ite[Inhabited α](ls: List α)(n i: Nat)
: (ls.take n)[i]! = if i < n then ls[i]! else default
:= by split <;> simp_lists


attribute [local simp_lists_simps] List.getElem!_take_eq_ite in
theorem simple.sponge_squeeze.panic_free.spec(r: Nat)
  (r_bnd: 0 < r ∧ r < 1600)
  (dst s: List Bool)(offset : Nat)
: s.length = 1600
→ offset ≤ dst.length
→ have : NeZero r := {out := Nat.not_eq_zero_of_lt r_bnd.left}
  panic_free r dst s offset = ListIR.sponge.squeeze dst.length r (dst.take offset) s
:= by
  intro len_s offset_idx
  simp
  unfold panic_free ListIR.sponge.squeeze
  simp_ifs
  simp
  split
  case isTrue next_offset_lt =>
    have: (List.replace_slice offset (offset + r) dst (List.take r s)).length = dst.length := by
      simp [List.replace_slice]; scalar_tac
    have: offset ≠ dst.length := by scalar_tac
    simp_ifs
    rw [spec r r_bnd]
    case a => simp
    case a => simp [*, le_of_lt]
    congr 1
    ext i
    · simp [*, le_of_lt]
    assume i < offset + r
    case otherwise => simp_lists
    simp_lists [List.getElem!_replace_slice]
  case isFalse next_offset_lt =>
    unfold ListIR.sponge.squeeze
    simp_ifs
    split
    · have: offset = dst.length := by scalar_tac
      simp [this, List.replace_slice]
    · ext i
      · simp [*, List.replace_slice]; scalar_tac
      simp_lists [List.getElem!_replace_slice]
      simp_ifs
termination_by dst.length - offset
decreasing_by scalar_decr_tac

@[simp]
theorem Aeneas.Std.Slice.val_drop{T: Type}(s: Slice T)(k: Usize)
: (s.drop k).val = s.val.drop k.val
:= by simp [Slice.drop]

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 1000000 in
-- set_option trace.meta.Tactic.simp true in
theorem simple.sponge_squeeze.panic_free.refinement(r i: Std.Usize)
  (dst: Std.Slice Bool)(s: Aeneas.Std.Array Bool 1600#usize)
: (r_bnd: 0 < r.val ∧ r.val < 1600)
→ i ≤ dst.length
→ dst.length + r.val < Std.Usize.max
→ let _: NeZero r.val := {out:= Nat.not_eq_zero_of_lt r_bnd.left}
  ∃ output,
  sponge_squeeze_loop r dst s i = .ok output ∧
  output.val = panic_free r.val dst.val s.val i.val
:= by
  intro r_bnd i_idx no_overflow
  unfold simple.sponge_squeeze_loop panic_free
  let* ⟨ i1, i1_post ⟩ ← Std.Usize.add_spec
  split
  . simp [Std.core.slice.index.Slice.index_mut, Std.core.slice.index.SliceIndexRangeUsizeSlice.index_mut]
    simp_ifs
    simp [Std.core.array.Array.index, Std.core.ops.index.IndexSliceInst, Std.core.slice.index.Slice.index, Std.core.slice.index.SliceIndexRangeUsizeSlice.index, Std.Array.to_slice]
    simp_ifs
    simp [Std.core.slice.Slice.copy_from_slice, List.slice, Std.Slice.len]
    simp_ifs
    simp
    let* ⟨ s4, s4_post ⟩ ← keccak_p.spec'
    simp [List.replace_slice, *, le_of_lt]
    try simp_ifs -- TODO: Why does this not work?
    split
    case isFalse =>
      scalar_tac -- contradiction
    case isTrue h =>
      let* ⟨ rest, rest_post⟩ ← refinement
      simp [*]
  . let* ⟨ nb_left, nb_left_post ⟩ ← Aeneas.Std.Usize.sub_spec'
    simp at nb_left_post
    simp [Std.core.slice.index.Slice.index_mut, Std.core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut]
    simp_ifs
    simp [Std.core.array.Array.index, Std.core.ops.index.IndexSliceInst, Std.core.slice.index.Slice.index, Std.core.slice.index.SliceIndexRangeUsizeSlice.index, Std.Array.to_slice]
    simp_ifs
    simp [Std.core.slice.Slice.copy_from_slice, List.slice, Std.Slice.len, *, Nat.min_def, List.length_drop]
    simp_ifs
    simp [*]
    try simp_ifs -- TODO: Again, why does this not work?
    have : (dst.length - ↑i) ⊓ 1600 + i.val ≤ Std.Usize.max := by scalar_tac
    simp [this, List.replace_slice]
termination_by dst.length - i
decreasing_by scalar_decr_tac

theorem BitVec.toList_inj{bv bv2: BitVec n}
: bv.toList = bv2.toList → bv = bv2
:= by
  intro cond
  ext i i_idx
  replace cond := List.getElem_of_eq cond (by simp; exact i_idx)
  simpa [getElem_eq_getElem!] using cond

theorem BitVec.getLsbD_eq_getElem! {x : BitVec w} {i : Nat} :
    x.getLsbD i = x[i]! := by
  if h: i < w then
    simp only [getElem!_pos, h]
    rfl
  else
    rw [getElem!_neg]
    case h => assumption
    simp [default, BitVec.getLsbD, Nat.testBit]
    have: x.toNat >>> i = 0 := by
      apply Nat.shiftRight_eq_zero
      calc
        _ < 2^w := by exact x.toFin.isLt
        _ ≤ 2^i := by
          apply Nat.pow_le_pow_of_le Nat.one_lt_two
          simpa using h
    rw [this]

attribute [local simp] BitVec.getLsbD_eq_getElem! in
theorem BitVec.toList_setWidth(bv: BitVec n)(m: Nat)
: (bv.setWidth m).toList = bv.toList.setWidth m
:= by
  ext i
  · simp
  simp
  assume i < m
  case otherwise h => simp [getElem!_neg, h]
  simp [getElem!_pos, *]

attribute [local simp_lists_simps] List.getElem!_take_eq_ite in
set_option maxRecDepth 1000000 in
def ListIR.sponge.squeeze.refinement(r: Nat) [NeZero r]
    (Z: BitVec m)
    (S: BitVec (Spec.b 6))
: Spec.sponge.squeeze (d := d) (f := Spec.Keccak.P 6 24) r Z S =
  (squeeze d r Z.toList S.toList).toBitVec.cast (by simp)
:= by
  refine BitVec.toList_inj ?_

  simp
  unfold squeeze Spec.sponge.squeeze
  simp
  split
  case isTrue base_case =>
    simp [base_case, BitVec.toList]
    ext i
    · simp [*]
    simp_lists
    simp
    assume i < d
    case otherwise h => simp [h]
    simp [*, ‹i < m›']
    rfl
  case isFalse _ =>
    rw [ListIR.sponge.squeeze.refinement]
    simp [ListIR.list_keccak_p, BitVec.toBitVec_toList]
    congr
    simp [BitVec.toList_setWidth]
termination_by d - m
decreasing_by scalar_decr_tac


theorem simple.sponge_squeeze.spec(r i: Std.Usize)
  (dst: Std.Slice Bool)(s: Aeneas.Std.Array Bool 1600#usize)
: (r_bnd: 0 < r.val ∧ r.val < 1600)
→ i ≤ dst.length
→ dst.length + r.val < Std.Usize.max
→ let _: NeZero r.val := {out:= Nat.not_eq_zero_of_lt r_bnd.left}
  ∃ output,
  sponge_squeeze_loop r dst s i = .ok output ∧
  output.val = ListIR.sponge.squeeze dst.length r (dst.val.take i.val) s.val
:= by
  intros
  progress with simple.sponge_squeeze.panic_free.refinement as ⟨res, res_post⟩
  rw [res_post]
  rw [simple.sponge_squeeze.panic_free.spec]
  · assumption
  · simp
  · simpa
