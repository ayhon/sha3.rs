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

set_option maxHeartbeats 100000
attribute [-simp] List.getElem!_eq_getElem?_getD
/- attribute [simp] Aeneas.Std.Slice.set -/

open Aeneas hiding Std.Array
open Std.alloc.vec 

def spec_sponge (r: Nat)(r_pos: r > 0):= 
  have: NeZero r := ⟨Nat.not_eq_zero_of_lt r_pos⟩
  Spec.sponge (f := Spec.Keccak.P 6 24) (pad := Spec.«pad10*1»)
def spec_sponge_absorb (r: Nat)(r_pos: r > 0) := 
  have: NeZero r := ⟨Nat.not_eq_zero_of_lt r_pos⟩
  Spec.sponge.absorb (f := Spec.Keccak.P 6 24) (pad := Spec.«pad10*1») (r := r) 
def spec_sponge_squeze{m d}(r: Nat)(r_pos: r > 0) := 
  have: NeZero r := ⟨Nat.not_eq_zero_of_lt r_pos⟩
  Spec.sponge.squeeze (m := m) (d := d) (f := Spec.Keccak.P 6 24) (r := r)

/- #check BitVec.setWidth_cast -/

def absorb{r: Nat}(S: BitVec (Spec.b 6))(Ps: Array (BitVec r)) := Id.run do
  let mut S := S
  for P in Ps do
    S := Spec.Keccak.P 6 24 (S ^^^ P.setWidth (Spec.b 6))
  return S

theorem absorb_def{r: Nat}(S: BitVec (Spec.b 6))(Ps: Array (BitVec r)) 
: absorb S Ps = List.foldl (Spec.Keccak.P 6 24 <| · ^^^ BitVec.setWidth (Spec.b 6) ·) S Ps.toList
:= by simp [absorb, ←Array.foldl_toList,-Array.size_chunks_exact, -Array.size_map]

theorem absorb.spec (N : Array Spec.Bit) (r: Nat)(r_pos: r > 0)
: spec_sponge_absorb r r_pos N = absorb (0#(Spec.b 6)) ((N ++ Spec.«pad10*1» r N.size).chunks_exact r |>.map (·.toBitVec))
:= by 
  rw [spec_sponge_absorb, Spec.sponge.absorb, absorb_def]
  -- NOTE: I needed to exercise a bit too much control here.
  simp [←Array.foldl_toList,-Array.size_chunks_exact, -Array.size_map]
  rw [←List.foldl_of_foldl_map (f := Vector.toBitVec)]
  simp [Vector.toBitVec]

/- @[progress] -/
/- theorem Aeneas.Std.core.slice.index.Slice.index.spec -/
/-   (bs: Std.Slice α)(inst: SliceIndex (ops.range.Range Usize) (Slice α) (Slice α))(range: ops.range.Range Usize) -/
/- : ∃ output, -/
/-   Aeneas.Std.core.slice.index.Slice.index inst bs range = .ok output ∧ -/


/-     (Std.core.slice.index.SliceIndexRangeUsizeSliceInst Bool) bs := -/ 

attribute [simp] Aeneas.Std.core.slice.index.Slice.index

@[progress]
theorem Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice.index.spec(input: Slice α)(r: ops.range.Range Usize)
: r.start.val ≤ r.end_.val
→ r.end_.val ≤ input.length
→ ∃ output,
  core.slice.index.SliceIndexRangeUsizeSlice.index r input = .ok output ∧
  output.val = input.val.extract r.start.val r.end_.val
:= by
  obtain ⟨start, end_⟩ := r
  intro r_proper end_lt_length
  simp at *
  rw [index]
  simp [List.slice, *]

@[progress]
theorem Aeneas.Std.core.slice.index.Slice.index.slice_index_range_usize_slice_spec(input: Slice α)(r: ops.range.Range Usize)
: r.start.val ≤ r.end_.val
→ r.end_.val ≤ input.length
→ ∃ output,
  core.slice.index.Slice.index (Std.core.slice.index.SliceIndexRangeUsizeSliceInst α) input r = .ok output ∧
  output.val = input.val.extract r.start.val r.end_.val
:= by simpa using SliceIndexRangeUsizeSlice.index.spec input r

@[progress]
theorem simple.sponge_absorb_initial_loop.spec
  (bs : Std.Slice Bool) (r : Std.Usize) (s : Aeneas.Std.Array Bool 1600#usize) (n i : Std.Usize)
: n.val = bs.length / r.val
→ (r_pos: r.val > 0)
→ i.val ≤ n.val
→ r.val < 1600
→ ∃ output,
  sponge_absorb_initial_loop bs r s n i = .ok output ∧ 
  have h: (1600#usize).val = Spec.b 6 := by simp [Spec.w, Spec.b]
  output.toBitVec = ((absorb (s.toBitVec.cast h) (bs.toArray.chunks_exact r |>.map (·.toBitVec) |>.drop i)).cast h.symm)
:= by
  rintro n_val r_pos i_idx r_le
  rw [sponge_absorb_initial_loop]
  split
  case isTrue i_idx =>
    have _: r.val*i.val ≤ bs.length := sorry -- r * i < r * n = r * (bs.length / r) ≤ bs.length ≤ Usize.max
    have _: r.val*(i.val + 1) ≤ bs.length := sorry -- r * (i + 1) ≤ r * n = r * (bs.length / r) ≤ bs.length ≤ Usize.max

    let* ⟨ i1, i1_post ⟩ ← Std.Usize.mul_spec
    let* ⟨ i2, i2_post ⟩ ← Std.Usize.add_spec
    let* ⟨ i3, i3_post ⟩ ← Std.Usize.mul_spec
    let* ⟨ slice, slice_post ⟩ ← Std.core.slice.index.Slice.index.slice_index_range_usize_slice_spec
    let* ⟨old_slice, new_slice, slice_mut_post⟩ ← Std.Array.to_slice_mut.progress_spec
    simp [Std.Array.to_slice_mut, Std.Array.to_slice] at slice_mut_post
    obtain ⟨old_slice_post, new_slice_post⟩ := slice_mut_post
    let* ⟨ s2, s2_post ⟩ ← xor_long.spec
    let* ⟨ s4, s4_post ⟩ ← keccak_p.spec
    let* ⟨rest, rest_post ⟩ ← spec

    simp [*, new_slice_post]
    apply congrArg
    simp [absorb_def]
    

    sorry

  case isFalse i_oob =>
    have := ‹bs.length / r.val - i.val = 0›'
    simp [absorb, this]
    sorry
/- termination_by n.val - i.val -/
/- decreasing_by scalar_decr_tac -/


@[progress]
theorem simple.sponge_absorb_initial.spec
  (bs : Std.Slice Bool) (r : Std.Usize) (s : Aeneas.Std.Array Bool 1600#usize)
(r_pos: r.val > 0)
: s.toBitVec = (0#(Spec.b 6)).cast (by simp [Spec.w, Spec.b])
→ ∃ output,
  sponge_absorb_initial bs r s = .ok output ∧ 
  let h := by simp [Spec.b, Spec.w]
  output.toBitVec = ((absorb (s.toBitVec.cast h) (bs.toArray.chunks_exact r |>.map (·.toBitVec))).cast h.symm)
:= by 
  intro s_zero
  rw [sponge_absorb_initial]
  let* ⟨ n, n_post ⟩ ← Std.Usize.div_spec
  let* ⟨ res, res_post ⟩ ← simple.sponge_absorb_initial_loop.spec
  simp [*, Array.extract_eq_self_of_le]

@[progress]
theorem simple.sponge_absorb_final.spec
  (rest suffix : Std.Slice Bool) (r : Std.Usize) (s : Aeneas.Std.Array Bool _)
(r_pos: r.val > 0)
: rest.length < r
→ suffix.length ≤ 4
→ ∃ output,
  sponge_absorb_final s rest suffix r = .ok output ∧ 
  let h := by simp [Spec.b, Spec.w]
  output.toBitVec = (
    absorb (s.toBitVec.cast h) (
      (rest.toArray ++ suffix.toArray ++ Spec.«pad10*1» r (rest.val ++ suffix.val).length).chunks_exact r
        |>.map (·.toBitVec)
    )
  ).cast h.symm
:= by 
  intro rest_small suffix_le
  sorry


/- @[progress] -/
theorem simple.sponge_absorb.spec
  (bs : Std.Slice Bool) (r : Std.Usize) [NeZero r.val](output : Aeneas.Std.Array Bool 1600#usize)
  (suffix : Std.Slice Bool)
: r.val < 1600
→ ∃ output,
  sponge_absorb bs r output suffix = .ok output ∧
  output.toBitVec = (spec_sponge_absorb r.val (Nat.pos_of_neZero r.val) (bs.toArray ++ suffix.toArray)).cast (by simp [Spec.b, Spec.w])
:= by 
  intro r_bounded
  unfold sponge_absorb
  let* ⟨_, _⟩ ← simple.sponge_absorb_initial.spec
  progress*?

  sorry

-- @[progress]
theorem simple.sponge.spec (r : Std.Usize) (bs output suffix: Std.Slice Bool) 
[NeZero r.val]
/- (r_ne_zero: r.val ≠ 0) -/
: ∃ output,
  simple.sponge r bs output suffix = .ok output ∧
  output.val = (Spec.sponge (f := Spec.Keccak.P 6 (nᵣ := 24)) (pad := Spec.«pad10*1») r.val (Array.mk <| bs.val ++ suffix.val ) output.length).toArray.toList
:= by sorry
