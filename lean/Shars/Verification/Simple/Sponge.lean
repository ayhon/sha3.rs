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
import Shars.Verification.Simple.Auxiliary
import Shars.Verification.Simple.KeccakP

set_option maxHeartbeats 1000000
attribute [-simp] List.getElem!_eq_getElem?_getD
attribute [simp] Aeneas.Std.Slice.set

open Aeneas hiding Std.Array
open Std.alloc.vec 

abbrev spec_sponge (r: Nat)(r_pos: r > 0):= 
  have: NeZero r := ⟨Nat.not_eq_zero_of_lt r_pos⟩
  Spec.sponge (f := Spec.Keccak.P 6 24) (pad := Spec.«pad10*1»)
abbrev spec_sponge_absorb (r: Nat)(r_pos: r > 0) := 
  have: NeZero r := ⟨Nat.not_eq_zero_of_lt r_pos⟩
  Spec.sponge.absorb (f := Spec.Keccak.P 6 24) (pad := Spec.«pad10*1») (r := r) 
abbrev spec_sponge_squeze{m d}(r: Nat)(r_pos: r > 0) := 
  have: NeZero r := ⟨Nat.not_eq_zero_of_lt r_pos⟩
  Spec.sponge.squeeze (m := m) (d := d) (f := Spec.Keccak.P 6 24) (r := r)

def Vector.toBitVec(self: Vector Bool n): BitVec n := (BitVec.ofBoolListLE <| self.toList).cast (by simp)

def absorb{r: Nat}(S: BitVec (Spec.b 6))(Ps: Array (BitVec r)) := Id.run do
  let mut S := S
  for P in Ps do
    S := Spec.Keccak.P 6 24 (S ^^^ P.setWidth (Spec.b 6))
  return S

theorem absorb.spec (N : Array Spec.Bit) (r: Nat)(r_pos: r > 0)
: spec_sponge_absorb r r_pos N = absorb (0#(Spec.b 6)) ((N ++ Spec.«pad10*1» r N.size).chunks_exact r |>.map (·.toBitVec))
:= by sorry

@[elab_as_elim, cases_eliminator]
def Array.cases_extract(k: Nat)[NeZero k]
  {motive : Array α → Prop}
  (onSmall: (rest: Array α) → (small: rest.size < k) → motive rest)
  (onBig: (chunk: Vector α k) → (rest: Array α) → motive (chunk.toArray ++ rest))
  (arr: Array α)
: motive arr
:= 
  if h: arr.size < k then
    onSmall arr h
  else
    let chunk: Vector α k := ⟨arr.extract (stop  := k), (by simpa using h)⟩
    let other := arr.extract (start := k)
    have properPartition: chunk.toArray ++ other = arr := by simp [chunk, other]
    properPartition ▸ onBig chunk other

@[simp]
theorem Array.size_chunks_exact[Inhabited α](arr: Array α)(k: Nat)
: (arr.chunks_exact k).size = arr.size / k
:= by
  rw [chunks_exact]
  split
  case isTrue h =>
    rcases h with arr_small | k_zero
    · simp [Nat.div_eq_of_lt arr_small]
    · simp [k_zero]
  case isFalse h =>
    simp at h
    obtain ⟨k_lt_size, k_pos⟩ := h
    simp
    have ih: (chunks_exact k (arr.extract k)).size = (arr.size - k) / k
      := by simpa using (arr.extract k).size_chunks_exact k
    rw [
      ih, 
      Nat.add_comm,
      ←Nat.add_div_right (H := Nat.zero_lt_of_ne_zero k_pos),
      Nat.sub_add_cancel k_lt_size
    ]
termination_by arr.size
decreasing_by 
  replace k_pos := Nat.zero_lt_of_ne_zero k_pos
  simp [k_pos]
  apply trans k_pos k_lt_size

theorem Array.extract_start_start(arr: Array α)(start: Nat)
: arr.extract start start = #[]
:= by simp only [extract_eq_empty_iff, inf_le_left]

theorem Array.getElem_chunks_exact[Inhabited α](arr: Array α)(k i: Nat)(i_idx: i < arr.size / k)
: k > 0 
→ (arr.chunks_exact k)[i]!.toArray = arr.extract (k*i) (k*(i+1))
:= by
  intro k_pos
  have: NeZero k := {out := by omega}
  have : i < (chunks_exact k arr).size := by simp [i_idx]
  rw [getElem!_pos _ i this]

  cases arr using Array.cases_extract k
  case onSmall small =>
    have: arr.size / k = 0 := Nat.div_eq_of_lt small
    simp [this] at i_idx
  case onBig chunk rest =>
    /- rw [Array.chunks_exact] -- TODO: Why does rw fail here? -/
    unfold Array.chunks_exact
    simp [Nat.not_eq_zero_of_lt k_pos, Array.extract_start_start]
    cases i
    case zero =>
      simp
      rw [Array.getElem_append_left (Nat.one_pos)]
      simp
    case succ i' =>
      rw [Array.getElem_append_right (by simp)]
      simp 
      rw [getElem_eq_getElem!]

      rw [Array.extract_empty_of_size_le_start chunk.toArray (by simp)]
      rw [Array.extract_empty_of_size_le_start chunk.toArray ?precond]
      case precond => simp; (conv => arg 1; rw [←Nat.mul_one k]); apply Nat.mul_le_mul_left; simp

      simp
      have ih := Array.getElem_chunks_exact rest k i'
      rw [ih ?i_idx (k_pos)]
      case i_idx => simpa [Nat.add_div_left (H := k_pos)] using i_idx

      ring_nf
      congr
      · rw[Nat.add_comm, Nat.add_sub_cancel]
      · rw[Nat.add_comm (k*2), Nat.mul_two, ←Nat.add_assoc, Nat.add_sub_cancel, Nat.add_comm]


def Aeneas.Std.Array.toArray{size: Usize}(self: Aeneas.Std.Array α size): _root_.Array α := Array.mk self.val
def Aeneas.Std.Slice.toArray(self: Aeneas.Std.Slice α): _root_.Array α := Array.mk self.val

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
→ ∃ output,
  sponge_absorb_initial_loop bs r s n i = .ok output ∧ 
  have h: (1600#usize).val = Spec.b 6 := by simp [Spec.w, Spec.b]
  output.toBitVec = ((absorb (s.toBitVec.cast h) (bs.toArray.chunks_exact r |>.map (·.toBitVec) |>.drop i)).cast h.symm)
:= by
  rintro n_val r_pos
  rw [sponge_absorb_initial_loop]
  split
  . let* ⟨ i1, i1_post ⟩ ← Std.Usize.mul_spec
    · sorry
    let* ⟨ i2, i2_post ⟩ ← Std.Usize.add_spec
    let* ⟨ i3, i3_post ⟩ ← Std.Usize.mul_spec
    · sorry
    let* ⟨ slice, slice_post ⟩ ← Std.core.slice.index.Slice.index.slice_index_range_usize_slice_spec
    · sorry
    let* ⟨old_slice, new_slice⟩ ← Std.Array.to_slice_mut.progress_spec
    let* ⟨ s2, s2_post ⟩ ← xor_long.spec
    let* ⟨ s4, s4_post ⟩ ← keccak_p.spec
    let* ⟨_, _ ⟩ ← spec
    simp [*]
    sorry

  case isFalse h =>
    have := ‹bs.length / r.val - i.val = 0›'
    simp [absorb, this]
    sorry


/- @[progress] -/
theorem simple.sponge_absorb_initial.spec
  (bs : Std.Slice Bool) (r : Std.Usize) (s : Aeneas.Std.Array Bool _)
(r_pos: r.val > 0)
: s.toBitVec = (0#(Spec.b 6)).cast (by simp [Spec.w, Spec.b])
→ ∃ output,
  sponge_absorb_initial bs r s = .ok output ∧ 
  output.toBitVec = ((spec_sponge_absorb r.val r_pos ⟨bs.val⟩).cast (by simp [Spec.w, Spec.b]))
:= by sorry

/- @[progress] -/
theorem simple.sponge_absorb_final.spec
  (rest suffix : Std.Slice Bool) (r : Std.Usize) (s : Aeneas.Std.Array Bool _)
(r_pos: r.val > 0)
: ∃ output,
  sponge_absorb_final s rest suffix r = .ok output ∧ 
  output.toBitVec = (spec_sponge_absorb r.val r_pos ⟨bs.val⟩).cast (by simp [Spec.w, Spec.b]))
:= by sorry


/- @[progress] -/
theorem simple.sponge_absorb.spec
  (bs : Std.Slice Bool) (r : Std.Usize) [NeZero r.val](output : Aeneas.Std.Array Bool 1600#usize)
  (suffix : Std.Slice Bool)
: ∃ output,
  sponge_absorb_initial_loop
  sponge_absorb bs r output suffix = .ok output ∧
  output.val = (Spec.sponge.absorb (f:=Spec.Keccak.P 6 24) (pad:=Spec.«pad10*1») r.val (Array.mk <| bs.val ++ suffix.val)).toArray.toList
:= by sorry

-- @[progress]
theorem simple.sponge.spec (r : Std.Usize) (bs output suffix: Std.Slice Bool) 
[NeZero r.val]
/- (r_ne_zero: r.val ≠ 0) -/
: ∃ output,
  simple.sponge r bs output suffix = .ok output ∧
  output.val = (Spec.sponge (f := Spec.Keccak.P 6 (nᵣ := 24)) (pad := Spec.«pad10*1») r.val (Array.mk <| bs.val ++ suffix.val ) output.length).toArray.toList
:= by sorry
