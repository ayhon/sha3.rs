import Aeneas
import Shars.ArrayExtract
import Shars.Verification.Simple.Utils.List
import Sha3.Utils

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

theorem Array.toArray_getElem!_chunks_exact[Inhabited α](arr: Array α)(k i: Nat)(i_idx: i < arr.size / k)
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
      have ih := Array.toArray_getElem!_chunks_exact rest k i'
      rw [ih ?i_idx (k_pos)]
      case i_idx => simpa [Nat.add_div_left (H := k_pos)] using i_idx

      ring_nf
      congr
      · rw[Nat.add_comm, Nat.add_sub_cancel]
      · rw[Nat.add_comm (k*2), Nat.mul_two, ←Nat.add_assoc, Nat.add_sub_cancel, Nat.add_comm]

@[simp]
theorem Array.size_getElem!_chunks_exact[Inhabited α](arr: Array α)(k i: Nat)
: k > 0 
→ (arr.chunks_exact k)[i]!.size = k
:= by
  intro k_pos
  simp

theorem Array.getElem!_chunks_exact[Inhabited α](arr: Array α)(k i: Nat)
  (i_idx: i < arr.size / k)
  (k_pos: k > 0)
: (arr.chunks_exact k)[i]! = ⟨arr.extract (k*i) (k*(i+1)), by simp [←Array.toArray_getElem!_chunks_exact arr k i i_idx k_pos]⟩
:= by 
  simp only [Vector.eq_mk] 
  apply Array.toArray_getElem!_chunks_exact arr k i i_idx k_pos
