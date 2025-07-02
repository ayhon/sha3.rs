import Aeneas
import Shars.ArrayExtract
import Shars.Verification.Utils.Notation
import Shars.Verification.Utils.List
import Sha3.Utils


set_option maxHeartbeats 100000
attribute [-simp] List.getElem!_eq_getElem?_getD
attribute [simp] Id.run Id.pure_eq Id.bind_eq


theorem Array.append_of_extract{arr: Array α}{l r: Nat}
  (m: Nat)(m_ge: l ≤ m)(m_lt: m ≤ r)
: arr.extract l r = arr.extract l m ++ arr.extract m r
:= by simp [m_ge, m_lt]

theorem Array.extract_one(arr: Array α)(l: Nat)
   (l_idx: l < arr.size)
: arr.extract l (l+1) = #[arr[l]]
:= by
  ext i hi1 hi2
  · simp [‹l+1 ≤ arr.size›']
  simp at hi1 hi2
  simp [hi2]

theorem Array.append_left_extract_of_extract(arr: Array α)(l r: Nat)
: (l_idx: l < arr.size)
→ (nonempty: l < r)
→ arr.extract l r = #[arr[l]] ++ arr.extract (l+1) r
:= by
  intro l_idx nonempty
  rw [Array.append_of_extract (l+1), Array.extract_one]
  all_goals omega

theorem Array.foldl_step_right(arr: Array α)(l r: Nat)(upd: β → α → β)(init: β)(l_idx: l < arr.size)(nontriv: l < r)
: arr.foldl upd init l r = arr.foldl upd (upd init arr[l]) (l+1) r
:= by
  unfold foldl
  rw [Array.foldlM_start_stop (m := Id), ←Array.foldlM_toList]
  rw [Array.foldlM_start_stop (m := Id), ←Array.foldlM_toList]
  by_cases r = l + 1 <;> simp [List.take_one, Array.append_left_extract_of_extract, *]

theorem Array.append_right_extract_of_extract(arr: Array α)(l r: Nat)
: (r_bnd: r < arr.size)
→ (nonempty: l ≤ r)
→ arr.extract l (r+1) = arr.extract l r ++ #[arr[r]]
:= by
  intro l_idx nonempty
  rw [Array.append_of_extract r, Array.extract_one]
  all_goals omega

theorem Array.foldl_step_left(arr: Array α)(l r: Nat)(upd: β → α → β)(init: β)(r_le: r ≤ arr.size)(nontriv: l < r)
: arr.foldl upd init l r = upd (arr.foldl upd init l (r-1)) arr[r-1]
:= by
  cases r
  case zero => simp at nontriv
  case succ r' =>
    have := ‹r' < arr.size›'
    unfold foldl
    rw [Array.foldlM_start_stop (m := Id), ←Array.foldlM_toList]
    rw [Array.foldlM_start_stop (m := Id), ←Array.foldlM_toList]
    if h: l = r' then
      simp [List.take_one, *]
    else
      rw [Array.append_right_extract_of_extract]
      · simp
      · assumption
      · omega

@[simp]
theorem Array.getElem!_append[Inhabited α]
  (ls ls2: Array α)(i: Nat)
: (ls ++ ls2)[i]! = if i < ls.size then ls[i]! else ls2[i - ls.size]!
:= by
  split
  case isTrue i_idx =>
    simp [getElem!_pos, i_idx, ‹i < ls.size + ls2.size›', Array.getElem_append]
  case isFalse i_oob =>
    by_cases i < ls.size + ls2.size
    case pos h => simp [getElem!_pos, ‹i - ls.size < ls2.size›', h, Array.getElem_append, i_oob]
    case neg h =>
      rw [getElem!_neg]
      case h => simpa using h
      rw [getElem!_neg]
      case h => scalar_tac

theorem Array.foldl_extract(arr: Array α)(l r: Nat)(upd: β → α → β)(init: β)
: (arr.extract l r).foldl upd init = arr.foldl upd init l r
:= by simp only [foldl, ←foldlM_start_stop (m := Id)]


theorem Array.toList_foldl(arr: _root_.Array α)
: arr.toList.foldl upd init = (arr.foldl upd init)
:= by simp only [foldl_toList]

theorem Array.foldl_mk(ls: List α)
: (Array.mk ls).foldl upd init = (ls.foldl upd init)
:= by
  simp only [List.size_toArray, List.foldl_toArray']

@[elab_as_elim, cases_eliminator]
theorem Array.cases_extract(k: Nat)[NeZero k]
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
    simp [Nat.ne_zero_of_lt k_pos, Array.extract_start_start]
    cases i
    case zero => simp
    case succ i' =>
      rw [Array.getElem_append_right (by simp)]
      simp
      rw [←getElem!_pos]

      rw [Array.extract_empty_of_size_le_start (h := by simp),
          Array.extract_empty_of_size_le_start (h := ?precond),
          Array.empty_append,
          Array.empty_append,
      ]
      case precond => simp; (conv => arg 1; rw [←Nat.mul_one k]); apply Nat.mul_le_mul_left; simp
      rw [Array.toArray_getElem!_chunks_exact]
      case i_idx => simpa [Nat.add_div_left, k_pos] using i_idx
      case a => exact k_pos

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

theorem Array.toList_chunks_exact(arr: Array α)(r: Nat)
: (arr.chunks_exact r).toList.map (·.toList) = arr.toList.chunks_exact r
:= by
  obtain ⟨data⟩ := arr
  if r_pos: r = 0 then
    subst r_pos
    simp [chunks_exact, List.chunks_exact]
  else if data_small: data.length < r then
    unfold chunks_exact List.chunks_exact
    simp [Nat.le_of_sub_eq_zero, Nat.lt_of_add_one_le, *]
  else
    have: data.length ≥ r := by omega
    unfold chunks_exact List.chunks_exact
    simp [*, not_lt.mpr]
    rw [Array.toList_chunks_exact]
    simp [List.take_of_length_le]
termination_by arr.size + 1 - r
decreasing_by simp [*]; omega
