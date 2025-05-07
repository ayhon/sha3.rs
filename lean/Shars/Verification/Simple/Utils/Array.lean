import Aeneas
import Shars.ArrayExtract
import Shars.Verification.Simple.Utils.Notation
import Shars.Verification.Simple.Utils.Extract


set_option maxHeartbeats 100000
attribute [-simp] List.getElem!_eq_getElem?_getD
attribute [simp] Id.run Id.pure_eq Id.bind_eq


theorem Array.foldl_split(arr: Array α)(upd: β → α → β)(init: β)
    (l m r: Nat)
    (l_idx: l < arr.size := by assumption)
    (r_le: r ≤ arr.size := by assumption)
    (m_inside: l ≤ m ∧ m < r := by simp; omega)
: arr.foldl upd init l r = arr.foldl upd (arr.foldl upd init l m) m r
:= by
  simp only [Array.foldl]
  rw [Array.foldlM_start_stop (m := Id), ←Array.foldlM_toList]
  rw [Array.foldlM_start_stop (m := Id), ←Array.foldlM_toList]
  rw [Array.foldlM_start_stop (m := Id), ←Array.foldlM_toList]
  simp only [Id.run]
  have : arr.extract l r = arr.extract l m ++ arr.extract m r := by
    simp; congr
    · simp [*]
    · simp [*, le_of_lt]
  rw [this, Array.toList_append]
  rw [List.foldlM_append]
  simp

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
  rw [←Array.extract_one]
  rw [Array.extract_append_extract]
  simp [*, ‹l + 1 ≤ r›']

theorem Array.foldl_step_right(arr: Array α)(l r: Nat)(upd: β → α → β)(init: β)(l_idx: l < arr.size)(r_le: r ≤ arr.size)(nontriv: l < r)
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
  intro r_bnd nonempty
  rw [←Array.extract_one]
  rw [Array.extract_append_extract]
  simp [*]

theorem Array.foldl_step_left(arr: Array α)(l r: Nat)(upd: β → α → β)(init: β)(l_idx: l < arr.size)(r_le: r ≤ arr.size)(nontriv: l < r)
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

theorem Array.getElem!_toList[Inhabited α](arr: Array α)(i: Nat)
: arr.toList[i]! = arr[i]!
:= by simp [getElem!_def]

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
