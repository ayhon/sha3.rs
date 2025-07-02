import Aeneas.ScalarTac
import Mathlib
import Shars.Verification.Utils.SimpLikeTactics
import Shars.Verification.Utils.ScalarTac
import Shars.Verification.Utils.Notation

set_option maxHeartbeats 100000
set_option maxRecDepth 10000000

attribute [-simp] List.getElem!_eq_getElem?_getD

theorem List.foldl_of_foldl_map(f: α' → α)(upd: β → α → β)(upd' : β → α' → β)(init: β)(ls: List α')
: upd' = (upd · <| f ·)
→ List.foldl upd' init ls = List.foldl upd init (ls.map f)
:= by rintro rfl; revert init; induction ls <;> simp [*]

theorem List.val_finRange_eq_range(n: Nat)
: (List.finRange n).map Fin.val = List.range n
:= by cases n <;> simp

theorem List.drop_range'(i s n: Nat): (List.range' s n |>.drop i) = List.range' (s + i) (n - i) := by
  cases i
  case zero => simp
  case succ i' =>
    cases n
    case zero => simp
    case succ n' =>
      rw [List.range'_succ, List.drop_succ_cons, Nat.add_comm i', ←Nat.add_assoc, Nat.sub_add_eq, Nat.add_sub_cancel]
      apply List.drop_range'

theorem List.drop_range(i n: Nat): (List.range n |>.drop i) = List.range' i (n-i) := by
  simp [List.range_eq_range', List.drop_range' (s := 0)]

theorem getElem_eq_getElem! [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
  [Inhabited elem] (c : cont) (i : idx) (h : dom c i)
: getElem c i h = getElem! c i
:= by
  have : Decidable (dom c i) := .isTrue h
  simp [getElem!_def, getElem?_def, h]

@[simp_lists_simps]
theorem List.getElem!_zipWith[Inhabited α] [Inhabited β] [Inhabited c]
  (a: List α)(b:List β)(f: α → β → c)(i: Nat)
: i < a.length
→ i < b.length
→ (a.zipWith f b)[i]! = f a[i]! b[i]!
:= by intros; simp [←getElem_eq_getElem!, *]

theorem List.zipWith_append_truncate_right{α : Type u} (f: α → β → γ) (x : List α)(y z: List β)
  (hyp: y.length ≥ x.length)
: List.zipWith f x (y ++ z) = List.zipWith f x y
:= by cases x <;> cases y <;> simp_all [List.zipWith_append_truncate_right]

theorem List.zipWith_append_truncate_left{α : Type u} (f:  β → α → γ) (x : List α)(y z: List β)
  (hyp: y.length ≥ x.length)
: List.zipWith f (y ++ z) x = List.zipWith f y x
:= by
  conv in (occs := *) List.zipWith f _ _ => all_goals rw [List.zipWith_comm]
  apply List.zipWith_append_truncate_right (hyp := hyp)

@[simp]
theorem List.drop_eq_drop(ls: List α)(n m: Nat)
: ls.drop n = ls.drop m ↔ n = m ∨ (n ≥ ls.length ∧ m ≥ ls.length)
:= by
  revert n m
  induction ls
  case nil =>
    simp
  case cons hd tl ih =>
    intro n m
    match n, m with
    | 0, 0 => simp
    | n'+1, m'+1 => simp [ih]
    | n'+1, 0
    | 0, m'+1 =>
      simp
      intro h
      have: (hd :: tl).length = (hd::tl).length := by rfl
      conv at this => lhs; (first | rw [←h] | rw [h])
      simp at this
      scalar_tac

def List.setLength(ls: List α)(n: Nat)(fill: α) :=
  match ls, n with
  | _, 0 => []
  | [], _ => List.replicate n fill
  | x :: xs, n'+1 => x :: xs.setLength n' fill

@[simp]
theorem List.length_setLength(ls: List α)(n: Nat)(fill: α)
: (ls.setLength n fill).length = n
:= by
  match ls, n with
  | x::xs, 0 => simp [setLength]
  | [], n => cases n <;> simp [setLength]
  | x :: xs, n'+1 =>
    simp [setLength, List.length_setLength]

@[simp_lists_simps]
theorem List.getElem!_finRange_pos(n: Nat)[NeZero n](i: Nat)
: i < n → (List.finRange n)[i]! = i
:= by
  intro h
  simp [finRange, getElem!_pos, h]
  congr
  simp [Nat.mod_eq_of_lt, h]

@[simp_lists_simps]
theorem List.getElem!_zip[Inhabited α] [Inhabited β]
  (a: List α)(b:List β)(i: Nat)
: i < a.length
→ i < b.length
→ (a.zip b)[i]! = (a[i]!,b[i]!)
:= by apply List.getElem!_zipWith (f := (·,·))

@[simp_lists_simps]
theorem List.take_append_of_ge_length(xs ys: List α)(n: Nat)
: n ≥ xs.length
→ (xs ++ ys).take n = xs ++ ys.take (n - xs.length)
:= by
  revert n
  induction xs
  case nil => simp
  case cons hd tl ih =>
    intro  n n_big
    cases n
    case zero => simp at n_big
    case succ n' =>
      simp
      apply ih
      simpa using n_big

@[simp_lists_simps]
theorem List.getElem!_map[Inhabited β]
  (ls: List α)(f: α → β)(i: Nat)
: (ls.map f)[i]! = if _: i < ls.length then f ls[i] else default
:= by
  split
  case isTrue i_idx =>
    simp [getElem!_def, getElem?_pos, i_idx]
  case isFalse i_oob =>
    rw [List.getElem!_default]
    simpa using i_oob

set_option trace.SimpLists true in
@[simp_lists_simps]
theorem List.getElem!_append[Inhabited α]
  (ls ls2: List α)(i: Nat)
: (ls ++ ls2)[i]! = if i < ls.length then ls[i]! else ls2[i - ls.length]!
:= by split <;> simp_lists

@[simp_lists_simps]
theorem List.zipWith_append_right{α : Type u} (f: α → β → γ) (x : List α)(y z: List β)
: List.zipWith f x (y ++ z) = (List.zipWith f x y).take y.length ++ List.zipWith f (x.drop y.length) z
:= by
  by_cases x.length < y.length
  case pos =>
    simp_lists [List.zipWith_append_truncate_right]
  case neg h =>
    have: (x.zipWith f y).length = y.length := by simpa using h
    simp_lists
    match x, y with
    | [], _ | _, [] => simp
    | a :: x', b :: y' =>
      simp [List.zipWith_append_right]

@[simp_lists_simps, simp]
theorem List.getElem!_singleton[Inhabited α](a: α)
: i = 0 → [a][i]! = a
:= by rintro rfl; congr

@[elab_as_elim, cases_eliminator]
def List.cases_extract(k: Nat)[NeZero k]
  {motive : List α → Prop}
  (onSmall: (rest: List α) → (small: rest.length < k) → motive rest)
  (onBig: (chunk: List α) → (rest: List α) → (small: chunk.length = k) → motive (chunk ++ rest))
  (ls: List α)
: motive ls
:=
  if h: ls.length < k then
    onSmall ls h
  else
    let chunk: List α := ls.extract (stop := k)
    let other := ls.extract (start := k)
    have properPartition: chunk ++ other = ls := by simp [chunk, other]; simp_lists
    properPartition ▸ onBig chunk other (by simp [chunk]; omega)

def List.chunks_exact(k: Nat)(ls: List α): List (List α) :=
  if ls.length < k ∨ k = 0 then
    []
  else
    let chunk := (ls.take k)
    let rest := (ls.drop k).chunks_exact k
    chunk :: rest
termination_by ls.length

#guard [1,2,3,4,5].chunks_exact 2 == [[1,2], [3,4]]

@[simp]
theorem List.length_chunks_exact(ls: List α)(k: Nat)
: (ls.chunks_exact k).length = ls.length / k
:= by
  by_cases h: k > 0
  case neg => simp at h; subst h; simp [chunks_exact]
  case pos =>
    have k_neZero: NeZero k := { out := ne_zero_of_lt h }
    unfold chunks_exact
    cases ls_def: ls using List.cases_extract k
    case onSmall small =>
      simp [Nat.div_eq_zero_iff_lt h |>.mpr small]
      simp [small]
    case onBig chunk rest chunk_small =>
      simp [chunk_small, k_neZero.ne]
      rw [Nat.add_div_left (H:=h)]
      simp
      apply List.length_chunks_exact
termination_by ls.length
decreasing_by simp [ls_def, *]

def List.setWidth[Inhabited α](ls: List α)(n: Nat): List α := ls.take n ++ List.replicate (n - ls.length) default

@[simp ,scalar_tac_simps]
theorem List.length_setWidth[Inhabited α](ls: List α)(n: Nat)
: (ls.setWidth n).length = n
:= by simp [setWidth]; omega

@[scalar_tac_simps]
theorem List.getElem!_chunks_exact(ls: List α)(r: Nat)
: ∀ i < (ls.chunks_exact r).length, (ls.chunks_exact r)[i]! = ls.extract (r*i) (r*(i+1))
:= by
  intro i i_idx
  unfold chunks_exact
  split
  case isTrue h =>
    by_cases h2: r = 0
    · simp [h2] at i_idx
    · simp [h2] at h
      simp [h, h2] at i_idx
      have := pos_iff_ne_zero.mpr h2
      have := Nat.div_eq_zero_iff_lt this |>.mpr h
      simp [this] at i_idx
  case isFalse h =>
    simp at h
    have: NeZero r := {out := h.right}
    cases i
    case zero => simp [h]
    case succ i' =>
      simp at i_idx ⊢
      have :=  List.getElem!_chunks_exact (ls.drop r) r i' (by simp [Nat.div_sub_self]; omega)
      rw [this]
      ext j : 1
      simp [List.extract]
      ring_nf
      congr 2
      omega

theorem List.length_getElem!_chunks_exact(ls: List α)(r: Nat)
: ∀ i < (ls.chunks_exact r).length, (ls.chunks_exact r)[i]!.length = r
:= by
  intro i i_idx
  unfold chunks_exact
  split
  case isTrue h =>
    by_cases h2: r = 0
    · simp [h2] at i_idx
    · simp [h2] at h
      simp [h, h2] at i_idx
      have := pos_iff_ne_zero.mpr h2
      have := Nat.div_eq_zero_iff_lt this |>.mpr h
      simp [this] at i_idx
  case isFalse h =>
    simp at h
    have: NeZero r := {out := h.right}
    cases i
    case zero => simp [h]
    case succ =>
      simp
      apply List.length_getElem!_chunks_exact
      have: ls.length = (ls.length - r) + r := by scalar_tac
      simp at i_idx ⊢
      rw [this, Nat.add_div_right (H:= by omega)] at i_idx
      simpa using i_idx

@[simp, simp_lists_simps]
theorem List.getElem!_setWidth[Inhabited α](ls: List α)(i n: Nat)
: (ls.setWidth n)[i]! = if i < n then ls[i]! else default
:= by
  simp [setWidth]; simp_lists
  split
  case isTrue => simp_ifs
  case isFalse h =>
    simp at h
    by_cases h2: i < n
    case neg =>
      simp_ifs
      rw [getElem!_neg]
      case h => scalar_tac
    replace h := h h2
    rw [List.getElem!_replicate]
    case pos.h => scalar_tac
    simp_ifs
    rw [getElem!_neg]
    case pos.h => scalar_tac

@[simp 10]
theorem List.setWidth_of_length_eq[Inhabited α](ls: List α)(n: Nat)
: ls.length = n → ls.setWidth n = ls
:= by rintro rfl; simp [setWidth]

@[simp] abbrev List.uniform(n: Nat)(ls: List (List α)) := ∀ xs ∈ ls, xs.length = n

@[simp] theorem List.uniform_cons(n: Nat)(hd: List α)(tl: List (List α))
: (hd :: tl).uniform n ↔ (hd.length = n) ∧ tl.uniform n
:= by simp [List.uniform]

theorem List.length_flatten_of_uniform{n: Nat}{ls: List (List Bool)}
: ls.uniform n
→ ls.flatten.length = n * ls.length
:= by
  intro uniform; unfold List.uniform at *
  induction ls
  case nil => simp
  case cons hd tl ih =>
    simp [-length_flatten]
    rw [ih, uniform hd]
    · simp [Nat.mul_add, Nat.add_comm]
    · simp
    · intros; simp [*]

def List.matrixIdx(ls: List (List α))(i: Nat)(acc: Nat := 0): Nat × Nat :=
  match ls with
  | [] => (acc, i)
  | hd :: tl =>
    if i < hd.length then
      (acc, i)
    else
      List.matrixIdx tl (i - hd.length) (acc + 1)

theorem List.acc_le_matrix_idx_1(ls: List (List α))(i acc: Nat)
: acc ≤ (ls.matrixIdx i acc).1
:= by
  unfold List.matrixIdx
  match ls with
  | [] => simp
  | hd :: tl =>
    if i < hd.length then
      simp [*]
    else
      simp [*]
      have := List.acc_le_matrix_idx_1 tl (i - hd.length) (acc + 1)
      omega

theorem List.getElem!_flatten (ls: List (List Bool))(i: Nat)(acc: Nat := 0)
: let (x,y) := ls.matrixIdx i acc
  ls.flatten[i]! = (ls[x - acc]!)[y]!
:= by
  simp only
  match ls with
  | [] => simp [default]
  | hd :: tl =>
    simp
    if i < hd.length then
      simp [List.matrixIdx, *]
    else
      simp [List.matrixIdx, *]
      simp_lists
      rw [List.getElem!_flatten tl (acc := acc + 1)]
      conv => enter [2, 1, 2, 2]; rw [show acc = (acc + 1) - 1 from rfl]
      conv => enter [2, 1, 2]; rw [tsub_tsub_eq_add_tsub_of_le (Nat.le_add_left 1 acc)]
      rw [Nat.sub_add_comm]
      simp
      simp [List.acc_le_matrix_idx_1]

attribute [-simp] List.length_flatten in
theorem List.matrix_idx_of_uniform{ls: List (List Bool)}
  (uniform : ls.uniform n)
  (acc: Nat := 0)
: n > 0
→ ∀ i < ls.flatten.length,
  ls.matrixIdx i acc = (acc + i / n, i % n)
:= by
  intro n_pos i i_idx
  simp [List.length_flatten_of_uniform uniform] at i_idx
  match ls with
  | [] => simp at i_idx
  | hd :: tl =>
    simp [Nat.mul_add] at i_idx uniform
    replace ⟨len_hd, uniform_tl⟩ := uniform
    if h: i < hd.length then
      rw [len_hd] at h
      simp [*, List.matrixIdx, Nat.div_eq_of_lt, Nat.mod_eq_of_lt]
    else
      rw [len_hd] at h
      simp [*, List.matrixIdx]
      have ih := List.matrix_idx_of_uniform (n := n) (i := i - n) (ls := tl) (acc := acc + 1)
      rw [ih]
      · simp +arith [Nat.div_sub_self]
        constructor
        · rw [Nat.sub_add_cancel]
          cases h2: i / n
          case zero => simp [*] at h2; simp [h2] at n_pos
          case succ => simp
        · conv => rhs; rw [Nat.mod_eq_sub_mod (h := by simpa using h)]
      · exact uniform_tl
      · exact n_pos
      · rw [List.length_flatten_of_uniform uniform_tl]
        omega

theorem List.uniform_zero{ls: List (List α)}
: ls.uniform 0 → ls = replicate ls.length []
:= by
  intro uniform
  simp at *
  match ls with
  | [] => simp
  | hd :: tl =>
    simp at *
    obtain ⟨len_hd, uniform_tl⟩ := uniform
    simp [len_hd]
    apply List.uniform_zero
    intro x x_in
    rw [uniform_tl x x_in]
    simp

theorem List.getElem!_flatten_of_uniform {ls: List (List Bool)}{n: Nat}
: ls.uniform n
→ ∀ i, ls.flatten[i]! = (ls[i / n]!)[i % n]!
:= by
  intro uniform i

  by_cases n_pos: n > 0; case neg =>
    simp at n_pos
    simp only [n_pos] at *
    replace uniform := List.uniform_zero uniform
    rw [uniform, Nat.mod_zero, Nat.div_zero]
    cases ls.length <;> simp [default]

  by_cases i_idx: i < ls.flatten.length
  case neg =>
    rw [getElem!_neg]; case h => assumption
    simp [List.length_flatten_of_uniform uniform] at i_idx
    rw [Nat.mul_comm] at i_idx
    have := Nat.le_div_iff_mul_le n_pos |>.mpr i_idx
    simp [this, Nat.div_eq_of_lt, Nat.mod_eq_of_lt, default]

  simp [List.length_flatten_of_uniform uniform] at i_idx
  rw [Nat.mul_comm] at i_idx
  have := Nat.div_lt_of_lt_mul i_idx

  match ls with
  | [] => simp [default]
  | hd :: tl =>
    simp at uniform
    obtain ⟨len_hd, uniform_tl⟩ := uniform
    if i = 0 then
      simp_lists
      simp [*]
    else
      rename_i i_pos
      if h: i < n then
        simp_lists
        simp [Nat.mod_eq_of_lt, Nat.div_eq_of_lt, h]
      else
        simp at h
        simp_lists
        simp [len_hd, Nat.mod_eq_sub_mod, h, Nat.div_eq_sub_div, n_pos]
        apply List.getElem!_flatten_of_uniform
        exact uniform_tl

@[simp_lists_simps]
theorem List.getElem!_set_pos[Inhabited α](ls: List α)(v: α)(i j: Nat)
: i = j ∧ i < ls.length → (ls.set i v)[j]! = v
:= by rintro ⟨rfl,h⟩; apply List.getElem!_set _ _ _ h

@[simp_lists_simps]
theorem List.getElem!_set_neg[Inhabited α](ls: List α)(v: α)(i j: Nat)
: i ≠ j ∨ i ≥ ls.length → (ls.set i v)[j]! = ls[j]!
:= by
  rintro (h1 | h2)
  · apply List.getElem!_set_ne ls i j v
    simp [Nat.not_eq, ne_eq, lt_or_lt_iff_ne, h1]
  · simp [h2, List.set_eq_of_length_le]

---

@[simp] theorem List.setSlice!_nil(ls: List α){i: Nat}: ls.setSlice! i [] = ls := by simp [List.setSlice!]

@[simp] theorem List.setSlice!_of_length_le(ls: List α){i: Nat}
 (length_le : ls.length ≤ i)(s: List α)
: ls.setSlice! i s = ls := by simp [setSlice!, length_le]

@[simp_lists_simps]
theorem List.setSlice!_consecutive[Inhabited α](ls s1 s2: List α)(i j: Nat)
: i + s1.length = j
→ (ls.setSlice! i s1).setSlice! j s2 = ls.setSlice! i (s1 ++ s2)
:= by
  rintro rfl
  apply List.ext_getElem <;> simp [←getElem!_pos]
  intro p p_idx
  if p < i then
    simp_lists
  else if p < i + s1.length then
    simp_lists
  else if p < i + s1.length + s2.length then
    simp_lists
    simp [Nat.sub_add_eq]
  else
    simp_lists

@[simp] theorem List.slice_of_ge(ls: List α)(i j: Nat)
: i ≥ j → ls.slice i j = []
:= by intro cond; simp [List.slice, cond]

theorem List.slice_append_getElem(ls: List α)
  (j_idx: j < ls.length)
: i ≤ j → ls.slice i j ++ [ls[j]] = ls.slice i (j+1)
:= by
  intro proper
  simp [List.slice]
  have: ls[j] = (drop i ls)[j - i]'(by simp; omega) := by simp [*]
  rw [this, List.take_append_getElem, Nat.sub_add_comm]
  omega

@[simp_lists_simps]
theorem List.slice_append_drop(ls: List α)(j: Nat)
:  ∀ i, i ≤ j → ls.slice i j ++ ls.drop j = ls.drop i
:= by
  intros i proper
  assume j < ls.length; case otherwise =>
    simp [List.take_drop, List.take_of_length_le, not_lt.mp, List.slice, *]
  if i = j then
    simp [*, List.slice]
  else
    have: i < j := by omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt this
    rw [←List.slice_append_getElem]
    case j_idx => omega
    case a => omega
    simp
    rw [List.slice_append_drop]
    case a => omega

theorem List.setSlice!_truncate(ls s: List α)(i: Nat)
: ls.setSlice! i s = ls.setSlice! i (s.take (ls.length - i))
:= by
  conv => rhs; rw [List.setSlice!]
  simp [List.setSlice!, List.take_take, Nat.min_comm]

theorem List.getElem!_setSlice!_eq_ite_getElem!{α : Type u_1} [Inhabited α] (s s' : List α) (i j : ℕ)
: (s.setSlice! i s')[j]! =
  if i ≤ j ∧ j - i < s'.length ∧ j < s.length then
   s'[j - i]!
  else
   s[j]!
:= by
  assume j < s.length; case otherwise => simp [*, getElem!_neg]
  if h : i ≤ j ∧ j - i < s'.length then
    simp [h, List.getElem!_setSlice!_middle, *]
  else
    simp [h, *]
    simp [-not_and, not_and_or] at h
    rw [List.getElem!_setSlice!_same]
    omega

theorem List.chunks_exact_truncate{α: Type}(bs: List α)(r: Nat)
: (bs.take (r*(bs.length/r))).chunks_exact r = bs.chunks_exact r
:= by
  assume r_pos: r > 0
  case otherwise => simp at r_pos; subst r_pos; simp [List.chunks_exact]
  have r_neZero: NeZero r := NeZero.of_pos r_pos
  cases bs using List.cases_extract r
  case onSmall small =>
    unfold List.chunks_exact
    simp [*]
  case onBig chunk rest len_chunk =>
    unfold List.chunks_exact
    simp [*, r_neZero.out]
    have: r <= r*(rest.length / r + 1) := by ring_nf; simp
    have: rest.length / r + 1 = (chunk ++ rest).length / r := by simp [len_chunk, Nat.add_div_left, r_pos]
    simp_lists [len_chunk]
    simp +arith
    ring_nf
    simp +arith
    apply List.chunks_exact_truncate
termination_by bs.length
decreasing_by simp [*]

@[simp, simp_lists_simps]
theorem List.chunks_exact_nil(r: Nat): ([]: List α).chunks_exact r = [] := by unfold List.chunks_exact; simp

theorem List.chunks_exact_split{α: Type}(bs: List α)(r: Nat)(i: Nat)
: (bs.take (r*i)).chunks_exact r ++ (bs.drop (r*i)).chunks_exact r = bs.chunks_exact r
:= by
  assume r_pos: r > 0; case otherwise => simp at r_pos; simp [r_pos]
  assume i_block_idx: r*i < bs.length; case otherwise => simp_lists
  have   i_lt: i ≤ bs.length / r := by simp only [Nat.le_div_iff_mul_le r_pos, i_block_idx, le_of_lt, Nat.mul_comm i]
  have   eq_len: ((bs.take (r*i)).chunks_exact r ++ (bs.drop (r*i)).chunks_exact r).length = (bs.chunks_exact r).length := by
    simp [*, Nat.min_def, le_of_lt, Nat.add_assoc i, Nat.div_sub_mult_left]

  apply List.ext_getElem <;> simp [eq_len, ←getElem!_pos]
  intro j j_idx

  by_cases j < i
  case pos j_lhs =>
    rw [List.getElem!_append_left ]; case h => simp [*, le_of_lt]
    rw [List.getElem!_chunks_exact]; case a => simp [*, le_of_lt]
    rw [List.getElem!_chunks_exact]; case a => simp [*]
    simp [*, List.take_drop, List.take_take, ‹j + 1 ≤ i›']
  case neg j_rhs =>
    simp at j_rhs
    rw [List.getElem!_append_right]; case h => simp [*, le_of_lt]
    rw [List.getElem!_chunks_exact]; case a => simp [*, le_of_lt, Nat.div_sub_mult_left]; omega
    rw [List.getElem!_chunks_exact]; case a => simp [*]
    simp [*, le_of_lt, Nat.mul_add, Nat.mul_sub]

theorem List.range'_advance_left: len > 0 → List.range' start len = start :: List.range' (start + 1) (len - 1) := by
  intros
  have ⟨n, n_val⟩ := Nat.exists_add_one_eq.mpr ‹len > 0›
  simp only [←n_val]
  rfl

theorem List.range'_advance_right: len > 0 → List.range' start len = List.range' start (len - 1) ++ [start + len - 1] := by
  intros
  have ⟨n, n_val⟩ := Nat.exists_add_one_eq.mpr ‹len > 0›
  simp only [←n_val, List.range'_concat]
  simp

theorem List.length_fold_set[Inhabited β](init: List β)(ls: List α)
  (idx_f: α → Nat)
  (value_f: α → β)
: (List.foldl (fun b a => b.set (idx_f a) (value_f a)) (init := init) ls).length = init.length
:= by induction ls generalizing init <;> simp [*]


@[simp] theorem List.setSlice!_zero_of_length_le(ls s: List α)
: ls.length ≤ s.length
→ ls.setSlice! 0 s = s.take (ls.length)
:= by intro cond; simp [List.setSlice!, cond]

theorem List.length_slice(ls: List α): (ls.slice a b).length = (b - a) ⊓  (ls.length - a) := by simp [List.slice]


theorem List.chunks_exact_append{α: Type}(xs ys: List α)(r: Nat)
: (xs ++ ys).chunks_exact r = xs.chunks_exact r ++ (xs.drop (r*(xs.length/r)) ++ ys).chunks_exact r
:= by rw [
    ←List.chunks_exact_split (i := xs.length / r),
    List.take_append_of_le_length (h := by simp only [Nat.mul_div_le]),
    List.chunks_exact_truncate,
    List.drop_append_of_le_length (h := by simp only [Nat.mul_div_le] )
  ]

theorem List.chunks_exact_of_length_eq{α: Type}(ls: List α)(r: Nat)(r_pos: r > 0)
: ls.length = r → ls.chunks_exact r = [ls]
:= by
  intro eq
  unfold chunks_exact
  simp [eq, ‹r ≠ 0›']
