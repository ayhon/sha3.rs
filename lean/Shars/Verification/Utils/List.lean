import Aeneas.ScalarTac
import Mathlib
import Shars.Verification.Utils.SimpLikeTactics

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

#check List.take_zipWith

/- #check List.zipWith_nil -/
/- attribute [simp_lists_simps] List.take_zipWith in -/
/- @[simp_lists_simps] -/
/- theorem List.zipWith_append_right{α : Type u} (f: α → β → γ) (x : List α)(y z: List β) -/
/- : List.zipWith f x (y ++ z) = (List.zipWith f x y).take y.length ++ List.zipWith f (x.drop y.length) z -/
/- := by -/
/-   by_cases x.length < y.length -/
/-   case pos => -/
/-     simp_lists [List.zipWith_append_truncate_right] -/
/-     simp -/
/-   case neg h => -/
/-     simp at h -/
/-     have: (x.zipWith f y).length = y.length := by simp [h] -/
/-     simp_lists -/
/-     simp -/
/-     match x, y with -/
/-     | [], _ | _, [] => simp -/
/-     | a :: x', b :: y' => -/
/-       simp [List.zipWith_append_right] -/

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
private theorem Nat.sub_div_self(a b: Nat)
:(a - b) / b = a / b - 1 := by
  by_cases b > 0
  case neg h => simp at h; subst h; simp
  by_cases a >= b
  case pos h =>
    have: a = (a - b) + b := (Nat.sub_eq_iff_eq_add h).mp rfl
    rw [this, Nat.add_sub_cancel, Nat.add_div_right, Nat.add_sub_cancel]
    assumption
  case neg h =>
    simp at h
    simp [Nat.div_eq_of_lt h, Nat.sub_eq_zero_of_le (le_of_lt h)]

@[scalar_tac_simps]
private theorem Nat.sub_div_mult_left(a b: Nat)
:(a - b*i) / b = a / b - i := by
  by_cases b > 0
  case neg h => simp at h; subst h; simp
  case pos =>
    cases i
    case zero => simp
    case succ i' =>
      simp [Nat.mul_add, Nat.sub_add_eq, Nat.sub_div_self]
      rw [Nat.sub_div_mult_left]

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
      have :=  List.getElem!_chunks_exact (ls.drop r) r i' (by simp [Nat.sub_div_self]; omega)
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

/- @[simp] -/
/- theorem List.toList_toBitVec(ls: List Bool) -/
/- : ls.toBitVec.toList = ls -/
/- := by -/
/-   simp [toBitVec, BitVec.toList, finRange] -/
/-   apply List.ext_getElem -/
/-   · simp [toBitVec, BitVec.toList] -/
/-   intros -/
/-   simp -/

theorem List.length_flatten_of_uniform{n: Nat}{ls: List (List Bool)}
: (∀ xs ∈ ls, xs.length = n)
→ ls.flatten.length = n * ls.length
:= by
  intro uniform
  induction ls
  case nil => simp
  case cons hd tl ih =>
    simp [-length_flatten]
    rw [ih, uniform hd]
    · simp [Nat.mul_add, Nat.add_comm]
    · simp
    · intros; simp [*]

def List.matrix_idx(ls: List (List α))(i: Nat)(acc: Nat := 0): Nat × Nat :=
  match ls with
  | [] => (acc, i)
  | hd :: tl => 
    if i < hd.length then
      (acc, i)
    else
      List.matrix_idx tl (i - hd.length) (acc + 1)

theorem List.acc_le_matrix_idx_1(ls: List (List α))(i acc: Nat)
: acc ≤ (ls.matrix_idx i acc).1 
:= by
  unfold List.matrix_idx
  match ls with
  | [] => simp
  | hd :: tl =>
    if i < hd.length then
      simp [*]
    else
      simp [*]
      have := List.acc_le_matrix_idx_1 tl (i - hd.length) (acc + 1)
      omega

theorem List.getElem!_flatten (ls: List (List Bool))(i: Nat)(acc: Nat)
: let (x,y) := ls.matrix_idx i acc
  ls.flatten[i]! = (ls[x - acc]!)[y]!
:= by
  simp only
  match ls with
  | [] => simp [default]
  | hd :: tl =>
    simp
    if i < hd.length then
      simp [List.matrix_idx, *]
    else
      simp [List.matrix_idx, *]
      simp_lists
      rw [List.getElem!_flatten tl (acc := acc + 1)]
      conv => enter [2, 1, 2, 2]; rw [show acc = (acc + 1) - 1 from rfl]
      conv => enter [2, 1, 2]; rw [tsub_tsub_eq_add_tsub_of_le (Nat.le_add_left 1 acc)]
      rw [Nat.sub_add_comm]
      simp
      simp [List.acc_le_matrix_idx_1]

/- attribute [-simp] List.length_flatten in -/
/- theorem List.matrix_idx_of_uniform(ls: List (List Bool)) -/
/- : (∀ xs ∈ ls, xs.length = n) -/
/- → n > 0 -/
/- → i < ls.flatten.length -/
/- → ls.matrix_idx i acc = (acc + i / n, i % n) -/
/- := by -/
/-   intro uniform n_pos i_idx -/
/-   simp [List.length_flatten_of_uniform uniform] at i_idx -/
/-   match ls with -/
/-   | [] => simp at i_idx -/
/-   | hd :: tl => -/
/-     simp [Nat.mul_add] at i_idx -/
/-     if h: i < hd.length then -/
/-       rw [uniform] at h; case a => simp -/
/-       simp [*, matrix_idx, Nat.div_eq_of_lt, Nat.mod_eq_of_lt] -/
/-     else -/
/-       rw [uniform] at h; case a => simp -/
/-       simp [*, matrix_idx] -/
/-       have ih := List.matrix_idx_of_uniform (n := n) (i := i - n) (ls := tl) (acc := acc + 1) -/
/-       sorry -/
/-       rw [ih] -/
/-       · simp [Nat.sub_div] -/
