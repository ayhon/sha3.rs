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

attribute [simp_lists_simps] List.length_append List.take_append_eq_append_take List.take_zipWith List.length_zipWith List.length_take List.take_all_of_le List.length_drop List.drop_eq_nil_of_le List.drop_append_eq_append_drop List.nil_append List.zipWith_nil_left List.append_nil List.drop_drop List.take_take

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

@[simp_lists_simps]
theorem List.zipWith_append_right{α : Type u} (f: α → β → γ) (x : List α)(y z: List β)
: List.zipWith f x (y ++ z) = (List.zipWith f x y).take y.length ++ List.zipWith f (x.drop y.length) z
:= by
  by_cases x.length < y.length
  case pos =>
    simp_lists [List.zipWith_append_truncate_right]
  case neg h =>
    simp_lists
    match x, y with
    | [], _ | _, [] => simp
    | a :: x', b :: y' =>
      simp [List.zipWith_append_right]

@[simp]
theorem List.drop_eq_drop(ls: List α)(n m: Nat)
: ls.drop n = ls.drop m ↔ n = m ∨ (n ≥ ls.length ∧ m ≥ ls.length)
:= by sorry

@[simp]
theorem BitVec.length_toList(bv: BitVec n)
: bv.toList.length = n
:= by simp [toList]

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
theorem List.getElem!_take[Inhabited α](ls: List α)(i n: Nat)
: i < n → (ls.take n)[i]! = ls[i]!
:= by
  by_cases i < ls.length
  case pos h =>
    intro h2
    apply List.getElem!_take_same <;> assumption
  case neg =>
    intro
    simp_lists

attribute [simp_lists_simps] List.getElem!_drop

@[simp_lists_simps]
theorem List.getElem!_zipWith[Inhabited α] [Inhabited β] [Inhabited c]
  (a: List α)(b:List β)(f: α → β → c)(i: Nat)
: i < a.length
→ i < b.length
→ (a.zipWith f b)[i]! = f a[i]! b[i]!
:= by intros; simp [←getElem_eq_getElem!, *]

@[simp_lists_simps]
theorem List.getElem!_zip[Inhabited α] [Inhabited β]
  (a: List α)(b:List β)(i: Nat)
: i < a.length
→ i < b.length
→ (a.zip b)[i]! = (a[i]!,b[i]!)
:= by apply List.getElem!_zipWith (f := (·,·))

/- theorem List.getElem!_append[Inhabited α](ls1 ls2: List α) -/
/- : (ls1 ++ ls2)[i] = -/
attribute [simp_lists_simps] List.getElem!_append_left List.getElem!_append_right

attribute [simp_lists_simps] Nat.min_eq_left
attribute [simp_lists_simps] Nat.min_eq_right

@[simp_lists_simps]
theorem getElem!_eq_default[Inhabited α]
  (ls: List α)(i: Nat)
: i ≥ ls.length
→ ls[i]! = default
:= by intro oob; simp [getElem!_def, getElem?_eq_none, oob]

attribute [simp_lists_simps] List.length_replicate List.getElem!_replicate

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

theorem getElem!_default [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
  [Inhabited elem] (c : cont) (i : idx) (h : ¬ dom c i)
: getElem! c i = default
:= by
  have : Decidable (dom c i) := .isFalse h
  simp [getElem!_def, getElem?_def, h]


@[simp_lists_simps]
theorem List.getElem!_append[Inhabited α]
  (ls ls2: List α)(i: Nat)
: (ls ++ ls2)[i]! = if i < ls.length then ls[i]! else ls2[i - ls.length]!
:= by split <;> simp_lists

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
      rw [getElem!_default]
      case h => simpa using h
      rw [getElem!_default]
      case h => scalar_tac

attribute [simp_lists_simps] List.length_map List.length_finRange

@[simp]
theorem BitVec.toList_append(bv: BitVec n)(bv2: BitVec m)
: (bv2 ++ bv).toList = bv.toList ++ bv2.toList
:= by
  simp [toList, BitVec.getElem_append]
  apply List.ext_getElem!
  · simp_arith
  intro i
  simp_lists
  by_cases h: i < n
  case pos =>
    simp [h, ‹i < m + n›']
    congr
  case neg =>
    simp [h]
    split
    case isTrue h =>
      simp [‹i < m + n›']
      congr
    case isFalse h =>
      simp [‹¬ i < m + n›']

@[simp]
theorem BitVec.toList_toArray(bv: BitVec n)
: bv.toArray.toList = bv.toList
:= by simp [toArray, toList, Array.finRange, List.finRange]

@[simp]
theorem BitVec.toArray_append(bv: BitVec n)(bv2: BitVec m)
: (bv2 ++ bv).toArray = bv.toArray ++ bv2.toArray
:= by
  apply Array.toList_inj.mp
  simp [BitVec.toList_append]

@[simp]
theorem BitVec.size_toArray(bv: BitVec n)
: bv.toArray.size = n
:= by simp [toArray, Array.finRange]

@[simp]
theorem BitVec.getElem!_toList(bv: BitVec n)(i: Nat)
: bv.toList[i]! = bv[i]!
:= by
  simp [toList]
  by_cases i < n
  case neg h =>
    rw [getElem!_default]
    case h => simpa using h
    rw [getElem!_default]
    case h => simpa using h
  simp [List.getElem!_map, *, getElem_eq_getElem!]

@[simp]
theorem BitVec.getElem!_toArray(bv: BitVec n)(i: Nat)
: bv.toArray[i]! = bv[i]!
:= by
  have: bv.toArray[i]! = bv.toList[i]! := by
    simp [toList, toArray]
    by_cases i_idx: i < n
    case neg =>
      rw [getElem!_default]
      case h => simpa [Array.finRange] using i_idx
      rw [getElem!_default]
      case h => simpa [Array.finRange] using i_idx
    rw [getElem!_pos (h := by simpa [Array.finRange] using i_idx)]
    rw [getElem!_pos (h := by simpa using i_idx)]
    simp [Array.finRange]
  rw [this]
  apply getElem!_toList

#check Array.getElem!_append

theorem Array.getElem!_toList[Inhabited α](arr: Array α)(i: Nat)
: arr.toList[i]! = arr[i]!
:= by congr


theorem getElem!_padding(x m: Nat)(i: Nat)
: (Spec.«pad10*1» x m)[i]! = if i = 0 ∨ i = (Spec.«pad10*1» x m).size - 1 then true else false
:= by
  split
  case isTrue h =>
    simp [Spec.«pad10*1»]
    obtain h | h := h
    · simp [h]; congr
    · simp [h, Spec.«pad10*1»]; congr
  case isFalse h =>
    by_cases i_idx: i < (Spec.«pad10*1» x m).size
    case neg => simp [getElem!_default, i_idx]
    simp [Spec.«pad10*1»] at h i_idx ⊢
    simp_ifs
    rw [getElem!_pos]
    case h => scalar_tac
    simp

@[simp_lists_simps, simp]
theorem List.getElem!_singleton[Inhabited α](a: α)
: i = 0 → [a][i]! = a
:= by rintro rfl; congr

attribute [simp_lists_simps] List.append_left_eq_self List.replicate_eq_nil_iff

attribute [simp_lists_simps] List.take_append_drop

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

theorem ref.mod_manipulation(a b r: Nat)
  (h1: r ≥ 6)
  (h2: a < r)
  (h3: b <= 4)
  (h4: (a + b) ≥ r)
: ((- (a + b + 2: Int)) % r).toNat = 2*r - (a + b + 2)
:= by
  have: ((- (a + b + 2: Int)) % r) ≡ 2*r - (a + b + 2) [ZMOD r] := by
    ring_nf
    calc _
      _ ≡ -2 + (-a.cast + -b.cast) [ZMOD r] := by apply Int.mod_modEq
      _ ≡ -2 + (-a.cast + -b.cast) + r [ZMOD r] := by exact Int.ModEq.symm Int.add_modEq_right
      _ ≡ -2 + (-a.cast + -b.cast) + r + r [ZMOD r] := by exact Int.ModEq.symm Int.add_modEq_right
      _ ≡ -2 + (-a.cast + -b.cast) + 2* r [ZMOD r] := by ring_nf; rfl
    ring_nf; rfl
  have := this.eq
  simp [Int.emod_emod] at this ⊢
  simp [this]
  have: (2*r - (a + b + 2): Int) >= 0 := by omega
  have: (2*r - (a + b + 2): Int) < r := by omega
  rw [Int.emod_eq_of_lt]
  case H1 => omega
  case H2 => omega
  zify
  rw [Int.toNat_of_nonneg (by omega)]
  rw [Nat.cast_sub (by omega)]
  simp


open Aeneas hiding Std.Array
open Std.alloc.vec

attribute [ext (iff := false)] List.ext_getElem!


theorem Spec.«pad10*1_length» (x m : Nat)
: (Spec.«pad10*1» x m).size = (2 + (-(m + 2: Int) % x).toNat)
:= by
  simp_arith [«pad10*1», neg_add, -neg_add_rev, -Int.reduceNeg]
  rfl

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

def absorb.upd(S: BitVec (Spec.b 6))(P: Vector Bool r): BitVec (Spec.b 6) :=
  Spec.Keccak.P 6 24 (S ^^^ (BitVec.ofBoolListLE <| P.toList).setWidth (Spec.b 6))

def absorb{r: Nat}(S: BitVec (Spec.b 6))(Ps: Array (Vector Bool r)) := Id.run do
  let mut S := S
  for P in Ps do
    S := absorb.upd S P
  return S

def ref.xor_long_at(s rest: List Bool)(offset: Nat): List Bool :=
  s.take offset ++ (s.drop offset |>.zipWith (· ^^ ·) rest) ++ s.drop (offset + rest.length)
def ref.xor_long(s rest: List Bool): List Bool := xor_long_at s rest 0

theorem ref.xor_long.def(s rest: List Bool)
: xor_long s rest = s.zipWith (· ^^ ·) rest ++ s.drop rest.length
:= by simp [xor_long, xor_long_at]

@[simp, scalar_tac_simps]
theorem ref.length_xor_long_at(s rest: List Bool)
: (xor_long_at s rest offset).length = s.length
:= by simp [xor_long_at, List.length_zipWith]; omega

def simple.sponge_absorb_final.panic_free
  (keccak_p: List Bool → List Bool)
  (r: Nat)
  (s rest suffix: List Bool)
: List Bool
:= Id.run do
  let mut s := s
  s := ref.xor_long s rest
  let nb_left := rest.length + suffix.length
  if nb_left >= r then
    s := ref.xor_long_at s (suffix.take (r - rest.length)) rest.length
  -- if nb_left >= r then
    s := keccak_p s
    s := ref.xor_long s (suffix.drop (r - rest.length))
    s := ref.xor_long_at s [true] (rest.length + suffix.length - r)
    s := ref.xor_long_at s [true] (r-1)
  else
    s := ref.xor_long_at s suffix rest.length
    s := ref.xor_long_at s [true] nb_left
    if nb_left + 1 < r then
      s := ref.xor_long_at s [true] (r-1)
    else
      s := keccak_p s
      s := ref.xor_long_at s [true] (r-1)
  keccak_p s

def ref.list_keccak_p(s: List Bool): List Bool :=
  let state := s.toBitVec.setWidth (Spec.b 6)
  let state := Spec.Keccak.P 6 24 state
  state.toList

def ref.absorb' (f: List Bool → List Bool) (s: List Bool) (chunks: List (List Bool)): List Bool := Id.run do
  let mut s := s
  for Pi in chunks do
    s := f (xor_long s Pi)
  return s

abbrev ref.interesting_part_of_the_proof.preconditions(r: Nat)(rest suffix: List Bool) :=
  r ≥ 6 -- Otherwise, we don't have suffix + 2 ≤ r
∧ suffix.length ≤ 4 -- Taken from the actual uses of `suffix` in SHA3
∧   rest.length < r -- Since rest is what's left after absorb_initial

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 1000000 in
theorem ref.interesting_part_of_the_proof.case1{r: Nat}{rest suffix: List Bool}
  (hyp: (rest ++ suffix).length ≥ r)
: preconditions r rest suffix
→ let padding := (Spec.«pad10*1» r (rest.length + suffix.length)).toList
  (rest ++ suffix ++ padding).chunks_exact r = [(rest ++ suffix).take r, (suffix.drop (r - rest.length) ++ padding)]
:= by
  /-
  · (rest ++ suffix) >= r
    Then we have
     (rest ++ suffix ++ padding).chunks_exact k =
     = [(rest ++ suffix).take r, (suffix.drop (r - rest.length) ++ padding)]
  -/
  rintro ⟨r_big_enough,suffix_len_le,rest_len_lt⟩ padding
  have len_padding: (Spec.«pad10*1» r (rest.length + suffix.length)).size = 2*r - (rest.length + suffix.length) := by
    simp [Spec.«pad10*1_length», -neg_add_rev]
    have := mod_manipulation (h1 := r_big_enough) (h2 := rest_len_lt) (h3 := suffix_len_le) (h4 := by scalar_tac)
    rw [this]
    scalar_tac
  have len_append: (rest.length + suffix.length + padding.length) = 2*r := by
    simp [padding, len_padding]
    scalar_tac
  simp at hyp
  have len_chunks: ((rest ++ suffix ++ padding).chunks_exact r).length = 2 := by
    simp
    rw [←Nat.add_assoc, len_append, Nat.mul_div_cancel]
    omega

  -- Execute List.chunks_exact
  unfold List.chunks_exact
  simp_ifs
  unfold List.chunks_exact
  simp_ifs
  unfold List.chunks_exact
  simp_ifs

  congr 1
  · ext i
    · simp [←Nat.add_assoc, len_append]
      omega
    by_cases i < r
    case neg => simp_lists
    rw [List.getElem!_take_append_beg]
    case pos.x => assumption
    case pos.x => simp; omega
    rw [List.getElem!_take]
    case pos.a => assumption
  · congr
    ext i
    · simp [←Nat.add_assoc, len_append]
      omega
    simp_lists
    congr
    omega

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 1000000 in
theorem ref.interesting_part_of_the_proof.case2{r: Nat}{rest suffix: List Bool}
  (hyp: (rest ++ suffix).length = r-1)
: preconditions r rest suffix
→ let padding := (Spec.«pad10*1» r (rest.length + suffix.length)).toList
  (rest ++ suffix ++ padding).chunks_exact r = [rest ++ suffix ++ [true], List.replicate (r-1) false ++ [true]]
:= by
  /-
  · (rest ++ suffix) = r - 1
    Then we have
     (rest ++ suffix ++ padding).chunks_exact k =
     = [rest ++ suffix ++ [true], List.replicate false (r-1) ++ [true]]
  -/
  rintro ⟨r_big_enough,suffix_len_le,rest_len_lt⟩ padding
  have len_padding: (Spec.«pad10*1» r (rest.length + suffix.length)).size = 2*r - (rest.length + suffix.length) := by
    simp at hyp
    simp [Spec.«pad10*1_length», -neg_add_rev, hyp, r_big_enough]
    zify
    rw [Nat.cast_sub (by omega)]
    rw [Nat.cast_sub (by omega)]
    rw [Nat.cast_sub (by omega)]
    rw [Nat.cast_mul]
    ring_nf
    simp
    rw [
      Int.neg_emod,
      Int.emod_eq_of_lt (H1:=by omega) (H2:=by omega),
      Int.max_eq_left (by omega)
    ]
    omega
  have len_append: (rest.length + suffix.length + padding.length) = 2*r := by
    simp [padding, len_padding]; scalar_tac

  simp at hyp
  have len_chunks: ((rest ++ suffix ++ padding).chunks_exact r).length = 2 := by
    simp
    rw [←Nat.add_assoc, len_append, Nat.mul_div_cancel]
    omega

  -- Execute List.chunks_exact
  unfold List.chunks_exact
  simp_ifs
  unfold List.chunks_exact
  simp_ifs
  unfold List.chunks_exact
  simp_ifs
  congr
  · ext i
    · simp; scalar_tac
    simp_lists
    congr
    simp [hyp, Nat.sub_sub_self, ‹r >= 1›', List.take_one, List.head?, padding, Spec.«pad10*1», BitVec.toList]
  · ext i
    · simp; scalar_tac
    simp_lists
    simp [hyp] at len_padding
    simp [hyp, Nat.sub_sub_self, ‹r >= 1›', padding, Array.getElem!_toList, getElem!_padding, len_padding,
       -Bool.if_false_right, -Bool.if_false_left, -Bool.if_true_left] -- Keep `if`s for `simp_ifs` to process
    by_cases i = r -1
    case pos h => simp_ifs [h]; simp
    case neg =>
      simp_ifs
      by_cases i > r - 1
      case neg => simp_ifs
      case pos =>
        simp_ifs
        rw [getElem!_default]
        simp
        scalar_tac

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 1000000 in
theorem ref.interesting_part_of_the_proof.case3{r: Nat}{rest suffix: List Bool}
  (hyp: (rest ++ suffix).length <= r-2)
: preconditions r rest suffix
→ let padding := (Spec.«pad10*1» r (rest.length + suffix.length)).toList
  (rest ++ suffix ++ padding).chunks_exact r = [rest ++ suffix ++ [true] ++ List.replicate (r -2 - rest.length - suffix.length) false ++ [true]]
:= by
  /-
  · (rest ++ suffix) <= r - 2
    Then we have
     (rest ++ suffix ++ padding).chunks_exact k =
     = [rest ++ suffix ++ [true, true]]
  -/
  rintro ⟨r_big_enough,suffix_len_le,rest_len_lt⟩ padding
  have len_padding: (Spec.«pad10*1» r (rest.length + suffix.length)).size = r - (rest.length + suffix.length) := by
    simp at hyp
    simp [Spec.«pad10*1_length», -neg_add_rev]
    zify
    rw [Nat.cast_sub (by omega)]
    rw [Int.neg_emod]
    rw [Int.emod_eq_of_lt (H1:=by omega) (H2:=by omega)]
    simp
    rw [Int.max_eq_left (by omega)]
    omega
  have len_append: (rest.length + suffix.length + padding.length) = r := by
    simp [padding, len_padding]
    scalar_tac
  have len_chunks: ((rest ++ suffix ++ padding).chunks_exact r).length = 1 := by
    simp [←Nat.add_assoc, len_append, Nat.div_self, ‹r > 0›']

  unfold List.chunks_exact
  simp_ifs

  unfold List.chunks_exact
  simp_ifs
  simp
  ext i
  · simp; scalar_tac
  simp_lists
  congr
  simp [padding, Spec.«pad10*1», BitVec.toList]
  have := Spec.«pad10*1_length» r (rest.length + suffix.length)
  simp at this
  ring_nf at this ⊢
  scalar_tac

@[simp]
theorem ref.length_list_keccak_p(ls: List Bool)
: (list_keccak_p ls).length = 1600
:= by simp [list_keccak_p, Spec.b, Spec.w]

theorem ref.xor_long_at_twice_compatible(a b c: List Bool)(offset: Nat)
(compatible_offset: offset2 = b.length + offset)
: xor_long_at (xor_long_at a b offset) c (offset2) -- Not offset + b.length so if offset is 0, it's defeq to b.length
= xor_long_at a (b ++ c) offset
:= by
  subst compatible_offset
  simp only [xor_long_at]
  simp_lists
  simp only [List.append_assoc]
  congr 2

  by_cases offset_idx: offset ≥ a.length
  case pos => simp_lists
  case neg =>
    simp at offset_idx
    simp [offset_idx, le_of_lt]
    by_cases h: (a.length - offset) ≤ b.length
    case pos => simp_lists
    case neg =>
      simp [le_of_lt (not_le.mp h)]
      simp_arith

@[simp_lists_simps]
theorem ref.getElem!_xor_long_at_inside(a b: List Bool)(offset i: Nat)
: offset ≤ i ∧ i < offset + b.length
→ i < a.length
→ (ref.xor_long_at a b offset)[i]! = (a[i]! ^^ b[i - offset]!)
:= by
  intro cond i_idx
  simp [xor_long_at]
  simp_lists
  simp_arith [cond]

@[simp_lists_simps]
theorem ref.getElem!_xor_long_at_outside(a b: List Bool)(offset i: Nat)
: ¬ (offset ≤ i ∧ i < offset + b.length)
→ (xor_long_at a b offset)[i]! = a[i]!
:= by
  intro cond
  simp only [not_le, not_lt, not_and_or] at cond
  by_cases h: i < a.length
  case neg =>
    have : ¬ i < (xor_long_at a b offset).length := by simpa using h
    simp_lists
  simp [xor_long_at]
  obtain h | h := cond
  · simp_lists
  · simp_lists
    congr
    scalar_tac

@[simp_lists_simps]
theorem ref.getElem!_xor_long_at(a b: List Bool)(offset i: Nat)
: (xor_long_at a b offset)[i]! = if offset ≤ i ∧ i < offset + b.length ∧ i < a.length then a[i]! ^^ b[i - offset]! else a[i]!
:= by
  split
  case isTrue inRange =>
    obtain ⟨range, idx⟩ := inRange
    simp_lists
  case isFalse oob =>
    simp [-not_and, not_and_or] at oob
    obtain i_under | i_over | i_oob := oob
    · simp_lists
    · simp_lists
    · have : ¬ i < (xor_long_at a b offset).length := by simpa using i_oob
      simp_lists

theorem ref.xor_long_at_twice_separate(a b c: List Bool)(offset: Nat)
(compatible_offset: offset2 ≥ offset + b.length)
: xor_long_at (xor_long_at a b offset) c (offset2) -- Not offset + b.length so if offset is 0, it's defeq to b.length
= xor_long_at a (b ++ List.replicate (offset2 - (b.length + offset)) false ++ c) offset
:= by
  ext i
  case hl => simp

  by_cases i_idx: i < a.length
  case neg => simp_lists

  simp_lists
  split
  case pos.isTrue first_range =>
    simp_ifs
    simp_lists
    congr 2
    scalar_tac
  case pos.isFalse not_first_range =>
    split
    case isTrue second_range =>
      simp_ifs
      simp_lists
    case isFalse not_second_range =>
      by_cases in_middle: offset + b.length ≤ i ∧ i < offset2
      case pos =>
        simp_ifs
        simp_lists
        simp
      case neg =>
        simp_ifs

theorem ref.xor_long_of_xor_long_at(a b: List Bool)(offset: Nat)
: xor_long_at a b offset = xor_long a (List.replicate offset false ++ b)
:= by
  ext i
  · simp [xor_long]
  simp [xor_long]
  simp_lists
  split
  case isTrue _ =>
    simp_ifs
    rw [List.getElem!_append_right]
    case h => simp [*]
    simp
  case isFalse _ =>
    split
    case isTrue h =>
      rw [List.getElem!_append_left]
      case h => scalar_tac
      simp_lists
      simp
    case isFalse h => rfl


theorem ref.interesting_part_of_the_proof.proof(r: Nat)(s rest suffix: List Bool)
: preconditions r rest suffix
→ let f := list_keccak_p
  let padding := (Spec.«pad10*1» r (rest.length + suffix.length)).toList
  simple.sponge_absorb_final.panic_free f r s rest suffix =
    absorb' f s (
      (rest ++ suffix ++ padding).chunks_exact r
    )
:= by
  rintro precond f padding
  have ⟨r_big_enough,suffix_len_le,rest_len_lt⟩ := precond
  /-
  There are three cases we must consider:
  · (rest ++ suffix) >= r
    Then we have
     (rest ++ suffix ++ padding).chunks_exact k =
     = [(rest ++ suffix).take r, (suffix.drop (r - rest.length) ++ padding)]
  · (rest ++ suffix) = r - 1
    Then we have
     (rest ++ suffix ++ padding).chunks_exact k =
     = [rest ++ suffix ++ [true], List.replicate false (r-1) ++ [true]]
  · (rest ++ suffix) <= r - 2
    Then we have
     (rest ++ suffix ++ padding).chunks_exact k =
     = [rest ++ suffix ++ [true, true]]
  -/
  if      cond1: (rest ++ suffix).length ≥ r then
    rw [case1 cond1 precond]
    simp at cond1
    simp [absorb', simple.sponge_absorb_final.panic_free, *, xor_long]

    generalize leftover_val: (rest.length + suffix.length - r) = leftover
    rw [ref.xor_long_at_twice_separate]
    case compatible_offset => scalar_tac

    rw [ref.xor_long_at_twice_separate]
    case compatible_offset => scalar_tac

    rw [ref.xor_long_at_twice_separate]
    case compatible_offset => scalar_tac

    congr
    · simp_arith [List.take_append_of_ge_length, le_of_lt rest_len_lt]
    · simp_arith
      scalar_tac
    · have padding_len
      : (Spec.«pad10*1» r (rest.length + suffix.length)).size = 2 * r - rest.length - suffix.length
      := by
        simp [Spec.«pad10*1»]
        have: (2: Int) = (2: Nat).cast := by congr
        rw [this]
        have(a b: Int): a - b = a + -b := by exact rfl
        rw [this]
        simp only [←Nat.cast_sub, ←neg_add, Nat.cast_add]
        conv =>
          lhs
          rhs
          rw [Nat.cast_ofNat]
          conv => enter [1, 1, 1, 1, 1]; rw [Int.add_comm]
          rw [mod_manipulation (h1 := r_big_enough) (h2 := rest_len_lt) (h3 := suffix_len_le) (h4 := cond1)]
        scalar_tac

      ext i
      · simp [padding_len]
        scalar_tac
      conv => rhs; rw [Array.getElem!_toList]
      simp [getElem!_padding, -List.cons_append, -List.singleton_append, -List.cons_append_fun]
      by_cases h: i = 0
      case pos => simp [h]
      by_cases h: i = (Spec.«pad10*1» r (rest.length + suffix.length)).size - 1
      -- by_cases h: i = 2* r - rest.length - suffix.length - 1
      case pos =>
        rw [List.getElem!_append_right]
        case h => scalar_tac
        rw [List.getElem!_append_right]
        case h => scalar_tac
        simp [h, padding_len, ←leftover_val]
        rw [List.getElem!_singleton]
        scalar_tac
      by_cases h: i < (Spec.«pad10*1» r (rest.length + suffix.length)).size
      case neg =>
        rw [getElem!_default]
        case h => simp [Spec.«pad10*1»] at *; scalar_tac
        simp [Spec.«pad10*1»] at *
        simp [*]
      case pos =>
        rw [getElem!_pos]
        case h => simp [padding_len] at *; scalar_tac
        rw [List.getElem_append_right]
        case h₁ => scalar_tac
        rw [List.getElem_append_left]
        case h => scalar_tac
        simp [padding_len] at *; simp [*]
        scalar_tac

  else if cond2: (rest ++ suffix).length = r - 1 then
    rw [case2 cond2 precond]
    replace cond2 := ‹r = (rest ++ suffix).length + 1›'
    simp [absorb', simple.sponge_absorb_final.panic_free, *, xor_long]

    rw [ref.xor_long_at_twice_separate]
    case compatible_offset => scalar_tac

    rw [ref.xor_long_at_twice_separate]
    case compatible_offset => scalar_tac

    simp [ref.xor_long_of_xor_long_at]
    congr
    -- have{α: Type}(x ls: List α): (x ++ ls) = ls ↔ x = [] := by exact?
    simp_lists
    scalar_tac
  else if cond3: (rest ++ suffix).length ≤ r - 2 then
    rw [case3 cond3 precond]
    simp at cond3
    simp [absorb', simple.sponge_absorb_final.panic_free, *, xor_long]
    simp_ifs

    rw [ref.xor_long_at_twice_separate]
    case compatible_offset => scalar_tac

    rw [ref.xor_long_at_twice_separate]
    case compatible_offset => scalar_tac

    rw [ref.xor_long_at_twice_separate]
    case compatible_offset => scalar_tac

    simp only [ref.xor_long_of_xor_long_at]
    congr
    · simp
    · rw [List.append_right_eq_self, List.replicate_eq_nil_iff]
      -- scalar_tac -- TODO: Gives maxRecDepth error
      omega
    · simp only [List.length_singleton, Nat.sub_add_eq]
      congr

  else omega -- Absurd


theorem absorb_def{r: Nat}(S: BitVec (Spec.b 6))(Ps: Array (Vector Bool r))
: absorb S Ps = Ps.foldl (absorb.upd · ·) S
:= by simp [absorb, ←Array.foldl_toList,-Array.size_chunks_exact, -Array.size_map]

theorem absorb.spec (N : Array Spec.Bit) (r: Nat)(r_pos: r > 0)
: spec_sponge_absorb r r_pos N = absorb (0#(Spec.b 6)) ((N ++ Spec.«pad10*1» r N.size).chunks_exact r)
:= by
  rw [spec_sponge_absorb, Spec.sponge.absorb, absorb]
  -- NOTE: I needed to exercise a bit too much control here.
  simp [←Array.foldl_toList,-Array.size_chunks_exact, -Array.size_map, upd]

attribute [simp] Aeneas.Std.core.slice.index.Slice.index

theorem Array.foldl_extract(arr: Array α)(l r: Nat)(upd: β → α → β)(init: β)
: (arr.extract l r).foldl upd init = arr.foldl upd init l r
:= by simp only [foldl, ←foldlM_start_stop (m := Id)]

theorem BitVec.cast_xor(bv bv2: BitVec n)(eq: n = m)
: (bv ^^^ bv2).cast eq = bv.cast eq ^^^ bv2.cast eq
:= by ext i i_lt; simp

@[simp]
theorem length_absorb'(s: List Bool)(chunks: List (List Bool))
: (absorb' s chunks).length = s.length
:= by
  simp [absorb']
  induction chunks using List.reverseRecOn
  case nil => simp
  case append_singleton init last ih =>
    simp [*]
    by_cases h: (s.length > last.length) <;> simp at h
    · simp [Nat.min_eq_right, le_of_lt, *]
    · simp [Nat.min_eq_left, *]

def List.chunks_exact'(k: Nat)(ls: List α): List (List α) :=
  if ls.length < k ∨ k = 0 then
    return []
  else
    let chunk := (ls.take k)
    let rest := (ls.drop k).chunks_exact' k
    chunk :: rest
termination_by ls.length
decreasing_by simp_wf; omega

@[progress]
theorem Aeneas.Std.Array.to_slice_mut.spec{α : Type u} {n : Usize} (a : Array α n)
: ∃ old new,
  Std.toResult (a.to_slice_mut) = .ok (old, new) ∧
  old = a.to_slice ∧
  new = a.from_slice
:= by simp [to_slice_mut, Std.toResult]

/- set_option maxHeartbeats 1000000 in -/
/- @[progress] -/
/- theorem simple.sponge_absorb_initial_loop.spec' -/
/-   (bs : Std.Slice Bool) (r : Std.Usize) (s : Aeneas.Std.Array Bool 1600#usize) (n i : Std.Usize) -/
/- : n.val = bs.length / r.val -/
/- → (r_pos: r.val > 0) -/
/- → i.val ≤ n.val -/
/- → r.val < 1600 -/
/- → ∃ output, -/
/-   sponge_absorb_initial_loop bs r s n i = .ok output ∧ -/
/-   output.val = (absorb' (s.val) (bs.val.chunks_exact r |>.drop i)) -/
/- := by -/
/-   rintro n_val r_pos i_loop_bnd r_le -/
/-   rw [sponge_absorb_initial_loop] -/
/-   split -/
/-   case isTrue i_idx => -/
/-     have _: r.val*i.val ≤ bs.length := sorry -- r * i < r * n = r * (bs.length / r) ≤ bs.length ≤ Usize.max -/
/-     have _: r.val*(i.val + 1) ≤ bs.length := sorry -- r * (i + 1) ≤ r * n = r * (bs.length / r) ≤ bs.length ≤ Usize.max -/

/-     let* ⟨ i1, i1_post ⟩ ← Std.Usize.mul_spec -/
/-     let* ⟨ i2, i2_post ⟩ ← Std.Usize.add_spec -/
/-     let* ⟨ i3, i3_post ⟩ ← Std.Usize.mul_spec -/
/-     let* ⟨ chunk, chunk_post ⟩ ← Std.core.slice.index.Slice.index.slice_index_range_usize_slice_spec -/
/-     let* ⟨ old_slice, new_slice, old_slice_post, new_slice_post ⟩ ← Std.Array.to_slice_mut.spec -/
/-     let* ⟨ s2, s2_post_1, s2_post_2 ⟩ ← xor_long.spec' -/
/-     let* ⟨ s4, s4_post ⟩ ← keccak_p.spec' -/
/-     let* ⟨ res, res_post ⟩ ← spec' -/

/-     simp [*, absorb'] -/
/-     rw [←List.cons_getElem_drop_succ (n := i.val)] -/
/-     simp -/
/-   . sorry -/
/-   -- TODO -/

abbrev List.chunks_exact(ls: List α)(k: Nat): List (_root_.Vector α k) := ls |> Array.mk  |>.chunks_exact k |>.toList

theorem Array.toList_foldl(arr: _root_.Array α)
: arr.toList.foldl upd init = (arr.foldl upd init)
:= by
  simp only [foldl_toList]

theorem Array.foldl_mk(ls: List α)
: (Array.mk ls).foldl upd init = (ls.foldl upd init)
:= by
  simp only [size_toArray, List.foldl_toArray']

attribute [simp] Std.Slice
set_option maxHeartbeats 1000000 in
@[progress]
theorem simple.sponge_absorb_initial_loop.spec
  (bs : Std.Slice Bool) (r : Std.Usize) (s : Aeneas.Std.Array Bool 1600#usize) (n i : Std.Usize)
: n.val = bs.length / r.val
→ (r_pos: r.val > 0)
→ i.val ≤ n.val
→ r.val < 1600
→ ∃ output,
  sponge_absorb_initial_loop bs r s n i = .ok output ∧
  output.val.toBitVec = (
    (
      absorb (s.val.toBitVec.cast (by simp [Spec.w, Spec.b])) (bs.val.toArray.chunks_exact r |>.drop i)
    ).cast (by simp [Spec.w, Spec.b])
  )
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
    fsimp only [*] at slice_post
    let* ⟨old_slice, new_slice, slice_mut_post⟩ ← Std.Array.to_slice_mut.progress_spec

    simp [Std.Array.to_slice_mut, Std.Array.to_slice] at slice_mut_post
    obtain ⟨old_slice_post, new_slice_post⟩ := slice_mut_post

    let* ⟨ s2, s2_len, s2_post ⟩ ← xor_long.spec
    rw [old_slice_post] at s2_post
    simp [s2_len] at s2_post

    rw [slice_post] at s2_post
    simp at s2_len
    /- rw [s2_len] at s2_post -/ -- NOTE: Annoying that this doesn't work (setWidth's type depends on argument)

    let* ⟨ s4, s4_post ⟩ ← keccak_p.spec
    let* ⟨rest, rest_post ⟩ ← spec

    simp [*]
    apply congrArg
    rw [absorb_def, absorb_def]
    simp only [Array.foldl_extract]
    rw [Array.foldl_step_right (l := i)]
    case l_idx  | r_le | nontriv => (first | simp; done | simpa [n_val] using i_idx)
    congr
    ext idx idx_idx
    simp [*]
    rw [List.toBitVec] at s2_post
    rw [←BitVec.getElem_ofBoolListLE, s2_post]
    simp [Std.Array.from_slice, s2_post, old_slice_post, new_slice_post, ‹s2.length = 1600›']

    rw [getElem_eq_getElem!,Array.getElem!_chunks_exact]
    case i_idx | k_pos => (first | assumption | simpa [n_val] using i_idx)

    simp
  case isFalse i_oob =>
    have := ‹bs.length / r.val - i.val = 0›'
    simp [absorb, this, Array.foldl,Array.foldlM_start_stop (m := Id)]
    rw [Array.extract_empty]
    simp
termination_by n.val - i.val
decreasing_by scalar_decr_tac

@[progress]
theorem simple.sponge_absorb_initial.spec
  (bs : Std.Slice Bool) (r : Std.Usize) (s : Aeneas.Std.Array Bool 1600#usize)
(r_pos: r.val > 0)
: r.val < 1600
→ s.val = List.replicate (Spec.b 6) false
→ ∃ output,
  sponge_absorb_initial bs r s = .ok output ∧
  output.val.toBitVec = ((absorb (s.val.toBitVec.cast (by simp; decide)) ((Array.mk bs.val).chunks_exact r)).cast (by simp; decide))
:= by
  intro r_lt s_zero
  rw [sponge_absorb_initial]
  let* ⟨ n, n_post ⟩ ← Std.Usize.div_spec
  let* ⟨ res, res_post ⟩ ← simple.sponge_absorb_initial_loop.spec
  simp [*, Array.extract_eq_self_of_le]

attribute [progress_pure_def] Aeneas.Std.core.num.Usize.saturating_sub

@[progress]
theorem Aeneas.Std.core.slice.index.Slice.index_range_from_usize_spec(T: Type)
(slice: Slice T)
(i: ops.range.RangeFrom Usize)
: i.start ≤ slice.length
→ ∃ output,
  Slice.index (Std.core.slice.index.SliceIndexRangeFromUsizeSlice T) slice i = .ok output ∧
  output.val = slice.val.extract (start := i.start.val)
:= by
  intro inbound
  simp only [index, SliceIndexRangeFromUsizeSlice.index]
  simp_ifs
  simp [Slice.drop]

@[simp]
def Aeneas.Std.UScalar.saturating_sub' {ty : UScalarTy} (x y : UScalar ty) : UScalar ty :=
  UScalar.mk <| BitVec.ofFin ⟨x.val - y.val, Nat.lt_of_le_of_lt (Nat.sub_le _ _) x.bv.toFin.isLt⟩

@[simp]
theorem Aeneas.Std.UScalar.saturating_sub_def(a b: Std.UScalar ty)
: a.saturating_sub b = a.saturating_sub' b
:= by
  simp only [saturating_sub, BitVec.ofNat, Fin.ofNat', saturating_sub']
  simp
  rw [Nat.mod_eq_of_lt]
  exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) a.bv.toFin.isLt

/- attribute [scalar_tac_simps] Std.Array.to_slice -/
-- TODO: Me da el límite de recursión, no se por qué.

theorem Aeneas.Std.core.num.Usize.saturating_sub.spec(a b: Std.Usize)
: ∃ c, Std.toResult (saturating_sub a b) = .ok c ∧ c.val = a.val - b.val
:= by
  simp [saturating_sub, UScalar.saturating_sub', Std.toResult]
  reduce
  rfl

@[simp] theorem BitVec.length_toList(bv: BitVec n)
: bv.toList.length = n
:= by simp [BitVec.toList]

theorem Aeneas.Std.Array.to_slice_mut.spec'.{u} {α : Type u} {n : Std.Usize} (a : Aeneas.Std.Array α n)
: ∃ old new, Std.toResult a.to_slice_mut = Std.Result.ok (old, new) ∧
  old.val = a.val ∧ ∀ s: Slice α, (new s).val = (a.from_slice s).val
:= by
  progress as ⟨old, new, old_post, new_post⟩
  simp [*, Std.Array.to_slice]


theorem BitVec.toBitVec_toList(bv: BitVec n)
: bv.toList.toBitVec = bv.cast (by simp)
:= by
  ext i i_idx
  simp [BitVec.toList]

theorem BitVec.cast_heq
  (bv: BitVec n)
  (bv2: BitVec m)
  (eq: m = n)
(heq: HEq bv bv2)
: bv = bv2.cast eq
:= by
  subst eq
  simp_all only [heq_eq_eq, cast_eq]

/- set_option pp.coercions false in -/
set_option maxHeartbeats 1000000 in
@[progress]
theorem simple.sponge_absorb_final.spec
  (rest suffix : Std.Slice Bool) (r : Std.Usize) (s : Aeneas.Std.Array Bool _)
(r_pos: r.val > 0)
: r.val ≥ 6 -- Since we need to ensure (rest ++ suffix ++ pad).drop r ≤ r
→ rest.length < r
→ suffix.length ≤ 4
→ rest.length + suffix.length < Std.Usize.max
→ ∃ output,
  sponge_absorb_final s rest suffix r = .ok output ∧
  output.val.toBitVec = (
    absorb (s.val.toBitVec.cast (by simp; decide)) (
      (rest.val.toArray ++ suffix.val.toArray ++ (Spec.«pad10*1» r (rest.val ++ suffix.val).length)).chunks_exact r
    )
  ).cast (by simp; decide)
:= by
  intro r_big_enough rest_lt suffix_le no_overflow
  rw [sponge_absorb_final]

  let* ⟨ nb_left, nb_left_post ⟩ ← Std.Usize.add_spec
  let* ⟨ orig_s, mk_s1, orig_s_post, mk_s1_post ⟩ ← Std.Array.to_slice_mut.spec'
  let* ⟨ s1, s1_len, s1_val ⟩ ← xor_long.spec
  simp [*] at s1_len
  let* ⟨ old_s1, mk_s2, old_s1_post, mk_s2_post ⟩ ← Std.Array.to_slice_mut.spec'
  let* ⟨ s2, s2_len, s2_val ⟩ ← xor_long_at.spec
  simp [*] at s2_len
  let* ⟨leftover, leftover_post⟩ ← Std.core.num.Usize.saturating_sub.spec
  split
  case isTrue leftover_pos =>
    /-
    We have that (rest ++ suffix) ≥ r, so (rest ++ suffix).drop r
    is left to be absorbed, plus then padding

    The idea then is that
    absorb S <| (rest ++ suffix ++ pad).chunks_exact r =
     = absorb S <| ((rest ++ suffix ++ pad).take r ++ (rest ++ suffix ++ pad).drop r).chunks_exact r
     ↓
     = absorb (S ^^ (rest ++ suffix ++ pad).take r) <| ((rest ++ suffix ++ pad).drop r).chunks_exact r
     ↓ List.take_append_of_le_length ∧ List.drop_append_of_le_length
     = absorb (S ^^ (rest ++ suffix).take r) <| ((rest ++ suffix).drop r ++ pad).chunks_exact r
     ↓ have: ((rest ++ suffix).drop r ++ pad).length = r since (rest ++ suffix).drop r ≤ 4
     = absorb (S ^^ (rest ++ suffix).take r)    [(rest ++ suffix).drop r ++ pad]
     ↓ reduce
     = absorb.upd (S ^^ (rest ++ suffix).take r) [(rest ++ suffix).drop r ++ pad]
     ↓ reduce
     = keccak_p (S ^^ (rest ++ suffix).take r) ^^ [(rest ++ suffix).drop r ++ pad]
    -/
    let* ⟨ s3, s3_len, s3_val ⟩ ← keccak_p.spec'
    simp [*] at s3_len
    let* ⟨ old_s3, mk_s4, old_s3_post, mk_s4_post ⟩ ← Std.Array.to_slice_mut.spec'
    /- rw [Std.Array.to_slice] at old_s3_post -/
    let* ⟨ left, left_post ⟩ ← Std.core.slice.index.Slice.index_range_from_usize_spec
    let* ⟨ s4, s4_len, s4_val ⟩ ← xor_long.spec'
    simp at s4_len
    simp only [old_s3_post, s3_len] at s4_len
    let* ⟨ old_s4, mk_s5, old_s4_post, mk_s5_post ⟩ ← Std.Array.to_slice_mut.spec'
    let* ⟨ a_one, a_one_post ⟩ ← Std.Array.to_slice.progress_spec
    simp [Std.Array.to_slice] at a_one_post
    /- subst -/
    /- a_one_post -/
    let* ⟨ pos1, pos1_post ⟩ ← Std.Usize.sub_spec
    /- set_option trace.Meta.Tactic.simp true in -/
    let* ⟨ s5, s5_len, s5_val ⟩ ← xor_long_at.spec
    · subst a_one_post
      simp [*]; scalar_tac
    simp at s5_len
    simp only [*] at s5_len
    simp only [Std.Array.from_slice, BitVec.length_toList] at s5_len
    simp [a_one_post, s4_len, Std.Array.to_slice] at s5_len s5_val
    let* ⟨ old_s5, new_s6, old_s5_post, new_s6_post ⟩ ← Std.Array.to_slice_mut.spec'
    let* ⟨ pos2, pos2_post ⟩ ← Std.Usize.sub_spec
    let* ⟨ s6, s6_len, s6_val⟩ ← xor_long_at.spec
    · simp [*]; scalar_tac
    simp [*] at s6_len
    simp only [Std.Array.from_slice] at new_s6_post
    let* ⟨ res, res_len, res_val ⟩ ← keccak_p.spec'

    ext i i_idx
    simp [BitVec.getElem_cast]
    simp only [getElem_eq_getElem!]
    /- rw [BitVec.toNat_eq] -/
    /- simp -/
    rw [res_val]
    generalize_proofs pf1 pf2 pf3 pf4
    have := new_s6_post s6
    have := aux3 _ _ this
    have := congrArg (f := BitVec.cast pf3) this
    rw [this]

    rw [(by rfl: pf5 = pf3)]
    change BitVec.cast pf3 (new_s6 s6).val.toBitVec at this

    #check (new_s6 s6).val.toBitVec = ((if h2 : s6.length = (1600#usize).val then ⟨s.val, h2⟩ else mk_s5 s5).val).toBitVec
    have: (new_s6 s6).val = ↑(if h : (s6).length = ↑1600#usize then ⟨s.val, h⟩ else mk_s5 s5) := congrArg (f := BitVec.ofBoolListLE) this
    /- have : ∀ (s : Std.Slice Bool), ↑(new_s6 s) = ↑(if h : (↑s).length = ↑1600#usize then ⟨↑s, h⟩ else mk_s5 s5) -/

    have := congrArg (f := BitVec.cast pf3 (List.toBitVec ·)) (new_s6_post s6)
    conv => enter [1, 1]; rw [new_s6_post s6]
    let motive := fun _a => (Spec.Keccak.P 6 24 (BitVec.cast ⋯ _a.toBitVec)).toList.toBitVec


    -- refine Eq.rec (motive := fun a h => explicit_motive) ?_ ?_2

    /- generalize_proofs _ _ h _ -/
    -- f res = bar.cast h with (f res : T res), (bar : T foo) (h: res = foo)
    /- ext idx idx_lt_res -/
    /- simp only [BitVec.getElem_cast] -/

    /- simp [*, Spec.b, Spec.w] -/
    /- simp only [Std.Array.from_slice, s5_len, s6_len, s4_len] -/
    /- simp -/

    sorry
  case isFalse leftover_zero =>
    sorry
    simp at leftover_zero
    let* ⟨ x_1, x_2, x_post_1, x_post_2 ⟩ ← Std.Array.to_slice_mut.spec
    let* ⟨ s8, s8_post ⟩ ← Std.Array.to_slice.progress_spec
    let* ⟨ s9, s9_post_1, s9_post_2 ⟩ ← xor_long_at.spec
    · simp [*, Std.Array.to_slice]
      scalar_tac
    let* ⟨ i3, i3_post ⟩ ← Std.Usize.add_spec
    split
    case isTrue has_space =>
      let* ⟨ x_1, x_2, x_post_1, x_post_2 ⟩ ← Std.Array.to_slice_mut.spec
      let* ⟨ i5, i5_post ⟩ ← Std.Usize.sub_spec
      let* ⟨ s18, s18_post_1, s18_post_2 ⟩ ← xor_long_at.spec
      · simp [*, Std.Array.to_slice]; scalar_tac
      let* ⟨ res, res_post ⟩ ← keccak_p.spec'
      sorry
    case isFalse no_space =>
      let* ⟨ s11, s11_post ⟩ ← keccak_p.spec'
      let* ⟨ x_1, x_2, x_post_1, x_post_2 ⟩ ← Std.Array.to_slice_mut.spec
      let* ⟨ i5, i5_post ⟩ ← Std.Usize.sub_spec
      let* ⟨ s18, s18_post_1, s18_post_2 ⟩ ← xor_long_at.spec
      · simp [*, Std.Array.to_slice]; scalar_tac
      let* ⟨ res, res_post ⟩ ← keccak_p.spec'

      simp [*, Std.Array.from_slice, Std.Array.to_slice, Spec.b, Spec.w]
      apply List.ext_getElem! (by simp); intro i
      simp [*]
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
  /- progress*? -/

  sorry

-- @[progress]
theorem simple.sponge.spec (r : Std.Usize) (bs output suffix: Std.Slice Bool)
[NeZero r.val]
/- (r_ne_zero: r.val ≠ 0) -/
: ∃ output,
  simple.sponge r bs output suffix = .ok output ∧
  output.val = (Spec.sponge (f := Spec.Keccak.P 6 (nᵣ := 24)) (pad := Spec.«pad10*1») r.val (Array.mk <| bs.val ++ suffix.val ) output.length).toArray.toList
:= by sorry
