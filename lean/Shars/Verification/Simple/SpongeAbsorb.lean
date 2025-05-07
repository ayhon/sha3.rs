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
attribute [ext (iff := false)] List.ext_getElem!
/- attribute [simp] Aeneas.Std.Slice.set -/

example(a b c: Nat): 0 < b → a * b < c → a ≤ c / b := by
  intros b_pos a_b_lt_c
  calc a
    _ = (a * b) / b := by
      rw [Nat.mul_div_cancel (H:=b_pos)]
    _ ≤ c / b := by
      apply Nat.div_le_div_right
      simp [*, le_of_lt]

-- attribute [simp_lists_simps] List.length_append List.take_append_eq_append_take List.take_zipWith List.length_zipWith List.length_take List.take_all_of_le List.length_drop List.drop_eq_nil_of_le List.drop_append_eq_append_drop List.nil_append List.zipWith_nil_left List.append_nil List.drop_drop List.take_take

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
    case neg => simp [getElem!_neg, i_idx]
    simp [Spec.«pad10*1»] at h i_idx ⊢
    simp_ifs
    rw [getElem!_pos]
    case h => scalar_tac
    simp

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

theorem Spec.«pad10*1_length» (x m : Nat)
: (Spec.«pad10*1» x m).size = (2 + (-(m + 2: Int) % x).toNat)
:= by simp +arith [«pad10*1», neg_add, -neg_add_rev, -Int.reduceNeg]

def spec_sponge (r: Nat)(r_pos: r > 0):=
  have: NeZero r := ⟨Nat.ne_zero_of_lt r_pos⟩
  Spec.sponge (f := Spec.Keccak.P 6 24) (pad := Spec.«pad10*1»)
def spec_sponge_absorb (r: Nat)(r_pos: r > 0) :=
  have: NeZero r := ⟨Nat.ne_zero_of_lt r_pos⟩
  Spec.sponge.absorb (f := Spec.Keccak.P 6 24) (pad := Spec.«pad10*1») (r := r)
def spec_sponge_squeze{m d}(r: Nat)(r_pos: r > 0) :=
  have: NeZero r := ⟨Nat.ne_zero_of_lt r_pos⟩
  Spec.sponge.squeeze (m := m) (d := d) (f := Spec.Keccak.P 6 24) (r := r)

/- #check BitVec.setWidth_cast -/

def absorb.upd(S: BitVec (Spec.b 6))(P: Vector Bool r): BitVec (Spec.b 6) :=
  Spec.Keccak.P 6 24 (S ^^^ (BitVec.ofBoolListLE <| P.toList).setWidth (Spec.b 6))

def absorb{r: Nat}(S: BitVec (Spec.b 6))(Ps: Array (Vector Bool r)) := Id.run do
  let mut S := S
  for P in Ps do
    S := absorb.upd S P
  return S

def simple.sponge_absorb_final.panic_free
  (keccak_p: List Bool → List Bool)
  (r: Nat)
  (s rest suffix: List Bool)
: List Bool
:= Id.run do
  let mut s := s
  s := ListIR.xor_long s rest
  let nb_left := rest.length + suffix.length
  if nb_left >= r then
    s := ListIR.xor_long_at s (suffix.take (r - rest.length)) rest.length
  -- if nb_left >= r then
    s := keccak_p s
    s := ListIR.xor_long s (suffix.drop (r - rest.length))
    s := ListIR.xor_long_at s [true] (rest.length + suffix.length - r)
    s := ListIR.xor_long_at s [true] (r-1)
  else
    s := ListIR.xor_long_at s suffix rest.length
    s := ListIR.xor_long_at s [true] nb_left
    if nb_left + 1 < r then
      s := ListIR.xor_long_at s [true] (r-1)
    else
      s := keccak_p s
      s := ListIR.xor_long_at s [true] (r-1)
  keccak_p s


@[scalar_tac_simps]
theorem Nat.sub_div_self(a b: Nat)
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
theorem Nat.sub_div_mult_left(a b: Nat)
:(a - b*i) / b = a / b - i := by
  by_cases b > 0
  case neg h => simp at h; subst h; simp
  case pos =>
    cases i
    case zero => simp
    case succ i' =>
      simp [Nat.mul_add, Nat.sub_add_eq, Nat.sub_div_self]
      rw [Nat.sub_div_mult_left]

theorem BitVec.cast_xor(bv bv2: BitVec n)(eq: n = m)
: (bv ^^^ bv2).cast eq = bv.cast eq ^^^ bv2.cast eq
:= by ext i i_lt; simp

attribute [simp] Aeneas.Std.core.slice.index.Slice.index


private theorem List.foldl_congr{ls ls': List α}
: ls = ls'
→ upd = upd'
→ init = init'
→ ls.foldl upd init = ls'.foldl upd' init'
:= by rintro rfl rfl rfl; rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000 in
theorem absorb.refinement(r: Nat)(S: BitVec (Spec.b 6))(bs: Array Bool)
: (absorb S (bs.chunks_exact r)).toList = ListIR.absorb' ListIR.list_keccak_p S.toList (bs.toList.chunks_exact r)
:= by
  unfold absorb ListIR.absorb'
  simp [ListIR.list_keccak_p, ListIR.xor_long.def, -Array.size_chunks_exact]
  rw [←Array.foldl_toList]
  rw [Array.chunks_exact, List.chunks_exact]
  split <;> simp_ifs
  case isTrue h =>
    simp
    ext i
    · simp [Spec.b, Spec.w]
    by_cases i < 1600 <;> simp
    case pos h => intros; assumption
    case neg h =>
      rw [getElem!_neg]
      case h => simpa using h
      simp
  case isFalse h =>
    simp
    generalize_proofs _ len_extract
    have ih := absorb.refinement r (@upd r S ⟨bs.extract 0 r, len_extract⟩) (bs.extract r)
    simp [absorb,ListIR.absorb', ListIR.list_keccak_p, ListIR.xor_long.def] at ih
    rw [ih]
    rw [List.foldl_congr]
    · simp_lists
    · ext s chunk
      · simp
      simp
    · rw [upd]
      simp [List.setWidth, Spec.b, Spec.w]
      rw [List.take_of_length_le (by simp)]
      apply congrArg
      apply congrArg
      ext i i_idx
      rw [ListIR.xor_long, ListIR.xor_long_at]
      simp at i_idx
      simp [←Bool.default_bool,←List.getElem!_eq_getElem?_getD, i_idx]
      have: S.toList.length = 1600 := by simp [Spec.b, Spec.w]
      if h: i < r then
        simp_lists
        simp [getElem_eq_getElem!]
      else
        simp_lists
        simp at h
        simp +arith [getElem_eq_getElem!, ←Nat.add_sub_assoc, h]
termination_by bs.size

abbrev ref.interesting_part_of_the_proof.preconditions(r: Nat)(s rest suffix: List Bool) :=
  r ≥ 6 -- Otherwise, we don't have suffix + 2 ≤ r
∧ suffix.length ≤ 4 -- Taken from the actual uses of `suffix` in SHA3
∧   rest.length < r -- Since rest is what's left after absorb_initial
∧ s.length = 1600 -- The state has length Spec.b 6

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 1000000 in
theorem ref.interesting_part_of_the_proof.case1{r: Nat}{s rest suffix: List Bool}
  (hyp: (rest ++ suffix).length ≥ r)
: preconditions r s rest suffix
→ let padding := (Spec.«pad10*1» r (rest.length + suffix.length)).toList
  (rest ++ suffix ++ padding).chunks_exact r = [(rest ++ suffix).take r, (suffix.drop (r - rest.length) ++ padding)]
:= by
  /-
  · (rest ++ suffix) >= r
    Then we have
     (rest ++ suffix ++ padding).chunks_exact k =
     = [(rest ++ suffix).take r, (suffix.drop (r - rest.length) ++ padding)]
  -/
  rintro ⟨r_big_enough,suffix_len_le,rest_len_lt,len_s⟩ padding
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
theorem ref.interesting_part_of_the_proof.case2{r: Nat}{s rest suffix: List Bool}
  (hyp: (rest ++ suffix).length = r-1)
: preconditions r s rest suffix
→ let padding := (Spec.«pad10*1» r (rest.length + suffix.length)).toList
  (rest ++ suffix ++ padding).chunks_exact r = [rest ++ suffix ++ [true], List.replicate (r-1) false ++ [true]]
:= by
  /-
  · (rest ++ suffix) = r - 1
    Then we have
     (rest ++ suffix ++ padding).chunks_exact k =
     = [rest ++ suffix ++ [true], List.replicate false (r-1) ++ [true]]
  -/
  rintro ⟨r_big_enough,suffix_len_le,rest_len_lt,len_s⟩ padding
  have len_padding: (Spec.«pad10*1» r (rest.length + suffix.length)).size = 2*r - (rest.length + suffix.length) := by
    simp at hyp
    simp [Spec.«pad10*1_length», -neg_add_rev, hyp, r_big_enough]
    zify
    rw [Nat.cast_sub (by omega)]
    rw [Nat.cast_sub (by omega)]
    rw [Nat.cast_sub (by omega)]
    rw [Nat.cast_mul]
    ring_nf
    simp [Int.neg_emod_eq_sub_emod]
    rw [
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
        rw [getElem!_neg]
        simp
        scalar_tac

set_option maxRecDepth 100000000 in
set_option maxHeartbeats 1000000 in
theorem ref.interesting_part_of_the_proof.case3{r: Nat}{s rest suffix: List Bool}
  (hyp: (rest ++ suffix).length <= r-2)
: preconditions r s rest suffix
→ let padding := (Spec.«pad10*1» r (rest.length + suffix.length)).toList
  (rest ++ suffix ++ padding).chunks_exact r = [rest ++ suffix ++ [true] ++ List.replicate (r -2 - rest.length - suffix.length) false ++ [true]]
:= by
  /-
  · (rest ++ suffix) <= r - 2
    Then we have
     (rest ++ suffix ++ padding).chunks_exact k =
     = [rest ++ suffix ++ [true, true]]
  -/
  rintro ⟨r_big_enough,suffix_len_le,rest_len_lt,len_s⟩ padding
  have len_padding: (Spec.«pad10*1» r (rest.length + suffix.length)).size = r - (rest.length + suffix.length) := by
    simp at hyp
    simp [Spec.«pad10*1_length», -neg_add_rev]
    zify
    rw [Nat.cast_sub (by omega),
        Int.neg_emod_eq_sub_emod,
        Int.emod_eq_of_lt (H1:=by omega) (H2:=by omega)]
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

set_option maxHeartbeats 1000000 in
theorem ref.interesting_part_of_the_proof.proof(r: Nat)(s rest suffix: List Bool)
: preconditions r s rest suffix
→ let f := ListIR.list_keccak_p
  let padding := (Spec.«pad10*1» r (rest.length + suffix.length)).toList
  simple.sponge_absorb_final.panic_free f r s rest suffix =
    ListIR.absorb' f s (
      (rest ++ suffix ++ padding).chunks_exact r
    )
:= by
  rintro precond f padding
  have ⟨r_big_enough,suffix_len_le,rest_len_lt,len_s⟩ := precond
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
    simp [ListIR.absorb', simple.sponge_absorb_final.panic_free, *, ListIR.xor_long]

    generalize leftover_val: (rest.length + suffix.length - r) = leftover
    rw [ListIR.xor_long_at_twice_separate]
    case compatible_offset => scalar_tac

    rw [ListIR.xor_long_at_twice_separate]
    case compatible_offset => scalar_tac

    rw [ListIR.xor_long_at_twice_separate]
    case compatible_offset => scalar_tac

    congr
    · simp +arith [List.take_append_of_ge_length, le_of_lt rest_len_lt]
    · simp +arith; scalar_tac
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
        rw [getElem!_neg]
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
    simp [ListIR.absorb', simple.sponge_absorb_final.panic_free, *, ListIR.xor_long]

    rw [ListIR.xor_long_at_twice_separate]
    case compatible_offset => scalar_tac

    rw [ListIR.xor_long_at_twice_separate]
    case compatible_offset => scalar_tac

    simp [ListIR.xor_long_of_xor_long_at]
    congr
    -- have{α: Type}(x ls: List α): (x ++ ls) = ls ↔ x = [] := by exact?
    simp_lists
    scalar_tac

  else if cond3: (rest ++ suffix).length ≤ r - 2 then
    rw [case3 cond3 precond]
    simp at cond3
    simp [ListIR.absorb', simple.sponge_absorb_final.panic_free, *, ListIR.xor_long]
    simp_ifs

    rw [ListIR.xor_long_at_twice_separate]
    case compatible_offset => scalar_tac

    rw [ListIR.xor_long_at_twice_separate]
    case compatible_offset => scalar_tac

    rw [ListIR.xor_long_at_twice_separate]
    case compatible_offset => scalar_tac

    simp only [ListIR.xor_long_of_xor_long_at]
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
:= by simp [absorb]

theorem absorb.spec (N : Array Spec.Bit) (r: Nat)(r_pos: r > 0)
: spec_sponge_absorb r r_pos N = absorb (0#(Spec.b 6)) ((N ++ Spec.«pad10*1» r N.size).chunks_exact r)
:= by
  rw [spec_sponge_absorb, Spec.sponge.absorb, absorb]
  -- NOTE: I needed to exercise a bit too much control here.
  simp [←Array.foldl_toList,-Array.size_chunks_exact, -Array.size_map, upd]

@[progress]
theorem Aeneas.Std.Array.to_slice_mut.spec{α : Type u} {n : Usize} (a : Array α n)
: ∃ old new,
  Std.toResult (a.to_slice_mut) = .ok (old, new) ∧
  old = a.to_slice ∧
  new = a.from_slice
:= by simp [to_slice_mut, Std.toResult]

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
     -- r * i < r * n = r * (bs.length / r) ≤ bs.length ≤ Usize.max
    have _: r.val*i.val ≤ bs.length := le_of_lt $ calc r.val * i.val
        _ < r.val * n := Nat.mul_lt_mul_of_pos_left i_idx r_pos
        _ = r.val * (bs.length / r) := by simp [n_val]
        _ ≤ bs.length := Nat.mul_div_le bs.length ↑r

     -- r * (i + 1) ≤ r * n = r * (bs.length / r) ≤ bs.length ≤ Usize.max
    have _: r.val*(i.val + 1) ≤ bs.length := calc r.val * (i.val + 1)
        _ ≤ r.val * n := Nat.mul_le_mul_left r.val i_idx
        _ = r.val * (bs.length / r) := by simp [n_val]
        _ ≤ bs.length := Nat.mul_div_le bs.length ↑r

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

theorem Array.extract_start_stop(arr: Array α)
(start_default : start = 0        := by omega)
(stop_default :  stop  = arr.size := by omega)
: arr.extract start stop = arr
:= by subst start_default; subst stop_default; simp only [extract_size]

@[progress]
theorem simple.sponge_absorb_initial.spec
  (bs : Std.Slice Bool) (r : Std.Usize) (s : Aeneas.Std.Array Bool 1600#usize)
(r_pos: r.val > 0)
: r.val < 1600
→ s.val = List.replicate (Spec.b 6) false
→ ∃ output,
  sponge_absorb_initial bs r s = .ok output ∧
  output.val = ListIR.absorb' ListIR.list_keccak_p s.val (bs.val.chunks_exact r)
  -- ∧ output.val.toBitVec = ((absorb (s.val.toBitVec.cast (by simp; decide)) ((Array.mk bs.val).chunks_exact r)).cast (by simp; decide))
:= by
  intro r_lt s_zero
  rw [sponge_absorb_initial]
  let* ⟨ n, n_post ⟩ ← Std.Usize.div_spec
  let* ⟨ res, res_post ⟩ ← simple.sponge_absorb_initial_loop.spec
  simp [*, Array.extract_eq_self_of_le]

  replace res_post := congrArg (f := BitVec.toList) res_post
  simp at res_post
  rw [res_post]

  rw [Array.extract_start_stop (stop_default := by simp [*])]
  rw [absorb.refinement]
  simp [ListIR.absorb', s_zero]

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

-- @[simp]
-- def Aeneas.Std.UScalar.saturating_sub' {ty : UScalarTy} (x y : UScalar ty) : UScalar ty :=
--   UScalar.mk <| BitVec.ofFin ⟨x.val - y.val, Nat.lt_of_le_of_lt (Nat.sub_le _ _) x.bv.toFin.isLt⟩

-- @[simp]
-- theorem Aeneas.Std.UScalar.saturating_sub_def(a b: Std.UScalar ty)
-- : a.saturating_sub b = a.saturating_sub' b
-- := by
--   simp only [saturating_sub, BitVec.ofNat, Fin.ofNat', saturating_sub']
--   simp
--   rw [Nat.mod_eq_of_lt]
--   exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) a.bv.toFin.isLt

-- /- attribute [scalar_tac_simps] Std.Array.to_slice -/
-- -- TODO: Me da el límite de recursión, no se por qué.

-- theorem Aeneas.Std.core.num.Usize.saturating_sub.spec(a b: Std.Usize)
-- : ∃ c, Std.toResult (saturating_sub a b) = .ok c ∧ c.val = a.val - b.val
-- := by
--   simp [saturating_sub, UScalar.saturating_sub', Std.toResult]
--   reduce
--   rfl


@[progress]
theorem simple.xor_long_at.spec'(a b: Std.Slice Bool)(offset: Std.Usize)
: b.length + offset.val ≤ Std.Usize.max
→ ∃ c,
  xor_long_at a b offset = .ok c ∧
  c.val = ListIR.xor_long_at a.val b.val offset.val
:= by
  intro nooverflow
  let* ⟨ res, res_len, res_post ⟩ ← spec
  ext i
  · simp [res_len]
  assume i_idx: i < res.length
  case otherwise => simp_lists
  rw [res_post, ListIR.getElem!_xor_long_at]
  case a => assumption
  simp [res_len] at i_idx
  simp [i_idx]

@[progress]
theorem simple.xor_long.spec'(a b: Std.Slice Bool)
: ∃ c,
  xor_long a b = .ok c ∧
  c.val = ListIR.xor_long a.val b.val
:= by
  rw [xor_long]
  let* ⟨ res, post ⟩ ← xor_long_at.spec'
  rw [post, ListIR.xor_long]


/- set_option pp.coercions false in -/
set_option maxHeartbeats 1000000 in
@[progress]
theorem simple.sponge_absorb_final.spec
  (rest suffix : Std.Slice Bool) (r : Std.Usize) (s : Aeneas.Std.Array Bool _)
: r.val ≥ 6
→ rest.length < r
→ suffix.length ≤ 4
→ rest.length + suffix.length < Std.Usize.max
→ ∃ output,
  sponge_absorb_final s rest suffix r = .ok output ∧
  output.val = sponge_absorb_final.panic_free ListIR.list_keccak_p r.val s.val rest.val suffix.val
:= by
  intro r_big_enough rest_lt suffix_le no_overflow
  rw [sponge_absorb_final]

  let* ⟨ old_s, mk_s1, old_s_post, new_s_post ⟩ ← Std.Array.to_slice_mut.spec'
  let* ⟨ x1, x1_val ⟩ ← xor_long.spec'
  -- ←Nat.sub_sub_eq_min
  let* ⟨ nb_left, nb_left_post ⟩ ← Std.Usize.add_spec
  simp at nb_left_post
  split
  case isTrue nb_left_ge_r =>
    simp [nb_left_post] at nb_left_ge_r
    let* ⟨ old_s1, mk_s2, old_s1_post, mk_s2_post ⟩ ← Std.Array.to_slice_mut.spec'
    let* ⟨ i3, i3_post ⟩ ← Std.Usize.sub_spec'
    simp at i3_post
    let* ⟨ suffix_low, suffix_low_post ⟩ ← Std.core.slice.index.Slice.index.slice_index_range_usize_slice_spec
    let* ⟨ x2, x2_val ⟩ ← xor_long_at.spec'
    · simp [*]; scalar_tac
    let* ⟨ x3, x3_val ⟩ ← keccak_p.spec'
    let* ⟨ old_s2, mk_s3, old_s2_post, mk_s3_post ⟩ ← Std.Array.to_slice_mut.spec'
    let* ⟨ suffix_high, suffix_high_post ⟩ ← Std.core.slice.index.Slice.index_range_from_usize_spec
    let* ⟨ x4, x4_val ⟩ ← xor_long.spec'
    let* ⟨ old_s3, mk_s4, old_s3_post, mk_s4_post ⟩ ← Std.Array.to_slice_mut.spec'
    let* ⟨ single_one, single_one_post ⟩ ← Std.Array.to_slice.progress_spec
    simp only [Std.toResult, Std.Array.make, Std.Array.to_slice] at single_one_post
    let* ⟨ i7, i7_post ⟩ ← Std.Usize.sub_spec'
    let* ⟨ x5, x5_val ⟩ ← xor_long_at.spec'
    let* ⟨ old_s4, mk_s5,  old_s4_post, mk_s5_post ⟩ ← Std.Array.to_slice_mut.spec'
    let* ⟨ i8, i8_post ⟩ ← Std.Usize.sub_spec'
    let* ⟨ x6, x6_val ⟩ ← xor_long_at.spec'
    let* ⟨ res, res_post_2 ⟩ ← keccak_p.spec'

    simp [*, panic_free, Std.Array.from_slice, ListIR.xor_long]
    simp_ifs
    congr
    simp_lists
  case isFalse nb_left_idx =>
    simp [nb_left_post] at nb_left_idx
    let* ⟨ old_s1, mk_s2, old_s1_post, mk_s2_post ⟩ ← Std.Array.to_slice_mut.spec'
    let* ⟨ s5, s5_val ⟩ ← xor_long_at.spec'
    let* ⟨ _x_1, _x_2, _x_post_1, _x_post_2 ⟩ ← Std.Array.to_slice_mut.spec'
    let* ⟨ single_one, single_one_post ⟩ ← Std.Array.to_slice.progress_spec
    simp only [Std.toResult, Std.Array.make, Std.Array.to_slice] at single_one_post
    let* ⟨ s9, s9_val ⟩ ← xor_long_at.spec'
    let* ⟨ i3, i3_post ⟩ ← Std.Usize.add_spec
    split
    case isTrue nb_left_has_space =>
      let* ⟨ _x_1, _x_2, _x_post_1, _x_post_2 ⟩ ← Std.Array.to_slice_mut.spec'
      let* ⟨ i8, i8_post ⟩ ← Std.Usize.sub_spec'
      let* ⟨ s19, s19_val ⟩ ← xor_long_at.spec'
      let* ⟨ res, res_val ⟩ ← keccak_p.spec'

      simp [*, panic_free, Std.Array.from_slice, ListIR.xor_long]
      simp_ifs
    case isFalse nb_left_has_space =>
      let* ⟨ s11, s11_val ⟩ ← keccak_p.spec'
      let* ⟨ _x_1, _x_2, _x_post_1, _x_post_2 ⟩ ← Std.Array.to_slice_mut.spec'
      let* ⟨ i8, i8_post ⟩ ← Std.Usize.sub_spec'
      let* ⟨ s19, s19_val ⟩ ← xor_long_at.spec'
      let* ⟨ res, res_val ⟩ ← keccak_p.spec'

      simp [*, panic_free, Std.Array.from_slice, ListIR.xor_long]
      simp_ifs

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

@[simp]
theorem List.chunks_exact_nil(r: Nat): ([]: List α).chunks_exact r = [] := by unfold List.chunks_exact; simp

theorem List.chunks_exact_split{α: Type}(bs: List α)(r: Nat)(i: Nat)
: (bs.take (r*i)).chunks_exact r ++ (bs.drop (r*i)).chunks_exact r = bs.chunks_exact r
:= by
  assume r_pos: r > 0
  case otherwise => simp at r_pos; simp [r_pos]

  ext j : 1
  · simp
    by_cases r*i ≥ bs.length
    case pos h => simp [h]
    case neg h =>
      simp at h
      have : i ≤ bs.length / r := by
        simp only [Nat.le_div_iff_mul_le r_pos, h, le_of_lt, Nat.mul_comm i]
      simp [h, le_of_lt, Nat.sub_div_mult_left, Nat.mul_div_cancel_left, r_pos, this]
  assume h: r*i < bs.length
  case otherwise =>
    simp at h
    rw [List.take_of_length_le h]
    rw [List.drop_of_length_le h]
    simp
  have: i ≤ bs.length / r := by
    simp only [Nat.le_div_iff_mul_le r_pos, h, le_of_lt, Nat.mul_comm i]
  assume j < bs.length / r
  case otherwise h =>
    simp at h
    rw [getElem!_neg]
    rw [getElem!_neg]
    · simp; omega
    · simp [*, le_of_lt, Nat.sub_div_mult_left]

  by_cases j < i
  case pos j_lhs =>
    rw [List.getElem!_append_left]
    case h => simp [*, le_of_lt, Nat.mul_div_cancel, r_pos]
    rw [List.getElem!_chunks_exact]
    case a => simp [*, le_of_lt, Nat.mul_div_cancel, r_pos]
    rw [List.getElem!_chunks_exact]
    case a => simp; omega
    simp
    rw [List.take_drop]
    rw [List.take_drop]
    rw [List.take_take]
    congr
    ring_nf
    simp
    have : r*(j + 1) ≤ r*i := by
      apply Nat.mul_le_mul_left
      assumption
    simpa [Nat.mul_add] using this
  case neg j_rhs =>
    simp at j_rhs
    rw [List.getElem!_append_right]
    case h => simp [*, le_of_lt]
    rw [List.getElem!_chunks_exact]
    case a => simp [*, le_of_lt, Nat.sub_div_mult_left]; omega
    rw [List.getElem!_chunks_exact]
    case a => simp [*]
    simp [*, le_of_lt]
    congr 1
    · ring_nf; simp [Nat.mul_sub]
    · congr
      simp [Nat.mul_sub, *]


/- @[progress] -/
set_option maxRecDepth 1000000 in
theorem simple.sponge_absorb.spec_list
  (bs : Std.Slice Bool) (r : Std.Usize) [NeZero r.val](input : Aeneas.Std.Array Bool 1600#usize)
  (suffix : Std.Slice Bool)
: r.val ≥ 6
→ r.val < 1600
→ suffix.length ≤ 4
→ input.val = List.replicate 1600 false
→ let padding := (Spec.«pad10*1» r.val (bs.length % r.val + suffix.length)).toList
∃ output,
  sponge_absorb bs r input suffix = .ok output ∧
  -- output.
  -- output.val.toBitVec = (spec_sponge_absorb r.val (Nat.pos_of_neZero r.val) (bs.val.toArray ++ suffix.val.toArray)).cast (by simp [Spec.b, Spec.w])
  -- absorb → absorb'
  output.val =
    ListIR.absorb' ListIR.list_keccak_p input.val (
      (bs.val ++ suffix.val ++ padding).chunks_exact r
    )
:= by
  intro r_big_enough r_bounded suffix_small input_zero
  unfold sponge_absorb
  have r_pos: r.val > 0 := by omega

  let* ⟨ s1, s1_post ⟩ ← sponge_absorb_initial.spec
  let* ⟨ n, n_post ⟩ ← Std.Usize.div_spec
  have := Nat.mul_div_le bs.length r
  let* ⟨ i1, i1_post ⟩ ← Std.Usize.mul_spec
  let* ⟨ rest, rest_post ⟩ ← Std.core.slice.index.Slice.index_range_from_usize_spec
  have rest_len: rest.length < r := by simp [*, ←Nat.mod_eq_sub, Nat.mod_lt]
  let* ⟨ res, res_post ⟩ ← sponge_absorb_final.spec

  simp only [*]
  rw [ref.interesting_part_of_the_proof.proof]
  case a =>
    simp [ref.interesting_part_of_the_proof.preconditions, *, ←Nat.mod_eq_sub, Nat.mod_lt]
  simp [-List.reduceReplicate, ←Nat.mod_eq_sub, Nat.mod_lt]
  generalize (Spec.«pad10*1» r.val (bs.length % r.val + suffix.length)).toList = padding
  rw [ListIR.absorb'_absorb']
  congr
  rw [List.take_of_length_le (h := by simp [Nat.add_comm (bs.length % r), Nat.div_add_mod])]

  rw [←List.chunks_exact_truncate]

  rw [←List.append_assoc]
  rw [←List.drop_append_of_le_length (by scalar_tac)]
  rw [←List.drop_append_of_le_length (by trans bs.length <;> (first | assumption | simp))]
  rw [←List.take_append_of_le_length (l₂ := suffix.val) (by assumption)]
  rw [←List.take_append_of_le_length (l₂ := padding) (by trans bs.length <;> (first | assumption | simp))]
  rw [List.chunks_exact_split, List.append_assoc]
