import Aeneas
import Shars.Definitions.Simple
import Sha3.Spec
/- import Sha3.Utils -/
import Sha3.Facts
import Init.Data.Vector.Lemmas

set_option maxHeartbeats 1000000

open Aeneas hiding Std.Array
open Std.alloc.vec 
section Auxiliary/- {{{ -/

theorem getElem_of_getElem?_in_bounds{xs: List α}{i: Nat}
(i_idx: i < xs.length)
: xs[i]? = some (xs[i])
:= by simp only [List.getElem?_eq_some_getElem_iff]

@[progress]
theorem simple.add_to_vec_loop.spec(dst: Vec Bool)(other: Vec Bool)(o n i: Std.Usize)
: o.val + n.val < Std.Usize.max
→ n.val < other.length
→ ∃ nb_added output,
  add_to_vec_loop core.marker.CopyBool dst o other n i = .ok (nb_added, output) ∧
  nb_added = Nat.min (n.val) (dst.length - o.val) - i.val + i.val ∧
  ∀ (j: Fin dst.length), 
    if o.val + i.val ≤ j ∧ j < o.val + n.val then output.val[j]! = other.val[j-o.val]!
    else  output.val[j]! = dst.val[j]!
:= by/- {{{ -/
  intro no_overflow o_other_idx
  rw [add_to_vec_loop]
  split
  case isTrue i_bnd =>
    let* ⟨ oi, oi_post ⟩ ← Aeneas.Std.Usize.add_spec
    split
    case isTrue oi_idx => 
      let* ⟨ t, t_post ⟩ ← Aeneas.Std.Slice.index_usize_spec
      simp [*] at t_post
      let* ⟨ dst', dst'_post ⟩ ← Aeneas.Std.Slice.update_spec
      simp [*] at dst'_post
      let* ⟨ i3, i3_post ⟩ ← Aeneas.Std.Usize.add_spec
      let* ⟨ nb_added, output, nb_added_post, output_post ⟩ ← spec
      simp [*] at nb_added_post output_post
      simp [nb_added_post]
      apply And.intro
      · have: n.val.min (dst.length - o) >= (i.val + 1) := by scalar_tac
        rw [Nat.add_comm, ←Nat.add_sub_assoc this]
        conv => arg 2; rw [Nat.add_comm, ←Nat.add_sub_assoc (Nat.le_of_lt this)]
        simp
      intro j
      have dst'_length: dst'.length = dst.length := by simp [dst'_post]
      let j': Fin (dst').length := ⟨j.val, by simp [dst'_length] ⟩
      replace output_post := output_post j'
      split
      case isTrue j_in_range =>
        -- If j ≥ o + (i + 1) then by induction hypothesis we conclude
        -- Otherwise, we have j = o + i and by dst'_post we have
        --   output[o+i]! = (dst.set (o + i) (other[i]))[o+1]!
        --   and by List.getElem_set we have output[o+1] = other[i]
        if ih: o.val + (i.val + 1) ≤ j then
          simp [ih, j', j_in_range] at output_post
          exact output_post
        else
          have j_val: j = o.val + i := by scalar_tac
          have: ↑o + ↑i < (dst).length := by scalar_tac
          simp [ih, j', j_val, j_in_range, List.getElem?_set, this] at output_post
          simpa [j_val] using output_post
      case isFalse =>
        have j_not_range: ¬ (↑o + (i.val + 1) ≤ ↑j ∧ ↑j < o.val + ↑n) := by scalar_tac
        have j_not_updated: ¬ o.val + i.val = j.val := by scalar_tac
        rw [if_neg j_not_range] at output_post
        simp [List.getElem?_set, j_not_updated] at output_post
        rw [if_neg j_not_updated] at output_post
        simpa [j'] using output_post
    case isFalse oi_oob=>
      simp [oi_post] at oi_oob ⊢
      if h: n < dst.length - o.val then
        scalar_tac
      else
        apply And.intro
        · scalar_tac
        · intros; scalar_tac -- TODO: Maybe this could be included in `scalar_tac`
  case isFalse =>
    simp
    if h: n < dst.length - o.val then
      apply And.intro
      · scalar_tac
      · intros; scalar_tac
    else
      apply And.intro
      · scalar_tac
      · intros; scalar_tac
termination_by n.val - i.val
decreasing_by scalar_decr_tac/- }}} -/

@[progress]
theorem simple.add_to_vec.spec(dst: Std.Slice Bool)(other: Vec Bool)(o n: Std.Usize)
: o.val + n.val < Std.Usize.max
→ n.val < other.length
→ ∃ nb_added output,
  add_to_vec core.marker.CopyBool dst o other n = .ok (nb_added, output) ∧
  nb_added = Nat.min (n.val) (dst.length - o.val) ∧
  ∀ (j: Fin dst.length), 
    if o.val ≤ j ∧ j < o.val + n.val then output.val[j]! = other.val[j-o.val]!
    else  output.val[j]! = dst.val[j]!
:= by simpa using add_to_vec_loop.spec dst other o n (i := 0#usize)

@[progress]
theorem simple.binxor.spec(a b: Bool)
: ∃ c, binxor a b = .ok c ∧ c = (a ^^ b)
:= by rw [binxor]; cases a <;> cases b <;> simp

@[progress]
theorem simple.xor_long_at_loop.spec(a b: Std.Slice Bool)(pos n i: Std.Usize)
: b.length + pos.val ≤ Std.Usize.max
→ n = Nat.min a.length (b.length + ↑pos)
→ i ≥ pos
→ ∃ output,/- {{{ -/
  xor_long_at_loop a b pos n i = .ok output ∧ 
  output.length = a.length ∧
  ∀ (j: Fin a.length), 
    if i ≤ j.val ∧ j.val < n then output[j]! = (a[j]! ^^ b[j-pos.val]!)
    else output[j]! = a[j]!
:= by
  intro no_overflow n_def i_ge_pos
  rw [xor_long_at_loop]
  split
  case isTrue i_bnd =>
    have i_a_idx: i.val < a.length := by scalar_tac
    let* ⟨ ai, ai_post ⟩ ← Aeneas.Std.Slice.index_usize_spec
    simp [*] at ai_post
    let* ⟨ i', i'_post ⟩ ← Aeneas.Std.Usize.sub_spec
    have i'_b_idx: i'.val < b.length := by scalar_tac
    let* ⟨ bi, bi_post ⟩ ← Aeneas.Std.Slice.index_usize_spec
    simp [*] at bi_post
    let* ⟨ ci, ci_post ⟩ ← simple.binxor.spec
    simp [*] at ci_post
    let* ⟨ c, c_post ⟩ ← Aeneas.Std.Slice.update_spec
    simp [*] at c_post
    let* ⟨ i_succ, i_succ_post ⟩ ← Aeneas.Std.Usize.add_spec
    simp [*] at i_succ_post
    let* ⟨ rest, rest_len, rest_post ⟩ ← spec
    simp [*] at rest_post

    apply And.intro 
    · simp [c_post, rest_len]

    intro j
    let j': Fin c.length := ⟨j.val, by simp [c_post]⟩
    replace rest_post := rest_post j'
    split
    case isTrue j_range =>
      simp [i'_post] at j_range
      have cond : j' < a.length ∧ ↑j' < b.length + ↑pos := by scalar_tac
      if h: i'.val + pos.val + 1 ≤ j' then
        have not_set: ¬ i'.val + pos.val = j.val := by scalar_tac
        simp [And.intro h cond] at rest_post
        simp [List.getElem_set] at rest_post
        rw [if_neg not_set] at rest_post
        simpa using rest_post
      else
        have j_val: j'.val = i'.val + pos.val := by scalar_tac
        simp [h, j_val] at rest_post cond
        conv at rest_post =>
          arg 2
          -- (1) When doing getElem?_set I lose the ?
          simp [List.getElem?_set, cond] 
        simp
        have: j.val = i'.val + pos.val := (rfl: j.val = j'.val) ▸ j_val
        simp [this]
        -- NOTE: I need this to match to the goal, because of (1)
        have: i'.val < b.length := by scalar_tac
        rw [List.getElem?_eq_getElem this]
        exact rest_post
    case isFalse j_oob =>
      simp at rest_post
      have cond: ¬ (i'.val + pos.val + 1 ≤ j'.val ∧ j'.val < a.length ∧ j'.val < b.length + pos.val) := by scalar_tac
      simp [cond] at rest_post; clear cond
      simp only [Std.Slice.length, not_and_or, not_le, not_lt, n_def, i'_post] at j_oob
      have not_set: ¬ (i'.val + pos.val = j.val) := by scalar_tac
      rw [@List.getElem?_set_ne _ a.val _ _ not_set _ ] at rest_post
      simpa using rest_post
  case isFalse i_oob =>
    simp at i_oob ⊢; intro j h1 h2
    scalar_tac
termination_by n.val - i.val
decreasing_by scalar_decr_tac/- }}} -/

@[progress]
theorem simple.xor_long_at.spec(a b: Std.Slice Bool)(pos: Std.Usize)
: b.length + pos.val ≤ Std.Usize.max
→ ∃ output,
  xor_long_at a b pos = .ok output ∧ 
  output.length = a.length ∧
  ∀ (j: Fin a.length), 
    if pos ≤ j.val ∧ j.val < pos.val + b.length then output[j]! = (a[j]! ^^ b[j.val-pos.val]!)
    else output[j]! = a[j]!
:= by/- {{{ -/
  intro no_overflowa
  rw [xor_long_at]
  let* ⟨ i2, i2_post ⟩ ← Aeneas.Std.Usize.add_spec
  simp [Std.core.cmp.impls.OrdUsize.min, Std.toResult, xor_long_at]
  have min_works: ↑(if a.length < ↑i2 then a.len else i2) = a.length.min (b.length + ↑pos) := by
    split <;> scalar_tac
  let* ⟨ res, res_len, res_post ⟩ ← xor_long_at_loop.spec
  rw [min_works] at res_post
  apply And.intro res_len
  intro j
  replace res_post := res_post j
  split
  case isTrue cond =>
    have: j < a.length.min (b.len + pos) := by scalar_tac
    simp [cond, min_works, this] at res_post
    rw [Nat.add_comm] at res_post
    rw [if_pos cond.right] at res_post
    assumption
  case isFalse h =>
    have: ¬ (pos.val ≤ j.val ∧ j.val < b.length + ↑pos) := by scalar_tac
    simp [this] at res_post
    assumption/- }}} -/

@[progress]
theorem simple.xor_long.spec(a b: Std.Slice Bool)
: ∃ c, 
  xor_long a b = .ok c ∧ c = a.val.zipWith (· ^^ ·) b ++ a.val.drop b.length
:= by/- {{{ -/
  rw [xor_long]
  let* ⟨ res, res_len, res_post ⟩ ← simple.xor_long_at.spec
  simp at res_post
  ext i : 1
  if i_idx: i < a.length.min (b.length) then
    have i_a_idx := Nat.lt_min.mp i_idx |>.left
    have i_b_idx := Nat.lt_min.mp i_idx |>.right
    replace res_post := res_post ⟨i, by scalar_tac⟩
    simp [Nat.lt_min.mp i_idx] at res_post
    conv => 
      arg 2
      rw [@List.getElem?_append_left _ _ _ _ (by simp [List.length_zipWith, i_idx])]

    simp [List.getElem?_zipWith]
    simp [List.getElem?_eq_getElem i_a_idx]
    simp [List.getElem?_eq_getElem i_b_idx]
    -- TODO: Prove something about indices and res[i]? beign some (res[i])
    have i_res_idx: i < res.length := res_len ▸ Nat.lt_min.mp i_idx |>.left
    simp [List.getElem?_eq_getElem i_res_idx] at res_post ⊢
    assumption
  else
    conv => 
      arg 2
      rw [@List.getElem?_append_right _ _ _ _ (by simp [List.length_zipWith]; scalar_tac)]
    simp [List.length_zipWith]
    if i_a_idx: i < a.length then
      replace res_post := res_post ⟨i, i_a_idx⟩
      simp [List.getElem?_eq_getElem  (res_len ▸ (i_a_idx))] at res_post ⊢
      if h: a.length > b.length then
        have: ¬ i < b.length := by scalar_tac
        simp [this] at res_post
        have : b.length + (i - Nat.min a.length b.length) = i:= by scalar_tac
        rw [this]
        simp [List.getElem?_eq_getElem i_a_idx] at res_post ⊢
        assumption
      else
        -- NOTE: Over here, I need to simp `i_a_idx` so that scalar_tac uses it properly
        simp at i_a_idx
        scalar_tac
    else
      simp [List.getElem?_eq_none  (res_len ▸ (Nat.le_of_not_lt (i_a_idx)))] at res_post ⊢
      scalar_tac/- }}} -/

end Auxiliary/- }}} -/


def simple.StateArray.toSpec(self: simple.StateArray): Spec.Keccak.StateArray 6 :=
  Spec.Keccak.StateArray.ofBitVec <| (BitVec.ofBoolListLE <| self.val).setWidth (Spec.b 6)

theorem BitVec.getElem_ofBoolListLE{ls: List Bool}{i: Nat}
: ∀ (h: i < ls.length), (BitVec.ofBoolListLE ls)[i] = ls[i]
:= by
  intro i_lt
  cases ls
  case nil => contradiction
  case cons hd tl =>
    simp [BitVec.ofBoolListLE, BitVec.getElem_eq_testBit_toNat]
    cases i
    case zero => simp [Nat.mod_eq_of_lt (Bool.toNat_lt hd)]
    case succ i' => 
      have: (ofBoolListLE tl).toNat * 2 + hd.toNat = (ofBoolListLE tl).toNat.bit hd := by 
        simp [Nat.bit]; cases hd <;> simp [Nat.mul_comm]
      simp [this, Nat.testBit_bit_succ] at i_lt ⊢
      rw [←BitVec.getElem_eq_testBit_toNat (ofBoolListLE tl) i']
      apply BitVec.getElem_ofBoolListLE i_lt

theorem simple.W.spec 
: simple.W = Spec.w 6
:= by native_decide

example: (2^32)-1 <= Std.Usize.max := by
  simp [Std.Usize.max, Std.Usize.numBits_eq]
  obtain h | h := System.Platform.numBits_eq <;> rw [h] <;> omega


@[progress]
theorem  simple.StateArray.index.spec
  (self : StateArray)(x y z: Std.Usize)
(x_idx: x.val < 5)
(y_idx: y.val < 5)
(z_idx: z.val < Spec.w 6)
: ∃ output, self.index (x,y,z) = .ok output ∧ 
    output = self.toSpec.get x.val y.val z.val
:= by 
  rw [index]
  let* ⟨ i, i_post ⟩ ← Aeneas.Std.Usize.mul_spec
  let* ⟨ i1, i1_post ⟩ ← Aeneas.Std.Usize.add_spec
  let* ⟨ i2, i2_post ⟩ ← Aeneas.Std.Usize.mul_spec
  · simp [*, simple.W.spec, Std.Usize.max]
    simp [Spec.w]
    simp [Std.Usize.max, Std.Usize.numBits_eq]
    obtain h | h := System.Platform.numBits_eq <;> rw [h] <;> ring_nf
    all_goals calc ↑y * 2 ^ ↑6 * 5 + ↑x * 2 ^ ↑6 
       _ ≤ 5 * 2 ^ ↑6 * 5 + ↑x * 2 ^ ↑6  := by sorry
       _ ≤ 5 * 2 ^ ↑6 * 5 + 5 * 2 ^ ↑6  := by sorry
       _ ≤ _ := by native_decide
  let* ⟨ i3, i3_post ⟩ ← Aeneas.Std.Usize.add_spec
  · simp [*, simple.W.spec, Std.Usize.max]
    simp [Spec.w]
    simp [Std.Usize.max, Std.Usize.numBits_eq]
    obtain h | h := System.Platform.numBits_eq <;> rw [h] <;> ring_nf
    all_goals calc ↑y * 2 ^ ↑6 * 5 + ↑x * 2 ^ ↑6 + ↑z
       _ ≤ 5 * 2 ^ ↑6 * 5 + ↑x * 2 ^ ↑6 + ↑z := by sorry
       _ ≤ 5 * 2 ^ ↑6 * 5 + 5 * 2 ^ ↑6 + Spec.w 6 := by sorry
       _ ≤ _ := by native_decide
  have: Spec.w 6 * (5 * ↑y + ↑x) + ↑z < 1600 := by
    simp [Spec.w]
    ring_nf
    calc ↑y * 2 ^ ↑6 * 5 + ↑x * 2 ^ ↑6 + ↑z
       _ ≤ 4 * 2 ^ ↑6 * 5 + ↑x * 2 ^ ↑6 + ↑z := by sorry
       _ ≤ 4 * 2 ^ ↑6 * 5 + 4 * 2 ^ ↑6 + (Spec.w 6 -1) := by sorry
       _ < _ := by simp [Spec.w]; native_decide
  let* ⟨ res, res_post ⟩ ← Aeneas.Std.Array.index_usize_spec
  · simp [*, simple.W.spec, Std.Usize.max]
  rw [Spec.Keccak.StateArray.get]

  simp [*, Spec.Keccak.StateArray.encodeIndex]
  -- TODO: These are some ugly `conv`s
  conv => arg 2; arg 2; arg 1; arg 2; rw [Nat.mod_eq_of_lt x_idx]; arg 1; arg 2; rw [Nat.mod_eq_of_lt y_idx]
  conv => arg 2; arg 2; arg 2; rw [Nat.mod_eq_of_lt z_idx]
  simp [simple.W.spec]
  have self_length: self.val.length = 1600 := by simp
  simp [List.getElem?_eq_getElem (self_length ▸ this)]
  -- TODO: Not sure how to make Lean accept this, I suspect the issue comes with the rewriting
  try (rw [BitVec.getElem_ofBoolListLE])
  sorry

/- @[progress] -/
/- theorem Aeneas.Std.UScalar.cast.spec{src_ty : Std.UScalarTy} (tgt_ty : Std.UScalarTy) (x : Std.UScalar src_ty) : -/
/-   ∃ y, Std.toResult (Std.UScalar.cast tgt_ty x) = Std.Result.ok y ∧ y.val = (x: Nat) % 2 ^ tgt_ty.numBits -/
/- := by /1- {{{ -1/ -/
/-   simp [Std.toResult, cast] -/
/-   rw [UScalar.val, BitVec.toNat_setWidth, bv_toNat] -/

/- @[progress] -/
/- theorem Aeneas.Std.UScalar.hcast.spec{src_ty : Std.UScalarTy} (tgt_ty : Std.IScalarTy) (x : Std.UScalar src_ty) : -/
/-   ∃ y, Std.toResult (Std.UScalar.hcast tgt_ty x) = Std.Result.ok y ∧ y.val = (x: Int).bmod (2 ^ tgt_ty.numBits) -/
/- := by -/ 
/-   simp [Std.toResult, hcast] -/
/-   rw [IScalar.val, BitVec.toInt_setWidth, bv_toNat] -/


@[progress]
theorem simple.StateArray.index_mut.spec
  (self : simple.StateArray)(x y z: Std.Usize)
(x_idx: x.val < 5)
(y_idx: y.val < 5)
(z_idx: z.val < Spec.w 6)
: ∃ val upd, self.index_mut (x,y,z) = .ok (val, upd) ∧ 
    val = self.toSpec.get x.val y.val z.val ∧
    ∀ b, (upd b).toSpec = self.toSpec.set x.val y.val z.val b
:= by 
  rw [index_mut]
  let* ⟨ i, i_post ⟩ ← Aeneas.Std.Usize.mul_spec
  let* ⟨ i1, i1_post ⟩ ← Aeneas.Std.Usize.add_spec
  simp [*] at i1_post
  let* ⟨ i2, i2_post ⟩ ← Aeneas.Std.Usize.mul_spec
  · simp [*]; sorry
  simp [*] at i2_post
  let* ⟨ c, c_post ⟩ ← Aeneas.Std.Usize.add_spec
  · simp [*]; sorry
  simp [*] at c_post
  let* ⟨ celem, celem_post ⟩ ← Aeneas.Std.Array.index_mut_usize_spec
  · simp [*]; sorry
  simp
  sorry

theorem Bool.xor_eq_ne(a b: Bool): (a ^^ b) = (a != b) := by cases a <;> cases b <;> decide

@[progress]
theorem simple.theta.theta_c.spec(input : simple.StateArray)(x z: Std.Usize)
(x_idx: x.val < 5)
(z_idx: z.val < Spec.w 6)
: ∃ output, theta.c input x z = .ok output ∧ output = Spec.Keccak.θ.C input.toSpec x z
:= by rw [theta.c]; progress*; simp [*, Spec.Keccak.θ.C]

theorem Aeneas.Std.Usize.max_bound
: 2^32 - 1 <= Std.Usize.max
:= by
  rw [Std.Usize.max_def, Std.Usize.numBits, Std.UScalarTy.numBits]
  cases System.Platform.numBits_eq <;> simp [*]

@[progress]
theorem simple.theta.theta_d.spec(input : simple.StateArray)(x z: Std.Usize)
(x_idx: x.val < 5)
(z_idx: z.val < Spec.w 6)
: ∃ output, theta.d input x z = .ok output ∧ output = Spec.Keccak.θ.D input.toSpec x z
:= by
  rw [theta.d]
  progress* by ((try simp [W.spec]); scalar_tac)
  · trans (2^32 -1)
    · simp [W.spec] at *
      try scalar_tac
      sorry --TODO: Weird that it fails here
    · exact Aeneas.Std.Usize.max_bound
  · simp [*]
    rw [←i2_post, W.spec]
    apply Nat.mod_lt
    decide
  rw [Spec.Keccak.θ.D]
  simp [*]
  congr 2
  · have : (x.val + 4) % 5 = (x.val - 1) % 5 := by sorry
    rw [Nat.cast, NatCast.natCast, Fin.instNatCast, ]
    simp only
    apply Fin.eq_of_val_eq
    simp only [Fin.val_ofNat']
    natify
    simp only [Fin.ofNat']
    simp
    rw [@NatCast.natCast (Fin 5) Fin.instNatCast]
    rw [Fin.instNatCast, NatCast.natCast]
    simp
    sorry
  · sorry
  · sorry

theorem Bool.toNat_mod2_self(b: Bool)
: b.toNat % 2 = b.toNat
:= by cases b <;> simp


theorem BitVec.getElem_set{bv: BitVec n}{b: Bool}{i: Fin n}{j: Nat}
:  {j_lt: j < n}
→ (bv.set i b)[j] = if i = j then b else bv[j]
:= by 
  intro j_lt
  have n_pos: n > 0 := by cases n <;> (first | cases i.isLt | apply Nat.zero_lt_succ )
  have hyp: 2 ∣ 2^n := by
    cases n
    case zero => contradiction
    case succ n' => exact Dvd.intro_left (Nat.pow 2 n') rfl
  have bool_fits{n: Nat}{b:Bool}: n > 0 → b.toNat < 2^n := by
    intro hyp; cases b <;>
    all_goals (
      cases n 
      case zero => contradiction
      case succ n' => simp
    )

  rw [set]
  split
  case isTrue h => 
    subst h
    simp [Nat.mod_mod_of_dvd _ hyp, Bool.toNat_mod2_self, Nat.testBit, BitVec.getLsbD]
  case isFalse =>
    simp
    rw [BitVec.getLsbD, BitVec.toNat_ofNat, Nat.testBit, Nat.shiftRight_eq_div_pow]
    simp [Nat.mod_eq_of_lt (bool_fits n_pos)]
    if h: i < j then
      have: ¬ j < i := by scalar_tac
      have shift_nz: j - i.val > 0 := by scalar_tac
      simp [this, Nat]
      cases bv[i.val] ^^b <;> simp 
      have: 1 / 2 ^ (j - i.val) = 0 := by 
        apply Nat.div_eq_zero_iff_lt (bool_fits (b := false) shift_nz) |>.mpr
        exact bool_fits (b := true) shift_nz
      rw [this]
      simp
    else
      have h: j < i := by scalar_tac
      simp [h]

theorem Spec.Keccak.StateArray.get_set(a: Spec.Keccak.StateArray l)(x x' y y': Fin 5)(z z': Fin (w l))
: (a.set x' y' z' val).get x y z = if x = x' ∧ y = y' ∧ z = z' then val else a.get x y z
:= by
  simp [get, set, BitVec.getElem_set]
  split
  case isTrue h =>
    replace h := encode_inj x x' y y' z z' |>.mp <| Fin.eq_of_val_eq h.symm
    simp [h]
  case isFalse h =>
    have : ¬ (x = x' ∧ y = y' ∧ z = z') := by rintro ⟨rfl,rfl,rfl⟩; exact h rfl
    simp [this]

@[progress]
theorem simple.theta.inner.inner_loop.spec(input a: simple.StateArray)(x y z: Std.Usize)
(x_idx: x.val < 5)
(y_idx: y.val < 5)
(z_loop_bnd: z.val <= Spec.w 6)
: ∃ output, theta.inner.inner_loop input a x y z = .ok output ∧ 
  ∀ (x' y': Fin 5)(z': Fin (Spec.w 6)),
  output.toSpec.get x' y' z' = 
    if x = x' ∧ y = y' ∧ z.val ≤ z'.val then 
        a.toSpec.get x y z'  ^^ Spec.Keccak.θ.D a.toSpec x z'
      else input.toSpec.get x' y' z'
:= by
  rw [theta.inner.inner_loop]
  split
  case isTrue z_idx =>
    simp [W.spec] at z_idx
    let* ⟨ acc_elem, acc_elem_post ⟩ ← simple.StateArray.index.spec
    let* ⟨ aux, aux_post ⟩ ← simple.theta.theta_d.spec
    let* ⟨ res_elem, res_elem_post ⟩ ← simple.binxor.spec
    let* ⟨ old_val, mk_new, old_val.post, mk_new.post ⟩ ← simple.StateArray.index_mut.spec
    let* ⟨ z_succ, z_succ_post ⟩ ← Aeneas.Std.Usize.add_spec
    · simp; apply le_of_lt; calc z.val + 1
        _ < Spec.w 6 + 1 := by exact Nat.add_lt_add_right z_idx 1
        _ < 2^32 -1 := by decide
        _ ≤ Std.Usize.max := Std.Usize.max_bound
    let* ⟨ res, res_post ⟩ ← spec
    /- simp only [z_succ_post] at *; clear z_succ_post -/

    have norm{n: Nat}{x: Std.Usize}(x_lt: x.val < n)[NeZero n]: x.val.cast = Fin.mk x.val x_lt := by
      simp only [Nat.cast, NatCast.natCast, Fin.instNatCast, Fin.ofNat', Nat.mod_eq_of_lt x_lt]

    intro x' y' j
    replace res_post := res_post x' y' j
    split
    case isTrue h =>
      obtain ⟨rfl, rfl,j_bnd⟩ := h
      rw [res_post]; simp [z_succ_post] at res_post ⊢
      intro _
      obtain rfl : j = z.val.cast := by
        apply Fin.eq_of_val_eq; simp [Nat.mod_eq_of_lt z_idx]; scalar_tac
      rw [mk_new.post res_elem]
      simp [Spec.Keccak.StateArray.get_set, aux_post]
      simp [res_elem_post, acc_elem_post]
      simp [←norm, aux_post]

    case isFalse j_oob =>
      /-
      When x ≠ x' or y ≠ y', the result is trivially true.

      Otherwise, the idea here is to prove that if `j` is outside 
      of the interesting bounds, then no modifications have been 
      done to the input.

      To do that we need to reason about `res_post`, showing that
      ¬ z ≤ j → ¬ z + 1 ≤ j and about `mk_new res_elem`, showing
      now that getting an element which is not the one which was
      set gives you the same value as before.
      -/
      rw [not_and_or, not_and_or] at j_oob
      rw [res_post]
      obtain h | h | j_oob := j_oob
      · rw [mk_new.post res_elem, Spec.Keccak.StateArray.get_set]; simp [h]; scalar_tac
      · rw [mk_new.post res_elem, Spec.Keccak.StateArray.get_set]; simp [h]; scalar_tac

      simp only [z_succ_post] at *
      have: ¬ z.val + 1 ≤ j.val := by scalar_tac

      have h2:= mk_new.post res_elem
      simp [h2]
      simp [Spec.Keccak.StateArray.get_set, this]
      rintro rfl rfl rfl
      simp [Nat.mod_eq_of_lt z_idx] at j_oob
  case isFalse z_end =>
    have: z = Spec.w 6 := by simp [W.spec] at z_end; scalar_tac
    simp [this]
    intro x y z'
    simp [Nat.not_le_of_gt z'.isLt]
termination_by (Spec.w 6 + 1) - z.val
-- TODO: I need to do this to impose the order to be ≤, but it should be fine to use <, since
-- z is not incremented if `z = Spec.w 6`. Why does this happen then?
decreasing_by scalar_decr_tac

@[progress]
theorem simple.theta.inner_loop.spec(input a: simple.StateArray)(x y: Std.Usize)
(x_idx: x.val < 5)
(y_loop_bnd: y.val <= 5)
: ∃ output, theta.inner_loop input a x y = .ok output ∧
  ∀ (x' y': Fin 5)(z': Fin (Spec.w 6)),
  output.toSpec.get x' y' z' = 
    if x = x' ∧ y.val ≤ y'.val then
      a.toSpec.get x y' z'  ^^ Spec.Keccak.θ.D a.toSpec x z'
    else input.toSpec.get x' y' z'
:= by 
  rw [inner_loop, inner.inner]
  split
  case isTrue y_idx =>
    let* ⟨ res_z, res_z_post ⟩ ← simple.theta.inner.inner_loop.spec
    let* ⟨ y_succ, y_succ_post ⟩ ← Aeneas.Std.Usize.add_spec
    let* ⟨ res, res_post ⟩ ← spec (a := a) -- ← I do this instead of `· exact a`
    intro x' y' z'
    simp [res_post, y_succ_post, res_z_post]

    if h: x = x' ∧ y.val ≤ y'.val then
      obtain ⟨rfl,y'_range?⟩ := h
      simp [y'_range?]
      intro j_upper_bnd
      have y_y' : y.val = y'.val := by scalar_tac
      simp [y_y']
    else
      rw [not_and_or] at h
      obtain h | j_range? := h
      · simp [h, res_z_post]

      have: ¬ y.val + 1 <= y'.val := by scalar_tac
      simp [j_range?, this]
      rintro rfl rfl
      scalar_tac
  case isFalse y_oob =>
    have: y.val = 5 := by scalar_tac
    simp [this]
    intro x' y' z'
    simp [Nat.not_le_of_gt y'.isLt]
termination_by (5 +1) - y.val
decreasing_by scalar_decr_tac

@[progress]
theorem simple.theta_loop.spec(input a: simple.StateArray)(x: Std.Usize)
(x_loop_bnd: x.val <= 5)
: ∃ output, theta_loop a input x = .ok output ∧ 
  ∀ (x' y': Fin 5)(z': Fin (Spec.w 6)),
    output.toSpec.get x' y' z' = 
      if x.val ≤ x'.val then 
        a.toSpec.get x' y' z'  ^^ Spec.Keccak.θ.D a.toSpec x' z'
      else 
        input.toSpec.get x' y' z'
:= by
  rw [theta_loop, theta.inner]
  split
  case isTrue x_idx =>
    let* ⟨ res_y, res_y_post ⟩ ← simple.theta.inner_loop.spec
    let* ⟨ x_succ, x_succ_post ⟩ ← Aeneas.Std.Usize.add_spec
    let* ⟨ res, res_post ⟩ ← spec
    intro x' y' z'
    simp [res_post, res_y_post, x_succ_post]
    if h: x.val <= x'.val then
      simp [h]; intro _
      have x_x' : x.val = x'.val := by scalar_tac
      simp [x_x']
    else
      have: ¬ x.val + 1 <= x'.val := by scalar_tac
      simp [h, this]; rintro rfl
      scalar_tac
  case isFalse x_oob =>
    have : x.val = 5 := by scalar_tac
    simp [this]
    intro x' y' z'
    simp [Nat.not_le_of_gt x'.isLt]
termination_by 5+1 - x.val
decreasing_by scalar_decr_tac

@[ext]
theorem BitVec.ext{bv1 bv2: BitVec n}
{point_eq: ∀ (i: Fin n), bv1[i] = bv2[i]}
: bv1 = bv2 
:= by
  obtain ⟨⟨a, a_lt⟩⟩ := bv1
  obtain ⟨⟨b, b_lt⟩⟩ := bv2
  simp
  simp [BitVec.getElem_eq_testBit_toNat] at point_eq
  apply Nat.eq_of_testBit_eq
  intro i
  if h: i < n then
    exact point_eq ⟨i, h⟩
  else
    have: a < 2 ^i := calc
      a < 2 ^n := a_lt
      _ ≤ 2 ^i := Nat.pow_le_pow_of_le Nat.one_lt_two (Nat.le_of_not_gt h)
    simp [Nat.testBit_lt_two_pow this]
    have: b < 2 ^i := calc
      b < 2 ^n := b_lt
      _ ≤ 2 ^i := Nat.pow_le_pow_of_le Nat.one_lt_two (Nat.le_of_not_gt h)
    simp [Nat.testBit_lt_two_pow this]

@[ext]
theorem Spec.Keccak.StateArray.ext{a b: StateArray l}
{point_eq: ∀ (x y: Fin 5)(z: Fin (w l)), a.get x y z = b.get x y z}
: a = b
:= by
  obtain ⟨a⟩ := a
  obtain ⟨b⟩ := b
  have bv_point_eq: ∀ (c: Fin (Spec.b l)), a[c] = b[c] := by 
    simp [get] at point_eq
    intro c
    have := point_eq (decodeIndex c).1 (decodeIndex c).2.1 (decodeIndex c).2.2
    simp [Spec.Keccak.StateArray.decode_encode c] at this
    assumption
  simp
  apply BitVec.ext (point_eq := bv_point_eq)

theorem Spec.Keccak.StateArray.get_ofFn{f: Fin 5 × Fin 5 × Fin (w l) → Spec.Bit}(x y: Fin 5)(z: Fin (w l))
: (StateArray.ofFn f).get x y z = f (x,y,z)
:= by simp [ofFn, get, BitVec.ofFn, encode_decode]

@[progress]
theorem simple.theta.spec(input: simple.StateArray)
: ∃ output, theta input = .ok output ∧ output.toSpec = Spec.Keccak.θ input.toSpec
:= by 
  rw [theta, Spec.Keccak.θ, DefaultsimpleStateArray.default]
  let* ⟨ res, res_post ⟩ ← simple.theta_loop.spec
  ext x y z
  simp [res_post x y z, Spec.Keccak.StateArray.get_ofFn]

@[progress]
theorem sponge.spec (r : Std.Usize) (bs : Vec Bool) (d : Std.Usize) (r_ne_zero: r.val ≠ 0)
: ∃ output,
  sha3.simple.sponge r bs d = .ok output ∧
  output.val = (@Spec.sponge _ (f := Spec.Keccak.P 6 (nᵣ := 24)) (pad := Spec.«pad10*1») r.val ⟨r_ne_zero⟩ bs.toBitArray d.val).toList
:= sorry


section FinalResult

@[progress]
theorem sha3_224.spec(input: Vec Bool)
: ∃ output,
  sha3.simple.sha3_224 input = .ok (output) ∧
  output.val = (Spec.SHA3_224 input.toBitArray).toList
:= by
  sorry

@[progress]
theorem sha3_256.spec(input: Vec Bool)
: ∃ output,
  sha3.simple.sha3_256 input = .ok (output) ∧
  output.val = (Spec.SHA3_256 input.toBitArray).toList
:= by
  sorry

@[progress]
theorem sha3_384.spec(input: Vec Bool)
: ∃ output,
  sha3.simple.sha3_384 input = .ok (output) ∧
  output.val = (Spec.SHA3_384 input.toBitArray).toList
:= by
  sorry

@[progress]
theorem sha3_512.spec(input: Vec Bool)
: ∃ output,
  sha3.simple.sha3_512 input = .ok (output) ∧
  output.val = (Spec.SHA3_512 input.toBitArray).toList
:= by
  sorry
end FinalResul
