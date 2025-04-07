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

attribute [-simp] List.getElem!_eq_getElem?_getD

/- Not using Fin below: it works a lot better (see the other version with `Fin` below).
   There are many issues with Fin:
   - if `n = m`, it is non trivial to instantiate a `∀ (j : Fin n), ...` with a `j : Fin m`
   - if we have expression `a[j.val]!` where `j : Fin n`, we can't match it with, e.g., `a[i + pos]`,
     even if `j.val = i + pos`. It would work if we had a better treatment of equivalence classes,
     a bit like in SMT solvers (and grind is doing this, from my understanding)
-/
theorem simple.xor_long_at_loop.spec'(a b: Std.Slice Bool)(pos n i: Std.Usize)
: b.length + pos.val ≤ Std.Usize.max
→ n = Nat.min a.length (b.length + ↑pos)
→ i ≥ pos
→ ∃ output,/- {{{ -/
  xor_long_at_loop a b pos n i = .ok output ∧
  output.length = a.length ∧
  (∀ (j : Nat), (i ≤ j ∧ j < n) → output[j]! = (a[j]! ^^ b[j-pos.val]!)) ∧
  (∀ (j: Nat), ¬ (i ≤ j ∧ j < n) → output[j]! = a[j]!)
:= by
  intro no_overflow n_def i_ge_pos
  unfold xor_long_at_loop
  rename Std.Usize => i0
  progress*?
  . split_conjs
    . scalar_tac
    . -- TODO: this should be automated, but we need something like grind,
      -- in particular to make the case disjunction
      intro j hj
      simp at *
      dcases hj' : j = i0.val <;> simp_lists [*]
    . -- TODO: this should be automated
      intro j hj
      simp at *
      dcases hj' : j = i0.val <;> simp_lists [*]
      simp
  . simp
    scalar_tac
termination_by n.val - i.val
decreasing_by scalar_decr_tac

@[progress]
theorem simple.xor_long_at_loop.spec(a b: Std.Slice Bool)(pos n i: Std.Usize)
: b.length + pos.val ≤ Std.Usize.max
→ n = Nat.min a.length (b.length + ↑pos)
→ i ≥ pos
→ ∃ output,/- {{{ -/
  xor_long_at_loop a b pos n i = .ok output ∧
  output.length = a.length ∧
  (∀ (j: Fin a.length), (i ≤ j.val ∧ j.val < n) → output[j]! = (a[j]! ^^ b[j-pos.val]!)) ∧
  (∀ (j: Fin a.length), ¬ (i ≤ j.val ∧ j.val < n) → output[j]! = a[j]!)
:= by
  intro no_overflow n_def i_ge_pos
  unfold xor_long_at_loop
  rename Std.Usize => i0
  progress*
  . split_conjs
    . scalar_tac
    . -- TODO: this should be automated, but we need something like grind
      intro j hj
      replace res_post_2 := res_post_2 ⟨ j, by scalar_tac ⟩
      replace res_post_3 := res_post_3 ⟨ j, by scalar_tac ⟩
      simp at *
      dcases hj' : j.val = i0.val
      . simp_lists [res_post_3, s1_post]
        simp [*]
      . simp_lists [res_post_2]
        simp [*]
        simp_lists
    . -- TODO: this should be automated
      intro j hj
      replace res_post_2 := res_post_2 ⟨ j, by scalar_tac ⟩
      replace res_post_3 := res_post_3 ⟨ j, by scalar_tac ⟩
      simp at *
      dcases hj' : j.val = i0.val
      . simp_lists [res_post_3, s1_post]
      . simp_lists [res_post_3, s1_post]
  . simp
    scalar_tac
termination_by n.val - i.val
decreasing_by scalar_decr_tac

@[progress]
theorem simple.xor_long_at.spec(a b: Std.Slice Bool)(pos: Std.Usize)
: b.length + pos.val ≤ Std.Usize.max
→ ∃ output,
  xor_long_at a b pos = .ok output ∧
  output.length = a.length ∧
  (∀ (j: Fin a.length), (pos ≤ j.val ∧ j.val < pos.val + b.length) → output[j]! = (a[j]! ^^ b[j.val-pos.val]!)) ∧
  (∀ (j:Fin a.length), ¬ (pos ≤ j.val ∧ j.val < pos.val + b.length) → output[j]! = a[j]!)
:= by/- {{{ -/
  intro no_overflowa
  unfold xor_long_at
  progress*
  simp_lists [*]; simp

@[progress]
theorem simple.xor_long.spec(a b: Std.Slice Bool)
: ∃ c,
  xor_long a b = .ok c ∧ c = a.val.zipWith (· ^^ ·) b ++ a.val.drop b.length
:= by/- {{{ -/
  unfold xor_long
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

theorem Aeneas.Std.Usize.max_bound
: 2^32 - 1 <= Std.Usize.max
:= by
  rw [Std.Usize.max_def, Std.Usize.numBits, Std.UScalarTy.numBits]
  cases System.Platform.numBits_eq <;> simp [*]

theorem Nat.lt_packing_right {x y: Nat}(x_lt: x < n)(y_lt: y < m)
: n*y + x < n*m
:= by
  have n_pos: n > 0 := by apply Nat.pos_of_ne_zero; intro h; simp [h] at x_lt
  have m_pos: m > 0 := by apply Nat.pos_of_ne_zero; intro h; simp [h] at y_lt
  calc n*y + x
    _ = n * y + x := rfl
    _ ≤ n * (m-1) + x := by
      apply Nat.add_le_add_right
      apply Nat.mul_le_mul_left
      apply Nat.le_pred_iff_lt m_pos |>.mpr
      exact y_lt
    _ ≤ n * (m-1) + (n-1) := by
      apply Nat.add_le_add_left
      apply Nat.le_pred_iff_lt n_pos |>.mpr
      exact x_lt
    _ < n * m := by
      simp [Nat.mul_sub, ←Nat.add_sub_assoc n_pos]
      have: n*m >= n := by
        conv => arg 2; rw [←Nat.mul_one n]
        apply Nat.mul_le_mul (Nat.le_refl n) m_pos
      simp [Nat.sub_add_cancel this]
      exact And.intro n_pos m_pos

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
  · simp [*, simple.W.spec]
    apply le_of_lt
    calc Spec.w 6 * (5 * ↑y + ↑x)
     _ ≤ Spec.w 6 * (5 * 5) := by
          apply Nat.mul_le_mul_left (k := Spec.w 6)
          exact Nat.le_of_lt (Nat.lt_packing_right x_idx y_idx)
     _ < 2^32 - 1 := by simp [Spec.w]; decide
     _ ≤ Std.Usize.max := Std.Usize.max_bound
  let* ⟨ i3, i3_post ⟩ ← Aeneas.Std.Usize.add_spec
  · simp [*, simple.W.spec]
    apply le_of_lt
    calc Spec.w 6 * (5 * ↑y + ↑x) + ↑z
     _ ≤ Spec.w 6 * (5 * 5 - 1) + ↑z := by
          apply Nat.add_le_add_right (k := ↑z)
          apply Nat.mul_le_mul_left (k := Spec.w 6)
          exact Nat.le_pred_of_lt (Nat.lt_packing_right x_idx y_idx)
     _ < Spec.w 6 * (5 * 5) := by
          apply Nat.lt_packing_right z_idx (by decide: 5*5 - 1 < 5 * 5)
     _ < 2^32 - 1 := by simp [Spec.w]; decide
     _ ≤ Std.Usize.max := Std.Usize.max_bound
  have: Spec.w 6 * (5 * ↑y + ↑x) + ↑z < 1600 := by
    simp [Spec.w]
    calc Spec.w 6 * (5 * ↑y + ↑x) + ↑z
     _ ≤ Spec.w 6 * (5 * 5 - 1) + ↑z := by
          apply Nat.add_le_add_right (k := ↑z)
          apply Nat.mul_le_mul_left (k := Spec.w 6)
          exact Nat.le_pred_of_lt (Nat.lt_packing_right x_idx y_idx)
     _ < Spec.w 6 * (5 * 5) := by
          apply Nat.lt_packing_right z_idx (by decide: 5*5 - 1 < 5 * 5)
  let* ⟨ res, res_post ⟩ ← Aeneas.Std.Array.index_usize_spec
  · simp [*, simple.W.spec, Std.Usize.max]
  rw [Spec.Keccak.StateArray.get]

  simp [*, Spec.Keccak.StateArray.encodeIndex]
  -- TODO: These are some ugly `conv`s
  conv => arg 2; arg 2; arg 1; arg 2; rw [Nat.mod_eq_of_lt x_idx]; arg 1; arg 2; rw [Nat.mod_eq_of_lt y_idx]
  conv => arg 2; arg 2; arg 2; rw [Nat.mod_eq_of_lt z_idx]
  simp [simple.W.spec]
  have self_length: self.val.length = 1600 := by simp
  simp [toSpec]

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
  simp only [*] at i1_post
  let* ⟨ i2, i2_post ⟩ ← Aeneas.Std.Usize.mul_spec
  · simp [*, W.spec]
    -- TODO: Hmm, this should be using transitivity to get <, no?
    apply le_of_lt
    calc Spec.w 6 * (5 * y.val + x.val)
      _ < Spec.w 6 * (5 * 5) := by
          apply Nat.mul_lt_mul_left (by simp [Spec.w]: 0 < Spec.w 6) |>.mpr
          exact Nat.lt_packing_right x_idx y_idx
      _ < 2^32 - 1 := by decide
      _ ≤ Std.Usize.max := Std.Usize.max_bound
  simp only [*] at i2_post
  let* ⟨ c, c_post ⟩ ← Aeneas.Std.Usize.add_spec
  · simp [*, W.spec]
    apply le_of_lt
    calc Spec.w 6 * (5 * ↑y + ↑x) + ↑z
     _ ≤ Spec.w 6 * (5 * 5 - 1) + ↑z := by
          apply Nat.add_le_add_right (k := ↑z)
          apply Nat.mul_le_mul_left (k := Spec.w 6)
          exact Nat.le_pred_of_lt (Nat.lt_packing_right x_idx y_idx)
     _ < Spec.w 6 * (5 * 5) := by
          apply Nat.lt_packing_right z_idx (by decide: 5*5 - 1 < 5 * 5)
     _ < 2^32 - 1 := by simp [Spec.w]; decide
     _ ≤ Std.Usize.max := Std.Usize.max_bound
  simp only [*] at c_post
  have c_idx :↑c < Std.Array.length self := by
    simp [*, W.spec]
    calc Spec.w 6 * (5 * ↑y + ↑x) + ↑z
     _ ≤ Spec.w 6 * (5 * 5 - 1) + ↑z := by
          apply Nat.add_le_add_right (k := ↑z)
          apply Nat.mul_le_mul_left (k := Spec.w 6)
          exact Nat.le_pred_of_lt (Nat.lt_packing_right x_idx y_idx)
     _ < Spec.w 6 * (5 * 5) := by
          apply Nat.lt_packing_right z_idx (by decide: 5*5 - 1 < 5 * 5)
  let* ⟨ celem, celem_post ⟩ ← Aeneas.Std.Array.index_mut_usize_spec
  simp [-Bool.forall_bool,celem_post]
  simp only [Std.Array.length] at c_idx
  have c_encode: c.val = @Spec.Keccak.StateArray.encodeIndex 6 x.val.cast y.val.cast z.val.cast := by
    simp [Spec.Keccak.StateArray.encodeIndex, Nat.mod_eq_of_lt y_idx, Nat.mod_eq_of_lt x_idx, Nat.mod_eq_of_lt z_idx, c_post, W.spec]
  constructor
  · simp [Spec.Keccak.StateArray.get, ←c_encode]
    simp [toSpec]
  · intro b
    ext i j k
    simp [Spec.Keccak.StateArray.get, Spec.Keccak.StateArray.set, ←c_encode]
    /- let c2 := Spec.Keccak.StateArray.encodeIndex i j k -/
    /- have c2_encode: c2 = Spec.Keccak.StateArray.encodeIndex i j k := rfl -/
    /- rw [←c2_encode] -/
    simp [toSpec, Spec.Keccak.StateArray.set, Std.Array.set]
    /- have h := BitVec.setWidth_eq (BitVec.ofBoolListLE self.val) -/
    /- have : self.val.length = 1600 := by simp only [List.Vector.length_val, Std.UScalar.ofNat_val_eq] -/
    simp [BitVec.getElem_set]
    if h: c.val = Spec.Keccak.StateArray.encodeIndex i j k then
      rw [←h]
      simp [Nat.mod_eq_of_lt (by simpa [Spec.b, Spec.w, self.property] using c_idx: c.val < Spec.b 6), ←c_encode]
      have c_set_idx: c.val < (self.val.set c.val b).length := by simpa using c_idx
      simp [List.getElem?_eq_getElem c_set_idx]
    else
      rw [c_encode] at h
      simp [h]
      have:(Spec.Keccak.StateArray.encodeIndex i j k).val < (self.val.set ↑c b).length := by
        have := (Spec.Keccak.StateArray.encodeIndex i j k).isLt
        simp only [List.length_set]
        simp only [Spec.b, Spec.w] at this
        simp
        exact this
      rw [←c_encode] at h
      simp [List.getElem?_set_ne h]

theorem Bool.xor_eq_ne(a b: Bool): (a ^^ b) = (a != b) := by cases a <;> cases b <;> decide

@[progress]
theorem simple.theta.theta_c.spec(input : simple.StateArray)(x z: Std.Usize)
(x_idx: x.val < 5)
(z_idx: z.val < Spec.w 6)
: ∃ output, theta.c input x z = .ok output ∧ output = Spec.Keccak.θ.C input.toSpec x z
:= by rw [theta.c]; progress*; simp [*, Spec.Keccak.θ.C]

@[progress]
theorem simple.theta.theta_d.spec(input : simple.StateArray)(x z: Std.Usize)
(x_idx: x.val < 5)
(z_idx: z.val < Spec.w 6)
: ∃ output, theta.d input x z = .ok output ∧ output = Spec.Keccak.θ.D input.toSpec x z
:= by
  rw [theta.d]
  progress* by ((try simp [W.spec]); scalar_tac)
  · trans (2^32 -1)
    · have: i2.val = W.val - 1 := by scalar_tac
      simp [W.spec, Spec.w] at *
      simp [this, Fin.val_ofNat']
      --TODO: Weird that `scalar_tac` fails here
      /- scalar_tac -/
      calc _
        _ ≤ (2^6 - 1) + (2^(6: Fin 7).val - 1) :=
          Nat.add_le_add_right (Nat.le_pred_iff_lt (Nat.two_pow_pos 6) |>.mpr z_idx) (k := 2^(6: Fin 7).val - 1)
        _ ≤ 2^32 - 1 := by decide
    · exact Aeneas.Std.Usize.max_bound
  · simp [*]
    rw [←i2_post, W.spec]
    apply Nat.mod_lt
    decide
  rw [Spec.Keccak.θ.D]
  simp [*]
  congr 2
  · apply Fin.eq_of_val_eq
    simp [Fin.sub_def, Nat.add_comm]
  · apply Fin.eq_of_val_eq
    simp [Fin.add_def]
  · apply Fin.eq_of_val_eq
    simp [Fin.sub_def, ←i2_post, W.spec]
    have: i2.val = W.val - 1 := by scalar_tac
    simp [this, W.spec, Nat.add_comm]




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
decreasing_by

  scalar_decr_tac

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
    let* ⟨ res, res_post ⟩ ← spec (a := a) (y := y_succ) -- ← I do this instead of `· exact a`
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
decreasing_by

  scalar_decr_tac

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

@[progress]
theorem simple.theta.spec(input: simple.StateArray)
: ∃ output, theta input = .ok output ∧ output.toSpec = Spec.Keccak.θ input.toSpec
:= by
  rw [theta, Spec.Keccak.θ, DefaultsimpleStateArray.default]
  let* ⟨ res, res_post ⟩ ← simple.theta_loop.spec
  ext x y z
  simp [res_post x y z, Spec.Keccak.StateArray.get_ofFn]

theorem Array.getElem?_chunks_exact(k: Nat)(arr: Array α)(i: Nat)
: i < arr.size / k
→ Vector.toArray <$> (arr.chunks_exact k)[i]? = some (arr.extract (k*i) (k*(i+1)))
:= by sorry

@[progress]
private theorem auxiliary.Slice.index(start stop: Std.Usize)(arr: Std.Slice α)(k i: Nat)
: start.val = k * i
→ stop.val = k * (i + 1)
→ i < arr.length / k
→ k > 0
→ ∃ output,
  Std.core.slice.index.SliceIndexRangeUsizeSlice.index {start, end_ := stop} arr = .ok output ∧
  output.val = arr.val.slice start.val stop.val
:= by
  intro start_def stop_def i_bnd k_pos
  simp [Std.core.slice.index.SliceIndexRangeUsizeSlice.index]

  have start_lt_stop: start.val < stop.val := by simp [start_def, stop_def, Nat.mul_lt_mul_left k_pos |>.mpr]
  have stop_le_len: stop.val ≤ arr.length :=
    calc stop.val
      _ = k * (i + 1) := stop_def
      _ ≤ k * (arr.length / k) := Nat.mul_le_mul_left k i_bnd
      _ ≤ arr.length := Nat.mul_div_le arr.length k

  simp [le_of_lt start_lt_stop, stop_le_len]

/- @[progress] -/
theorem simple.sponge_absorb_loop.spec
  (bs : Std.Slice Bool) (r : Std.Usize) [NeZero r.val](output : Aeneas.Std.Array Bool 1600#usize)
  (suffix : Std.Slice Bool)(n i : Std.Usize)
: n = bs.length / r
→ ∃ output,
  sponge_absorb_loop bs r output suffix n i = .ok output ∧
  output.val = (Spec.sponge.absorb (f:=Spec.Keccak.P 6 24) (pad:=Spec.«pad10*1») r.val (Array.mk <| bs.val ++ suffix.val)).toArray.toList
:= by
  intro n_def
  unfold simple.sponge_absorb_loop
  split
  case isTrue h =>
    let* ⟨ i1, i1_post ⟩ ← Aeneas.Std.Usize.mul_spec
    · simp [n_def] at h
      calc r * i.val
        _ ≤ r * (bs.length / r) := Nat.mul_le_mul_left r.val (le_of_lt h)
        _ ≤ bs.length := Nat.mul_div_le bs.length r.val
        _ ≤ Std.Usize.max := bs.property
    let* ⟨ i2, i2_post ⟩ ← Aeneas.Std.Usize.add_spec
    let* ⟨ i3, i3_post ⟩ ← Aeneas.Std.Usize.mul_spec
    · simp [n_def, i2_post] at h ⊢
      calc r * (i.val + 1)
        _ ≤ r * (bs.length / r) := Nat.mul_le_mul_left r.val h
        _ ≤ bs.length := Nat.mul_div_le bs.length r.val
        _ ≤ Std.Usize.max := bs.property
    -- TODO: Should probably use a separate progress theorem for this.
    simp [Std.core.slice.index.Slice.index]
    let* ⟨ chunk, chunk_post ⟩ ← auxiliary.Slice.index
    · exact r.val.pos_of_neZero
    progress
  case isFalse h =>
    let* ⟨ i1, i1_post ⟩ ← Aeneas.Std.Usize.mul_spec
    · sorry
    sorry

@[progress]
theorem simple.sponge_absorb.spec
  (bs : Std.Slice Bool) (r : Std.Usize) [NeZero r.val](output : Aeneas.Std.Array Bool 1600#usize)
  (suffix : Std.Slice Bool)
: ∃ output,
  sponge_absorb bs r output suffix = .ok output ∧
  output.val = (Spec.sponge.absorb (f:=Spec.Keccak.P 6 24) (pad:=Spec.«pad10*1») r.val (Array.mk <| bs.val ++ suffix.val)).toArray.toList
:= by
  sorry

-- @[progress]
theorem simple.sponge.spec (r : Std.Usize) (bs output suffix: Std.Slice Bool)
[NeZero r.val]
/- (r_ne_zero: r.val ≠ 0) -/
: ∃ output,
  simple.sponge r bs output suffix = .ok output ∧
  output.val = (Spec.sponge (f := Spec.Keccak.P 6 (nᵣ := 24)) (pad := Spec.«pad10*1») r.val (Array.mk <| bs.val ++ suffix.val ) output.length).toArray.toList
:= by

  sorry


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
