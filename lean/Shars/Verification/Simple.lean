import Aeneas
import Shars.Definitions.Simple
import Sha3.Spec
import Sha3.Utils
import Init.Data.Vector.Lemmas

open Aeneas hiding Std.Array
open Std.alloc.vec 

attribute [simp] sha3.simple.Defaultsha3simpleStateArray.default


@[coe] def Aeneas.Std.alloc.vec.Vec.toBitString(v: Vec Bool): Spec.BitString v.length := ⟨Array.mk v.val, by simp⟩
@[coe] def Aeneas.Std.alloc.vec.Vec.toBitArray(v: Vec Bool): _root_.Array Spec.Bit := Array.mk v.val

section Auxiliary/- {{{ -/

theorem getElem_of_getElem?_in_bounds{xs: List α}{i: Nat}
(i_idx: i < xs.length)
: xs[i]? = some (xs[i])
:= by simp only [List.getElem?_eq_some_getElem_iff]

@[progress]
theorem sha3.simple.add_to_vec_loop.spec(bs: Vec Bool)(other: Vec Bool)(n i: Std.Usize)
: n < other.length
→ bs.length + (n - i) < Std.Usize.max
→ ∃ output,
  add_to_vec_loop sha3.core.marker.CopyBool bs other n i = .ok output ∧
  bs.val ++ (other.val.take n.val).drop i.val = output.val
:= by
  intro hyp no_overflow
  rw [add_to_vec_loop]
  if h: i < n then
    have i_idx := Nat.lt_trans h hyp
    simp [*]
    let* ⟨ t, t_post ⟩ ← Aeneas.Std.Slice.index_usize_spec
    let* ⟨ dst1, dst1_post ⟩ ← Aeneas.Std.alloc.vec.Vec.push_spec
    let* ⟨ i1, i1_post ⟩ ← Aeneas.Std.Usize.add_spec
    let* ⟨ res, res_post ⟩ ← spec
    · simp [dst1_post, i1_post]; scalar_tac
    simp [dst1_post, i1_post, t_post] at res_post
    simp [getElem_of_getElem?_in_bounds i_idx] at res_post
    have := List.getElem_cons_drop (other.val.take ↑n) i (by scalar_tac)
    simp at this -- List.getElem_take
    simpa [this] using res_post
  else
    simp [h]
    left; scalar_tac
termination_by n.val - i.val
decreasing_by scalar_decr_tac

@[progress]
theorem sha3.simple.add_to_vec.spec(bs: Vec Bool)(other: Vec Bool)(n: Std.Usize)
: n < other.length
→ bs.length + n  < Std.Usize.max
→ ∃ output,
  add_to_vec sha3.core.marker.CopyBool bs other n = .ok output ∧
  bs.val ++ other.val.take n.val = output.val
:= by
  intro h1 h2
  rw [add_to_vec]
  progress as ⟨_, post⟩
  simpa using post

@[progress]
theorem sha3.simple.binxor.spec(a b: Bool)
: ∃ c, binxor a b = .ok c ∧ c = (a ^^ b)
:= by
  rw [binxor]
  cases a <;> cases b <;> simp

theorem tmod_bounds{a b: Int}
: a.tmod b < 0 -> a < 0
:= match a with
  | .ofNat m => by
    cases b <;> simp only [Int.tmod]
    all_goals (
      intro _ ; contradiction
    )
  | .negSucc m => by 
    cases b <;> simp only [Int.tmod]
    all_goals (
      rintro -;
      exact Int.negSucc_lt_zero m
    )

theorem int_natAbs_nf_neg{a: Int}
: a < 0 → a = - a.natAbs 
:= by
  intro h
  cases a
  · contradiction
  · rfl

theorem int_natAbs_nf_nonneg{a: Int}
: a >= 0 → a = a.natAbs 
:= by
  intro h
  cases a
  · rfl
  · contradiction

#eval let (a,b) := (-5,-3); Int.ediv a b - Int.tdiv a b
#eval let (a,b) := ( 5,-3); Int.ediv a b - Int.tdiv a b
#eval let (a,b) := ( 5, 3); Int.ediv a b - Int.tdiv a b
#eval let (a,b) := (-5, 3); Int.ediv a b - Int.tdiv a b
#eval let (a,b) := (-4, 3); Int.ediv a b - Int.tdiv a b
#eval let (a,b) := (-4, 0); Int.ediv a b - Int.tdiv a b

#eval Int.sign 10 * 10
#check Int.tmod
#check Int.emod

def Int.my_tmod : Int → Int → Int
  | ofNat m, n => ofNat (m % natAbs n)
  | negSucc m,  n => - ofNat (Nat.succ m % n.natAbs)

theorem Int.smthg(a b: Int): a.my_tmod b = a.tmod b := by
  unfold my_tmod tmod; cases a <;> cases b <;> simp

theorem Int.tdiv_sub_ediv(a b : Int)
: a.ediv b - a.tdiv b = if b∣a ∨ a >= 0 then 0 else b.sign
:= by
  if div: b∣a then
    simp [div]
    have emod_def := Int.emod_def a b 
    rw [emod_eq_zero_of_dvd div] at emod_def
    have tmod_def := Int.tmod_def a b 
    rw [dvd_iff_tmod_eq_zero.mp div, emod_def] at tmod_def
    simp [HDiv.hDiv, Div.div] at tmod_def
    obtain mods_eq | b_zero := tmod_def
    · simp [mods_eq]
    · simp [b_zero]
      cases a <;> simp [ediv]
  else if a_nonneg: a ≥ 0 then
    simp [a_nonneg]
    cases a 
    case negSucc => contradiction
    cases b <;> simp [ediv,tdiv]
  else
    simp [div, a_nonneg]
    cases a
    case ofNat => simp at a_nonneg
    rename_i a'

    cases b
    case ofNat b' =>
      cases b'<;> simp [ediv, tdiv]
      rename_i b'
      simp at *
      have : ((a': Int) + 1) / (↑b' + 1) = ↑a'/ (↑b' + 1) + 1 / (↑b' + 1) := by
        sorry
      rw[this]
      have : 1 / (↑b' + 1) = 0 := by simp

      sorry
    case negSucc b' =>
      sorry

theorem tmod_with_nat_mod{b : Int}
: b ≠ 0
→ ∀ {a : Int},
a.tmod b = a % (b.natAbs) - (if a.tmod b < 0 then b.natAbs else 0)
:= by 
  intro b_nonneg a
  if h: a.tmod b < 0 then
    simp [h]
    sorry
  else
    have: a >= 0 := by
      sorry
    simp only [h, reduceIte, Int.sub_zero]
    have this2: (0: Int) <= b.natAbs := by simp
    have :=  Int.tmod_eq_emod this this2
    rw [←this]
    simp
    if h: b < 0 then
      rw [int_natAbs_nf_neg h]
      simp
    else
      simp at h
      rw [int_natAbs_nf_nonneg h]
      simp

example(a b: Nat): Int.subNatNat a b = (a: Int) - b := by exact Int.subNatNat_eq_coe

theorem Nat.mod_characteristic(c a b: Int)
: 0 <= c ∧ c < b ∧ (c ≡ a [ZMOD b]) → c = a % b 
:= by
  exact?

theorem tmod_with_nat_mod'{b : Int}
: b ≠ 0
→ ∀ {a : Int},
  a.tmod b < 0
→ a.tmod b = (a.emod b) - b.natAbs
:= by 
  intro b_ne_zero a a_mod_b_neg
  cases a
  case ofNat a => cases b <;> rw [Int.tmod] at a_mod_b_neg <;> contradiction
  case negSucc a' =>
    cases b <;> rw [Int.tmod]
    case ofNat b' => 
      rw [Int.emod]
      rw [Int.tmod] at a_mod_b_neg
      simp only [Int.ofNat_emod, Left.neg_neg_iff] at a_mod_b_neg
      have a_mod_b_neg := Int.ofNat_lt.mp a_mod_b_neg
      simp [Int.subNatNat_eq_coe, HMod.hMod, Mod.mod] at *
      rw [←Int.neg_add]
      congr
      have: (n m : Nat) → n.mod m = n % m := by exact fun n m => rfl
      simp [this] at *
      have one_elem_b': 1 % b' = 1 := by
        have: b' ≠ 1 := by
          intro b_eq_1
          simp [b_eq_1, Nat.mod_one] at a_mod_b_neg
        exact Nat.mod_eq_iff_lt (b_ne_zero) |>.mpr (by scalar_tac: 1 < b')
      have: a' % b' + 1 % b' < b' := by
        rw [one_elem_b']
        sorry
      simp [Nat.add_mod_of_add_mod_lt this]
      have : 1 % b' = 1 := Nat.mod_eq_iff_lt (b_ne_zero) |>.mpr (by scalar_tac: 1 < b')
      simp [this, Nat.add_comm]
    case negSucc b' => 
      sorry


@[progress]
theorem sha3.simple.rem_euclid_i8.spec(a b: Std.I8)
: b.val ≠ 0
→ ∃ c, rem_euclid_i8 a b = .ok c ∧ c = a.val % b
:= by 
  intro b_ne_zero
  rw [rem_euclid_i8]
  let* ⟨ a1, a1_post ⟩ ← Aeneas.Std.I8.rem_spec
  split
  case isTrue h =>
    simp [a1_post] at h
    split
    case isTrue b_neg =>
      let* ⟨ res, res_post ⟩ ← Aeneas.Std.I8.sub_spec
      rw [tmod_with_nat_mod b_ne_zero] at a1_post
      simp [res_post, a1_post, h]
      rw [int_natAbs_nf_neg b_neg]
      simp
    case isFalse b_nonneg =>
      simp at b_nonneg
      let* ⟨ res, res_post ⟩ ← Aeneas.Std.I8.add_spec
      rw [tmod_with_nat_mod b_ne_zero] at a1_post 
      simp [res_post, a1_post, h]
      have b_nonneg: b.val >= 0 := by scalar_tac
      rw [int_natAbs_nf_nonneg b_nonneg]
      simp
  case isFalse h =>
    simp [a1_post] at h
    rw [tmod_with_nat_mod b_ne_zero] at a1_post
    simp [a1_post, h]

@[progress]
theorem sha3.simple.rem_euclid_isize.spec(a b: Std.Isize)
: b.val ≠ 0
→ ∃ c, rem_euclid_isize a b = .ok c ∧ c = a.val % b
:= sorry

end Auxiliary/- }}} -/


@[simp] def sha3.simple.StateArray.toSpec(self: sha3.simple.StateArray): Spec.Keccak.StateArray 6 :=
  let data := Array.mk self.val
  Spec.Keccak.StateArray.ofVector ⟨data, by simp [data]; native_decide ⟩

@[simp] def sha3.simple.StateArray.toSpec_getElem_eq_val_getElem(self: sha3.simple.StateArray)
  (i: Fin (Spec.b 6))
: self.toSpec.toVector[i] = self.val[i]'(by 
    simp
    calc i.val 
      _ < Spec.b 6 := i.isLt
      _ = 1600 := by native_decide)
:= by simp only [Fin.isValue, toSpec, Fin.getElem_fin, Vector.getElem_mk, List.getElem_toArray]

theorem sha3.simple.W.spec 
: sha3.simple.W = Spec.w 6
:= by native_decide


example: (2^32)-1 <= Std.Usize.max := by
  simp [Std.Usize.max, Std.Usize.numBits_eq]
  obtain h | h := System.Platform.numBits_eq <;> rw [h] <;> omega


@[progress]
theorem  sha3.simple.StateArray.index.spec
  (self : simple.StateArray)(x y: Std.U8)(z: Std.Usize)
(x_idx: x.val < 5)
(y_idx: y.val < 5)
(z_idx: z.val < Spec.w 6)
: ∃ output, self.index (x,y,z) = .ok output ∧ 
    output = self.toSpec.get x.val y.val z.val
:= by 
  rw [index]
  let* ⟨ i, i_post ⟩ ← Aeneas.Std.UScalar.cast.progress_spec
  let* ⟨ i1, i1_post ⟩ ← Aeneas.Std.Usize.mul_spec
  · simp [i_post]; scalar_tac
  let* ⟨ i2, i2_post ⟩ ← Aeneas.Std.UScalar.cast.progress_spec
  let* ⟨ i3, i3_post ⟩ ← Aeneas.Std.Usize.add_spec
  · simp [i1_post, i2_post]; scalar_tac
  let* ⟨ i4, i4_post ⟩ ← Aeneas.Std.Usize.mul_spec
  · simp [*, sha3.simple.W.spec, Std.Usize.max]
    simp [Spec.w]
    simp [Std.Usize.max, Std.Usize.numBits_eq]
    obtain h | h := System.Platform.numBits_eq <;> rw [h] <;> ring_nf
    all_goals calc ↑y * 2 ^ ↑6 * 5 + ↑x * 2 ^ ↑6 
       _ ≤ 5 * 2 ^ ↑6 * 5 + ↑x * 2 ^ ↑6  := by sorry
       _ ≤ 5 * 2 ^ ↑6 * 5 + 5 * 2 ^ ↑6  := by sorry
       _ ≤ _ := by native_decide
  let* ⟨ i5, i5_post ⟩ ← Aeneas.Std.Usize.add_spec
  · simp [*, sha3.simple.W.spec, Std.Usize.max]
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
  · simp [*, sha3.simple.W.spec, Std.Usize.max]
  rw [Spec.Keccak.StateArray.get]

  simp [*, Spec.Keccak.StateArray.encodeIndex]
  -- TODO: These are some ugly `conv`s
  conv => arg 2; arg 2; arg 1; arg 2; rw [Nat.mod_eq_of_lt x_idx]; arg 1; arg 2; rw [Nat.mod_eq_of_lt y_idx]
  conv => arg 2; arg 2; arg 2; rw [Nat.mod_eq_of_lt z_idx]
  simp [sha3.simple.W.spec ]
  have self_length: self.val.length = 1600 := by simp
  simp [List.getElem?_eq_getElem (self_length ▸ this)]

@[progress]
theorem Aeneas.Std.UScalar.cast.spec{src_ty : Std.UScalarTy} (tgt_ty : Std.UScalarTy) (x : Std.UScalar src_ty) :
  ∃ y, Std.toResult (Std.UScalar.cast tgt_ty x) = Std.Result.ok y ∧ y.val = (x: Nat) % 2 ^ tgt_ty.numBits
:= by /- {{{ -/
  simp [Std.toResult, cast]
  rw [UScalar.val, BitVec.toNat_setWidth, bv_toNat]

@[progress]
theorem Aeneas.Std.UScalar.hcast.spec{src_ty : Std.UScalarTy} (tgt_ty : Std.IScalarTy) (x : Std.UScalar src_ty) :
  ∃ y, Std.toResult (Std.UScalar.hcast tgt_ty x) = Std.Result.ok y ∧ y.val = (x: Int).bmod (2 ^ tgt_ty.numBits)
:= by 
  simp [Std.toResult, hcast]
  rw [IScalar.val, BitVec.toInt_setWidth, bv_toNat]

#check Progress.liftThm

def Fin.packing_right (x: Fin n) (y: Fin m) : Fin (n*m) :=
  let val := n*y + x
  have val_lt: val < n * m := by
    have n_pos: n > 0 := by apply Nat.pos_of_ne_zero; intro h; simp [h] at x; cases x; contradiction
    have m_pos: m > 0 := by apply Nat.pos_of_ne_zero; intro h; simp [h] at y; cases y; contradiction
    calc val
      _ = n * y + x := rfl
      _ ≤ n * (m-1) + x := by
        apply Nat.add_le_add_right 
        apply Nat.mul_le_mul_left
        apply Nat.le_pred_iff_lt m_pos |>.mpr
        exact y.isLt
      _ ≤ n * (m-1) + (n-1) := by
        apply Nat.add_le_add_left
        apply Nat.le_pred_iff_lt n_pos |>.mpr
        exact x.isLt
      _ < n * m := by 
        simp [Nat.mul_sub, ←Nat.add_sub_assoc n_pos]
        have: n*m >= n := by 
          conv => arg 2; rw [←Nat.mul_one n]
          apply Nat.mul_le_mul (Nat.le_refl n) m_pos
        simp [Nat.sub_add_cancel this]
        exact And.intro n_pos m_pos

  ⟨val, val_lt⟩

def Fin.packing_left (x: Fin n) (y: Fin m) : Fin (n*m) := Nat.mul_comm m n ▸ y.packing_right x

-- TODO: Have some nice syntax where ⟪x,y,z⟫ = z.packing_right (y.packing_right x) = z.max * (y.max * x + y) + z

@[progress]
theorem sha3.simple.StateArray.index_mut.spec
  (self : simple.StateArray)(x y: Std.U8)(z: Std.Usize)
(x_idx: x.val < 5)
(y_idx: y.val < 5)
(z_idx: z.val < Spec.w 6)
: ∃ val upd, self.index_mut (x,y,z) = .ok (val, upd) ∧ 
    val = self.toSpec.get x.val y.val z.val ∧
    ∀ b, (upd b).toSpec = self.toSpec.set x.val y.val z.val b
:= by 
  rw [index_mut]
  let* ⟨ i, i_post ⟩ ← Aeneas.Std.UScalar.cast.spec
  let* ⟨ i1, i1_post ⟩ ← Aeneas.Std.Usize.mul_spec
  · sorry
  let* ⟨ i2, i2_post ⟩ ← Aeneas.Std.UScalar.cast.spec
  let* ⟨ i3, i3_post ⟩ ← Aeneas.Std.Usize.add_spec
  · sorry
  let* ⟨ i4, i4_post ⟩ ← Aeneas.Std.Usize.mul_spec
  · sorry
  let* ⟨ i5, i5_post ⟩ ← Aeneas.Std.Usize.add_spec
  · sorry
  let* ⟨ aux, aux_post ⟩ ← Aeneas.Std.Array.index_mut_usize_spec
  · sorry
  skip

theorem Bool.xor_eq_ne(a b: Bool): (a ^^ b) = (a != b) := by cases a <;> cases b <;> decide

@[progress]
theorem sha3.simple.theta.theta_c.spec(input : sha3.simple.StateArray)(x: Std.U8)(z: Std.Usize)
(x_idx: x.val < 5)
(z_idx: z.val < Spec.w 6)
: ∃ output, theta_c input x z = .ok output ∧ output = Spec.Keccak.θ.C input.toSpec x z
:= by
  rw [theta_c]
  progress*
  simp [*, Spec.Keccak.θ.C]


@[progress]
theorem sha3.simple.theta.theta_d.spec(input : sha3.simple.StateArray)(x: Std.U8)(z: Std.Usize)
(x_idx: x.val < 5)
(z_idx: z.val < Spec.w 6)
: ∃ output, theta_d input x z = .ok output ∧ output = Spec.Keccak.θ.D input.toSpec x z
:= by
  rw [theta_d]
  let* ⟨ i, i_post ⟩ ← Aeneas.Std.UScalar.hcast.progress_spec
  let* ⟨ i1, i1_post ⟩ ← Aeneas.Std.I8.sub_spec
  · have: i.val >= 0 := by 
      sorry
    scalar_tac
  let* ⟨ i2, i2_post ⟩ ← sha3.simple.rem_euclid_i8.spec
  let* ⟨ x1, x1_post ⟩ ← Aeneas.Std.IScalar.hcast.progress_spec
  let* ⟨ i3, i3_post ⟩ ← Aeneas.Std.U8.add_spec
  let* ⟨ x2, x2_post ⟩ ← Aeneas.Std.U8.rem_spec
  let* ⟨ i4, i4_post ⟩ ← Aeneas.Std.UScalar.hcast.progress_spec
  let* ⟨ i5, i5_post ⟩ ← Aeneas.Std.Isize.sub_spec
  · have: i4.val >= 0 := by 
      sorry
    scalar_tac
  let* ⟨ i6, i6_post ⟩ ← Aeneas.Std.UScalar.hcast.progress_spec
  let* ⟨ i7, i7_post ⟩ ← sha3.simple.rem_euclid_isize.spec
  · simp [i6_post]
    rw [Std.UScalar.hcast]
    simp
    #check Std.UScalar.cast_val_eq
    sorry
  let* ⟨ z2, z2_post ⟩ ← Aeneas.Std.IScalar.hcast.progress_spec
  simp [Spec.Keccak.θ.D]
  let* ⟨ b, b_post ⟩ ← sha3.simple.theta.theta_c.spec
  · sorry
  let* ⟨ b1, b1_post ⟩ ← sha3.simple.theta.theta_c.spec
  · sorry
  let* ⟨ res, res_post ⟩ ← sha3.simple.binxor.spec
  simp [*, Std.IScalar.hcast]

  sorry


@[progress]
theorem sha3.simple.theta.theta_apply_a_inner.spec(input acc: sha3.simple.StateArray)(x y: Std.U8)(z: Std.Usize)
(x_idx: x.val < 5)
(y_idx: y.val < 5)
(z_idx: z.val < Spec.w 6)
: ∃ output, simple.theta.theta_apply_a_inner.theta_apply_a_inner2_loop input acc x y z = .ok output ∧ True -- TODO
:= by
  rw [simple.theta.theta_apply_a_inner.theta_apply_a_inner2_loop]
  split
  case isTrue z_idx =>
    let* ⟨ b, b_post ⟩ ← sha3.simple.StateArray.index.spec
    let* ⟨ b1, b1_post ⟩ ← sha3.simple.theta.theta_d.spec
    let* ⟨ b2, b2_post ⟩ ← sha3.simple.binxor.spec
    skip
    skip
  case isFalse z_end =>
    simp
    sorry

@[progress]
theorem sha3.simple.theta.theta_apply_a_inner.spec(input acc: sha3.simple.StateArray)(x y: Std.U8)
: ∃ output, theta.theta_apply_a_inner_loop input acc x y = .ok output ∧ True -- TODO
:= by
  rw [theta.theta_apply_a_inner_loop]
  progress
  sorry

@[progress]
theorem sha3.simple.theta_loop.spec(input acc: sha3.simple.StateArray)(i: Std.U8)
: ∃ output, theta_loop input acc i = .ok output ∧ True -- TODO
:= by
  rw [theta_loop]
  simp [theta.theta_apply_a_inner]
  progress
  sorry

@[progress]
theorem sha3.simple.theta.spec(input: sha3.simple.StateArray)
: ∃ output, theta input = .ok output ∧ output.toSpec = Spec.Keccak.θ input.toSpec
:= by 
  rw [theta]
  simp
  sorry

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
