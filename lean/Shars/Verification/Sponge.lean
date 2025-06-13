import Aeneas
import Shars.BitVec
import Shars.ArrayExtract
import Shars.Definitions.Algos
import Sha3.Spec
import Aeneas.SimpLists.Init
import Sha3.Facts
import Init.Data.Vector.Lemmas
import Init.Data.Nat.Basic
import Init.Data.Array
import Shars.Verification.Utils
import Shars.Verification.Refinement
import Shars.Verification.Auxiliary
-- import Shars.Verification.ListIR
import Shars.Verification.SpongeAbsorb
import Shars.Verification.SpongeSqueeze

set_option maxHeartbeats 100000
attribute [-simp] List.getElem!_eq_getElem?_getD
attribute [ext (iff:=false)] List.ext_getElem!

open Aeneas

theorem Nat.cast_mod_Int(a b: Nat)
: ((a % b).cast: ℤ) = a.cast % b.cast
:= by simp [Nat.cast]

theorem Spec.«size_pad10*1_of_m_add_2_le_r»(r m: Nat)
: m + 2 ≤ r → (Spec.«pad10*1» r m).size = r - m
:= by
  intro cond
  rw [Spec.«size_pad10*1_eq_ite»]; case a => omega
  simp [Nat.mod_eq_of_lt, ‹m < r›', ‹m ≠ r - 1›']

theorem Nat.le_mul{a b c: Nat}
: 0 < c → a ≤ b → a ≤ b * c
:= by
  intro pos lt
  cases c
  case zero => simp at *
  case succ c' =>
    induction c'
    case zero => simp [*]
    case succ c'' ih =>
      simp [Nat.mul_add] at *
      omega

theorem Nat.add_mul_mod_mul{m x y r: Nat}
: 0 < r → y < m → (m*x + y) % (m*r) = m * (x % r) + y
:= by
  intro r_pos y_lt
  have m_pos: 0 < m := by omega
  rw [Nat.add_mod]
  rw [Nat.mul_mod_mul_left]
  rw [Nat.mod_eq_of_lt (show y < m * r from by
    induction r
    case zero => simp at *
    case succ n' ih => simp [Nat.mul_add]; omega
  )]
  rw [Nat.mod_eq_of_lt]
  calc
    _ ≤ m * (r - 1) + y := by simp; apply Nat.mul_le_mul_left; simp [r_pos, Nat.mod_lt, le_sub_one_of_lt]
    _ < m * (r - 1) + m := by simp [y_lt]
    _ = m * r := by simp [Nat.mul_sub]; rw [Nat.sub_add_cancel]; apply Nat.le_mul r_pos; simp

attribute [scalar_tac_simps] Aeneas.Std.UScalar.length_toBits List.length_setWidth

set_option maxHeartbeats 1000000 in
theorem extra_eq_suffix_append_take_padding(extra: Std.U8)(bs: List Bool)(r: Nat)
  (suffix_len: { i // i < 7 })
  (border_spec: extra.toBits[suffix_len.val]! = true ∧ ∀ j < 8, suffix_len.val < j → extra.toBits[j]! = false)
: 8 ∣ bs.length
→ 8 ∣ r
→ r ≥ 2
→ (extra.toBits.setWidth (r - (bs.length % r) - 1) ++ [true]) =
  (List.take suffix_len.val extra.toBits ++ (Spec.«pad10*1» r (bs.length + suffix_len.val)).toList)
:= by
  intro length_bs_mtpl_8 r_mtpl_8 r_ge_2
  obtain ⟨getElem!_border, getElem!_of_border_lt⟩ := border_spec

  have last_extra_eq_false: extra.toBits[7]! = false := getElem!_of_border_lt 7 (by decide) suffix_len.property
  have r_pos: 0 < r := by omega
  have border_lt_8: suffix_len.val < 8 := by omega
  have: (bs.length + ↑suffix_len) % r = bs.length % r + ↑suffix_len := by
    obtain ⟨r', n'_def⟩ := r_mtpl_8
    have r'_pos: 0 < r' := by omega
    obtain ⟨m', m'_def⟩ := length_bs_mtpl_8
    have := Nat.add_mul_mod_mul (x := m') (y := suffix_len.val) (m := 8) r'_pos border_lt_8
    simp [m'_def, n'_def, this, Nat.mul_mod_mul_left]
  have len_padding: (Spec.«pad10*1» r (bs.length + suffix_len.val)).size = r - (bs.length + suffix_len.val) % r
  · rw [Spec.«size_pad10*1_eq_ite»]; case a => omega
    rw [ite_cond_eq_false]
    obtain ⟨r', rfl⟩ := r_mtpl_8
    obtain ⟨m', m'_def⟩ := length_bs_mtpl_8
    have r'_pos: 0 < r' := by omega
    have := Nat.add_mul_mod_mul (x := m') (y := suffix_len.val) (m := 8) r'_pos border_lt_8
    simp [m'_def, this]
    omega

  -- Function extensionality
  apply List.ext_getElem
  · simp [*, len_padding, le_of_lt]
    scalar_tac
  simp [*, ←getElem!_pos, Nat.sub_add_cancel]
  intro i i_idx i_idx2

  if i < suffix_len then
    -- Suffix part
    simp_lists
    simp_ifs
  else if i = suffix_len then
    -- First true
    simp_lists [getElem!_padding]
    simp_ifs
    simp [*]
  else if h: i = r - (bs.length) % r - 1 then
    -- Last true
    subst h
    simp_lists [getElem!_padding]
    simp_ifs
  else
    -- False paddings
    simp_lists [getElem!_padding]
    simp_ifs
    if cond: i < 8 then -- The padding is included in the `extra` part.
      apply getElem!_of_border_lt i cond (by omega)
    else
      rw [getElem!_neg]; case h => simp; omega
      simp

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

-- set_option diagnostics true in
set_option maxRecDepth 7500 in
set_option maxHeartbeats 1000000 in
@[progress]
theorem algos.sponge.spec(r : Std.Usize) (bs input : Std.Slice Std.U8)(extra: Std.U8)
  -- (suffix_len: Nat)
  -- (suffix_len_lt: suffix_len < 7 := by omega)
  -- (extra_spec: extra.toBits.take suffix_len ++ (Spec.«pad10*1» (8*r) (bs.toBits.length + suffix_len)).toList.take (8 - suffix_len) = extra.toBits)
  -- (last_extra_eq_false: extra.toBits[7]! = false)
  (suffix_len: Nat)
  (suffix_len_lt: suffix_len < 7 := by simp +decide)
  (suffix_len_spec: extra.toBits[suffix_len]! = true ∧ ∀ j < 8, suffix_len < j → extra.toBits[j]! = false)
: (r_pos: 0 < r.val)
→ (r_bnd: r.val < 200)
→ 8 ∣ r.val
→ input.length + r.val < Std.Usize.max
→ ∃ output,
  sponge r bs input extra = .ok output ∧
  output.toBits = (Spec.sponge
    (f := Spec.Keccak.P 6 24)
    (pad := Spec.«pad10*1»)
    (r := ⟨8*r, by simp [*, Spec.b, Spec.w]; omega⟩)
    (bs.toBits ++ extra.toBits.take suffix_len).toArray
    input.toBits.length
   ).toList
:= by
  intros
  simp only [autoParam] at suffix_len_lt suffix_len_spec
  obtain ⟨getElem!_suffix_len, getElem!_of_suffix_len_lt⟩ := suffix_len_spec
  have suffix_len_le_8: suffix_len ≤ 8 := by omega
  have last_extra_eq_false: extra.toBits[7]! = false := getElem!_of_suffix_len_lt 7 (by decide) suffix_len_lt
  unfold sponge sponge_absorb
  simp [DefaultalgosStateArray.default, Std.core.slice.index.Slice.index]
  have: r.val * (bs.val.length / r.val) ≤ bs.length := by scalar_tac
  have: bs.length ≤ Std.Usize.max := bs.property

  progress*? by simp [*, ←Nat.mod_eq_sub, Nat.mod_lt]; try omega
  progress with algos.sponge_squeeze.spec as ⟨res, res_post⟩

  simp [*, Spec.sponge, IR.squeeze.refinement, IR.absorb.refinement (r := 8*r.val)]

  congr
  rw [List.chunks_exact_append]
  congr
  rw [List.chunks_exact_of_length_eq (r_pos := by omega)]
  simp [←Nat.mul_comm 8, Nat.mul_div_mul_left, Nat.mul_assoc, ←Nat.mod_eq_sub]
  have :=  extra_eq_suffix_append_take_padding extra (bs.toBits) (8*r.val) ⟨suffix_len, by omega⟩ ⟨getElem!_suffix_len, getElem!_of_suffix_len_lt⟩ (by simp) (by simp) (by omega)
  simp [*, ←Nat.mul_comm 8, Nat.mul_sub, Nat.mul_mod_mul_left] at this
  rw [this]

  have len_padding: (Spec.«pad10*1» (8*r) (8*bs.length + suffix_len)).size = 8*r - 8 * (bs.length % r) - suffix_len := by
    rw [Spec.«size_pad10*1_eq_ite»]; case a => omega
    have h2 := Nat.add_mul_mod_mul (x := bs.length) (y := suffix_len) (m := 8) (r := r) (by omega) (by omega)
    rw [ite_cond_eq_false]
    · simp [←Nat.mul_comm 8, h2]
      omega
    · simp [←Nat.mul_comm 8, h2]
      omega
  simp [*, ←Nat.mul_comm 8, ←Nat.mul_sub, ←Nat.mul_add, Nat.mul_div_mul_left, Nat.mul_assoc, len_padding, ←Nat.mod_eq_sub]
  scalar_tac

attribute [local simp] Std.Array.make Std.Array.to_slice Std.Array.from_slice Std.Array.length Std.Array.repeat Std.Array.to_slice_mut
attribute [-simp] List.reduceReplicate
attribute [progress] Std.Array.to_slice_mut.spec'
attribute [simp] Fin.val_ofNat
attribute [scalar_tac_simps] Std.Array.to_slice_mut

attribute [local simp] algos.sha3_224 algos.sha3_256 algos.sha3_384 algos.sha3_512 algos.shake128 algos.shake256
attribute [local simp] Spec.SHA3_224 Spec.SHA3_256 Spec.SHA3_384 Spec.SHA3_512 Spec.SHAKE128 Spec.SHAKE256

@[scalar_tac_simps]
theorem Simp.length_toBits_eq(ls: List (Std.UScalar ty))(x: Nat)
: ls.toBits.length = x → ls.length = x / ty.numBits
:= by
  intro eq
  simp [List.length_toBits] at eq
  rw [←eq, Nat.mul_div_left]
  simp only [Std.UScalar.numBits_pos]

section Artifacts

variable (bs: Std.Slice Std.U8)

theorem algos.sha3_224.spec
: ∃ output, algos.sha3_224 bs = .ok output ∧ output.toBits = (Spec.SHA3_224 bs.toBits.toArray).toList
:= by
  simp
  progress with algos.sponge.spec (suffix_len := 2) as ⟨res, res_post⟩
  case suffix_len_spec => simp +decide
  simp +decide [*, Spec.Keccak, Spec.b, Spec.w, List.length_toBits, Simp.length_toBits_eq res.val]
  congr

set_option maxRecDepth 200000 in
theorem algos.sha3_256.spec
: ∃ output, algos.sha3_256 bs = .ok output ∧ output.toBits = (Spec.SHA3_256 bs.toBits.toArray).toList
:= by
  simp
  progress with algos.sponge.spec (suffix_len := 2) as ⟨res, res_post⟩
  case suffix_len_spec => simp +decide
  simp +decide [*, Spec.Keccak, Spec.b, Spec.w, List.length_toBits, Simp.length_toBits_eq res.val]
  congr

set_option maxRecDepth 200000 in
theorem algos.sha3_384.spec
: ∃ output, algos.sha3_384 bs = .ok output ∧ output.toBits = (Spec.SHA3_384 bs.toBits.toArray).toList
:= by
  simp
  progress with algos.sponge.spec (suffix_len := 2) as ⟨res, res_post⟩
  case suffix_len_spec => simp +decide
  simp +decide [*, Spec.Keccak, Spec.b, Spec.w, List.length_toBits, Simp.length_toBits_eq res.val]
  congr

set_option maxRecDepth 1000000 in
theorem algos.sha3_512.spec
: ∃ output, algos.sha3_512 bs = .ok output ∧ output.toBits = (Spec.SHA3_512 bs.toBits.toArray).toList
:= by
  simp
  progress with algos.sponge.spec (suffix_len := 2) as ⟨res, res_post⟩
  case suffix_len_spec => simp +decide
  simp +decide [*, Spec.Keccak, Spec.b, Spec.w, List.length_toBits, Simp.length_toBits_eq res.val]
  congr

theorem algos.shake128.spec (dst: Std.Slice Std.U8)
: dst.length + 168 < Std.Usize.max
→ ∃ output, algos.shake128 bs dst = .ok output ∧ output.toBits = (Spec.SHAKE128 bs.toBits.toArray dst.toBits.length).toList
:= by
  intros; simp
  progress with algos.sponge.spec (suffix_len := 4) as ⟨res, res_post⟩
  case suffix_len_spec => simp +decide
  simp +decide [*, Spec.Keccak, Spec.b, Spec.w, List.length_toBits, Simp.length_toBits_eq res.val, Std.UScalar.toBits]

theorem algos.shake256.spec (dst: Std.Slice Std.U8)
: dst.length + 136 < Std.Usize.max
→ ∃ output, algos.shake256 bs dst = .ok output ∧ output.toBits = (Spec.SHAKE256 bs.toBits.toArray dst.toBits.length).toList
:= by
  intros; simp
  progress with algos.sponge.spec (suffix_len := 4) as ⟨res, res_post⟩
  case suffix_len_spec => simp +decide
  simp +decide [*, Spec.Keccak, Spec.b, Spec.w, List.length_toBits, Simp.length_toBits_eq res.val, Std.UScalar.toBits]

end Artifacts
