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
  (border_spec: extra.toBits[suffix_len.val]! = true ∧ ∀ j, suffix_len.val < j → extra.toBits[j]! = false)
: 8 ∣ bs.length
→ 8 ∣ r
→ r ≥ 2
→ (extra.toBits.setWidth (r - (bs.length % r) - 1) ++ [true]) =
  (List.take suffix_len.val extra.toBits ++ (Spec.«pad10*1» r (bs.length + suffix_len.val)).toList)
:= by
  intro length_bs_mtpl_8 r_mtpl_8 r_ge_2
  obtain ⟨getElem!_border, getElem!_of_border_lt⟩ := border_spec

  have last_extra_eq_false: extra.toBits[7]! = false := getElem!_of_border_lt 7 suffix_len.property
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
    if cond: i ≤ 8 then -- The padding is included in the `extra` part.
      apply getElem!_of_border_lt
      omega
    else
      rw [getElem!_neg]; case h => simp; omega
      simp


-- set_option diagnostics true in
set_option maxRecDepth 7500 in
set_option maxHeartbeats 1000000 in
-- @[progress]
theorem algos.sponge.spec(r : Std.Usize) (bs input : Std.Slice Std.U8)(extra: Std.U8)
  (border: { i // i < 7 })
  (border_spec: extra.toBits[border.val]! = true ∧ ∀ j, border.val < j → extra.toBits[j]! = false)
: (r_pos: 0 < r.val)
→ (r_bnd: r.val < 200)
→ 8 ∣ r.val
→ dst.length + r.val < Std.Usize.max
→ ∃ output,
  sponge r bs dst extra = .ok output ∧
  output.toBits = (Spec.sponge
    (f := Spec.Keccak.P 6 24)
    (pad := Spec.«pad10*1»)
    (r := ⟨8*r, by simp [*, Spec.b, Spec.w]; omega⟩)
    (bs.toBits ++ extra.toBits.take border).toArray
    dst.toBits.length
   ).toList
:= by
  intros
  obtain ⟨getElem!_border, getElem!_of_border_lt⟩ := border_spec
  have border_le_8: border.val ≤ 8 := by omega
  have: extra.toBits.take border ++ [true] ++ List.replicate (8 - border - 1) false = extra.toBits := by
    apply List.ext_getElem <;> simp +decide [*, ←getElem!_pos, ‹border.val + (8 - border.val - 1 + 1) = 8›']
    intro i i_lt
    if i < border then
      rw [List.getElem!_append_left]; case h => simp; omega
      rw [List.getElem!_take_of_lt]; case x => omega
    else if i = border then
      simp [*]
    else
      simp [getElem!_of_border_lt, ‹border < i›']
      rw [List.getElem!_append_right]; case h => simp; omega
      simp [border_le_8]
      obtain ⟨m', m'_val⟩ := Nat.exists_eq_add_one.mpr ‹0 < i - border.val›'
      simp [m'_val]
      rw [List.getElem!_replicate]; case h => omega
  have last_extra_eq_false: extra.toBits[7]! = false := getElem!_of_border_lt 7 border.property
  unfold sponge sponge_absorb
  simp [DefaultalgosStateArray.default, Std.core.slice.index.Slice.index]
  have: r.val * (bs.val.length / r.val) ≤ bs.length := by scalar_tac
  have: bs.length ≤ Std.Usize.max := bs.property

  progress*? by simp [*, ←Nat.mod_eq_sub, Nat.mod_lt]; try omega
  progress with algos.sponge_squeeze.spec as ⟨res, res_post⟩

  simp [*, Spec.sponge, IR.squeeze.refinement]

  -- TODO: Make this nicer, IR.absorb.refinement should be enough
  rw [IR.array_absorb.refinement]
  case r_pos => omega
  case r_bnd => simp [Spec.b, Spec.w]; omega
  rw [IR.absorb.refinement, IR.absorb.unfold]
  case r_pos => omega

  simp [*, Array.toList_chunks_exact, List.append_assoc]
  congr
  rw [←Nat.mod_eq_sub]
  conv =>
    rhs
    rw [←List.chunks_exact_split _ (8*r.val) (bs.toBits.length / (8*r.val))]
    lhs
    rw [List.take_append_of_le_length (h := by simp [←Nat.mul_comm 8, Nat.mul_div_mul_left, Nat.mul_assoc, Nat.mul_div_le])]
  rw [List.chunks_exact_truncate]
  congr
  rw [List.drop_append_of_le_length (h := by simp [←Nat.mul_comm 8, Nat.mul_div_mul_left, Nat.mul_assoc, Nat.mul_div_le])]

  -- TODO: This should probably be its own theorem
  unfold List.chunks_exact
  rw [ite_cond_eq_false]
  case h =>
    -- TODO(Son): Think about this thingy here
    simp
    simp [←Nat.mul_comm 8, ←Nat.mod_eq_sub, *]
    simp [*, ←Nat.mul_comm 8, Nat.mul_div_mul_left, Nat.mul_assoc, Nat.mul_div_le, ←Nat.mul_sub, ←Nat.mod_eq_sub]
    sorry

  unfold List.chunks_exact
  rw [ite_cond_eq_true]
  case h =>
    simp [*, ←Nat.mul_comm 8, Nat.mul_div_mul_left, Nat.mul_assoc, Nat.mul_div_le, ←Nat.mul_sub, ←Nat.mod_eq_sub]
    sorry
  simp [*, ←Nat.mul_comm 8, Nat.mul_div_mul_left, Nat.mul_assoc, Nat.mul_div_le, ←Nat.mul_sub, ←Nat.mod_eq_sub]
  rw [List.take_of_length_le (h := by simp [*, ←Nat.mul_comm 8, ←Nat.mul_sub, ←Nat.mod_eq_sub]; sorry)]
  have: 8 * (r.val - bs.length % r.val) ≥ 8 := by
    simp
    change 0 < r.val - bs.length % r.val
    simp [Nat.mod_lt, *]

  -- TODO: Look into `olet` and `tlet`
  congr 1
  apply List.ext_getElem
  · simp [*]
    sorry
  simp [*, ←getElem!_pos]
  intro i i_idx i_idx2
  simp

  sorry

  -- progress with algos.sponge_absorb.spec_list as ⟨mid, mid_post⟩
  -- · simp [Std.Array.repeat]
  -- progress with algos.sponge_squeeze.spec as ⟨res, post⟩
  -- simp [*]
  -- simp [Spec.sponge]
  -- have absorb_spec := absorb.spec
  -- simp [spec_sponge_absorb] at absorb_spec
  -- rw [ListIR.sponge.squeeze.refinement, absorb_spec, absorb.refinement]
  -- case r_pos => scalar_tac
  -- simp
  -- congr 6
  -- unfold Spec.«pad10*1»
  -- simp
  -- congr 2
  -- ext i i_lhs i_rhs
  -- · simp [BitVec.toNat]
  --   congr 1
  --   -- apply Int.ModEq.eq
  --   ring_nf
  --   rw [←Int.add_emod_emod]
  --   rw [Int.sub_emod_emod]
  --   rw [Int.add_emod_emod]
  -- simp [BitVec.toArray]


attribute [local simp] Std.Array.make Std.Array.to_slice Std.Array.from_slice Std.Array.length Std.Array.repeat
attribute [-simp] List.reduceReplicate
-- attribute [-progress] Std.Array.to_slice_mut.spec
-- attribute [progress] Std.Array.to_slice_mut.spec'

attribute [simp] Fin.val_ofNat

theorem algos.sha3_224.spec (bs: Std.Slice Bool)
: ∃ output, algos.sha3_224 bs = .ok output ∧ output.val = (Spec.SHA3_224 (Array.mk bs.val)).toList
:= by rw [sha3_224]; progress*; simp [*]; congr <;> simp [*]

theorem algos.sha3_256.spec (bs: Std.Slice Bool)
: ∃ output, algos.sha3_256 bs = .ok output ∧ output.val = (Spec.SHA3_256 (Array.mk bs.val)).toList
:= by rw [sha3_256]; progress*; simp [*]; congr <;> simp [*]

theorem algos.sha3_384.spec (bs: Std.Slice Bool)
: ∃ output, algos.sha3_384 bs = .ok output ∧ output.val = (Spec.SHA3_384 (Array.mk bs.val)).toList
:= by rw [sha3_384]; progress*; simp [*]; congr <;> simp [*]

set_option maxRecDepth 1000000 in
theorem algos.sha3_512.spec (bs: Std.Slice Bool)
: ∃ output, algos.sha3_512 bs = .ok output ∧ output.val = (Spec.SHA3_512 (Array.mk bs.val)).toList
:= by rw [sha3_512]; progress*; simp [*]; congr <;> simp [*]

theorem algos.shake128.spec (bs dst: Std.Slice Bool)
: dst.length + (1600 - 256) < Std.Usize.max
→ ∃ output, algos.shake128 bs dst = .ok output ∧ output.val = (Spec.SHAKE128 (Array.mk bs.val) dst.length).toList
:= by intros; rw [shake128]; progress*; simp [*]; congr; simp

theorem algos.shake256.spec (bs dst: Std.Slice Bool)
: dst.length + (1600 - 512) < Std.Usize.max
→ ∃ output, algos.shake256 bs dst = .ok output ∧ output.val = (Spec.SHAKE256 (Array.mk bs.val) dst.length).toList
:= by intros; rw [shake256]; progress*; simp [*]; congr; simp
