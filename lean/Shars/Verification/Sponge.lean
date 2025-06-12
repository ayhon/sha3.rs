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
