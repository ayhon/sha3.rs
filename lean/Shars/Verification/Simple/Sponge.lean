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
import Shars.Verification.Simple.ListIR
import Shars.Verification.Simple.SpongeAbsorb
import Shars.Verification.Simple.SpongeSqueeze

set_option maxHeartbeats 100000
attribute [-simp] List.getElem!_eq_getElem?_getD
attribute [ext (iff:=false)] List.ext_getElem!

open Aeneas

theorem Nat.cast_mod_Int(a b: Nat)
: ((a % b).cast: ℤ) = a.cast % b.cast
:= by simp [Nat.cast]

set_option maxRecDepth 1000000 in
@[progress]
theorem simple.sponge.spec(r : Std.Usize) (bs dst suffix : Std.Slice Bool)
: (r_big_enough: r.val ≥ 6)
→ suffix.length ≤ 4
→ r.val < 1600
-- → dst.length > 0
→ dst.length + r.val < Std.Usize.max
→ ∃ output,
  sponge r bs dst suffix = .ok output ∧
  have: NeZero r.val := {out:=Nat.ne_zero_of_lt r_big_enough}
  output.val = (Spec.sponge (f := Spec.Keccak.P 6 24) Spec.«pad10*1» r (bs.val ++ suffix.val).toArray dst.length).toList
:= by
  intros
  rw [sponge]
  have: NeZero r.val := {out:=Nat.ne_zero_of_lt (by assumption)}
  progress with simple.sponge_absorb.spec_list as ⟨mid, mid_post⟩
  · simp [Std.Array.repeat]
  progress with simple.sponge_squeeze.spec as ⟨res, post⟩
  simp [*]
  simp [Spec.sponge]
  have absorb_spec := absorb.spec
  simp [spec_sponge_absorb] at absorb_spec
  rw [ListIR.sponge.squeeze.refinement, absorb_spec, absorb.refinement]
  simp
  congr 6
  · unfold Spec.«pad10*1»
    simp
    congr 2
    ext i i_lhs i_rhs
    · simp [BitVec.toNat]
      congr 1
      -- apply Int.ModEq.eq
      ring_nf
      rw [←Int.add_emod_emod]
      rw [Int.sub_emod_emod]
      rw [Int.add_emod_emod]
    simp [BitVec.toArray]
  · omega


attribute [local simp] Std.Array.make Std.Array.to_slice Std.Array.from_slice Std.Array.length Std.Array.repeat
attribute [-simp] List.reduceReplicate
-- attribute [-progress] Std.Array.to_slice_mut.spec
-- attribute [progress] Std.Array.to_slice_mut.spec'

attribute [simp] Fin.val_ofNat

theorem simple.sha3_224.spec (bs: Std.Slice Bool)
: ∃ output, simple.sha3_224 bs = .ok output ∧ output.val = (Spec.SHA3_224 (Array.mk bs.val)).toList
:= by rw [sha3_224]; progress*; simp [*]; congr <;> simp [*]

theorem simple.sha3_256.spec (bs: Std.Slice Bool)
: ∃ output, simple.sha3_256 bs = .ok output ∧ output.val = (Spec.SHA3_256 (Array.mk bs.val)).toList
:= by rw [sha3_256]; progress*; simp [*]; congr <;> simp [*]

theorem simple.sha3_384.spec (bs: Std.Slice Bool)
: ∃ output, simple.sha3_384 bs = .ok output ∧ output.val = (Spec.SHA3_384 (Array.mk bs.val)).toList
:= by rw [sha3_384]; progress*; simp [*]; congr <;> simp [*]

set_option maxRecDepth 1000000 in
theorem simple.sha3_512.spec (bs: Std.Slice Bool)
: ∃ output, simple.sha3_512 bs = .ok output ∧ output.val = (Spec.SHA3_512 (Array.mk bs.val)).toList
:= by rw [sha3_512]; progress*; simp [*]; congr <;> simp [*]

theorem simple.shake128.spec (bs dst: Std.Slice Bool)
: dst.length + (1600 - 256) < Std.Usize.max
→ ∃ output, simple.shake128 bs dst = .ok output ∧ output.val = (Spec.SHAKE128 (Array.mk bs.val) dst.length).toList
:= by intros; rw [shake128]; progress*; simp [*]; congr; simp

theorem simple.shake256.spec (bs dst: Std.Slice Bool)
: dst.length + (1600 - 512) < Std.Usize.max
→ ∃ output, simple.shake256 bs dst = .ok output ∧ output.val = (Spec.SHAKE256 (Array.mk bs.val) dst.length).toList
:= by intros; rw [shake256]; progress*; simp [*]; congr; simp
