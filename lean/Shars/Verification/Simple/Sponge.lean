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

#check simple.sponge
set_option maxRecDepth 1000000 in
theorem simple.sponge.spec(r : Std.Usize) (bs dst suffix : Std.Slice Bool)
: (r_big_enough: r.val ≥ 6)
→ suffix.length ≤ 4
→ r.val < 1600
→ dst.length > 0
→ dst.length + r.val < Std.Usize.max
→ let _: NeZero r.val := {out:=Nat.not_eq_zero_of_lt r_big_enough}
  ∃ output,
  sponge r bs dst suffix = .ok output ∧
  output.val = (Spec.sponge (f := Spec.Keccak.P 6 24) Spec.«pad10*1» r (bs.val ++ suffix.val).toArray dst.length).toList
:= by
  intros
  rw [sponge]
  progress with simple.sponge_absorb.spec_list as ⟨mid, mid_post⟩
  · simp [Std.Array.repeat]
  progress with simple.sponge_squeeze.spec as ⟨res, post⟩
  simp [*]
  simp [Spec.sponge]
  have := absorb.spec
  simp [spec_sponge_absorb] at this
  rw [ListIR.sponge.squeeze.refinement, this, absorb.refinement]
  simp
  congr 6
  · native_decide
  · unfold Spec.«pad10*1»
    simp
    congr 4
    have(a x: Int): (-(a % x) % x) = - a % x := by
      simp [Int.emod_def]
      sorry
    simp [Nat.cast_mod_Int]
    apply Int.ModEq.eq
    ring
    zmodify
    ring_nf
    rw [neg_sub_comm]
    rw [←Int.emod_sub_emod]
    rw [Int.emod_add_emod]
    rw [Nat.mod_sub_mod]
    rw [Nat.mod_add_mod]
    sorry
  · omega
