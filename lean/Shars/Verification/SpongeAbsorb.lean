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
import Shars.Verification.KeccakP

set_option maxHeartbeats 100000
attribute [-simp] List.getElem!_eq_getElem?_getD
attribute [ext (iff := false)] List.ext_getElem!

theorem Spec.«toList_pad10*1»(x m: Nat)
: (Spec.«pad10*1» x m).toList = [true] ++ List.replicate ((Spec.«pad10*1» x m).size - 2) false ++ [true]
:= by simp +arith [Spec.«pad10*1»]

@[simp] theorem Spec.«pos_pad10*1»(x m: Nat)
: (Spec.«pad10*1» x m).size > 0
:= by simp [Spec.«pad10*1»]

theorem getElem!_padding(x m: Nat)(i: Nat)
: (Spec.«pad10*1» x m)[i]! = if i = 0 ∨ i = (Spec.«pad10*1» x m).size - 1 then true else false
:= by
  rw [←Array.getElem!_toList, Spec.«toList_pad10*1»]
  have pos := Spec.«pos_pad10*1» x m
  assume i_idx: i < (Spec.«pad10*1» x m).size; case otherwise =>
    rw [getElem!_neg]
    simp
    omega
    simp [Spec.«pad10*1»]at i_idx ⊢
    scalar_tac
  split
  · rename_i h
    obtain rfl | rfl := h
    · simp
    · simp_lists
      simp +arith
  · simp [Spec.«pad10*1»] at *
    simp_lists

open Aeneas hiding Std.Array
open Std.alloc.vec

def IR.absorb (s: List Bool) (chunks: List (List Bool)): List Bool := Id.run do
  let mut s := s.setWidth (Spec.b 6)
  for Pi in chunks do
    s := IR.keccak_p (IR.xor s Pi)
  return s

set_option maxHeartbeats 1000000 in
@[progress]
theorem algos.sponge_absorb_initial_loop.spec
  (bs : Std.Slice Std.U8) (r : Std.Usize) (s : StateArray) (n i : Std.Usize)
: n.val = bs.length / r.val
→ (r_pos: r.val > 0)
→ i.val ≤ n.val
→ r.val < 200
→ 8 ∣ r.val
→ ∃ output,
  sponge_absorb_initial_loop bs r s n i = .ok output ∧
  output.toBits = IR.absorb s.toBits (bs.toBits.chunks_exact (8*r) |>.drop i)
:= by
  intro n_val r_pos i_idx r_le r_mtpl_8
  unfold sponge_absorb_initial_loop

   -- r * (i + 1) ≤ r * n = r * (bs.length / r) ≤ bs.length            ( ≤ Usize.max )
  have r_range(i_idx: i < n): r.val*i.val + r.val ≤ bs.length := calc r.val * i.val + r.val
      _ ≤ r.val * n := Nat.mul_le_mul_left r.val i_idx
      _ = r.val * (bs.length / r) := by simp [n_val]
      _ ≤ bs.length := Nat.mul_div_le bs.length ↑r

  progress*
  · simp [*, IR.absorb, Nat.mul_add, Spec.Keccak.toList_P]
    simp [*] at chunk_post
    rw [←List.getElem_cons_drop_succ_eq_drop (i := i)]
    swap; { simp +arith [Nat.mul_div_mul_left]; scalar_tac}
    simp +decide [-List.getElem_cons_drop, Std.Array.toBits, List.toStateArray]
    congr
    simp [*, Std.Slice.toBits, ←getElem!_pos,]
    rw [List.getElem!_chunks_exact]; case a => simp +arith [Nat.mul_div_mul_left]; scalar_tac
    simp
    ring_nf

  case isFalse i_oob =>
    have := ‹bs.length / r.val - i.val = 0›'
    simp [IR.absorb, this]
    rw [List.drop_of_length_le ?bnd]; case bnd => simp +arith [Nat.mul_div_mul_left]; scalar_tac
    simp +decide [Std.Array.toBits, List.setWidth_of_length_eq]
termination_by n.val - i.val
decreasing_by scalar_decr_tac

@[progress]
theorem algos.sponge_absorb_initial.spec
  (bs : Std.Slice Std.U8) (r : Std.Usize) (s : StateArray)
: (r_pos: r.val > 0)
→ r.val < 200
→ 8 ∣ r.val
→ ∃ output,
  sponge_absorb_initial bs r s = .ok output ∧
  output.toBits = IR.absorb s.toBits (bs.toBits.chunks_exact (8*r))
:= by intros
      unfold sponge_absorb_initial
      progress*
      simp [*]

def IR.array_absorb.upd (r: Nat) (r_bnd: r < Spec.b 6) (state : Spec.Bitstring (Spec.b 6)) (chunk : Vector Spec.Bit r) :=
   Spec.Keccak.P 6 24 (state ^^^ (chunk ++ Vector.replicate (Spec.b 6 - r) false).cast (by simp [*, le_of_lt]))

def IR.array_absorb(r: Nat)(r_bnd: r < Spec.b 6)(arr: Array (Spec.Bitstring r))
  (init: Spec.Bitstring (Spec.b 6) := Vector.replicate (Spec.b 6) false)(i: Nat := 0)
:= arr.toList.drop i |>.foldl (IR.array_absorb.upd r r_bnd) init

def IR.array_absorb.refinement(r: Nat)(r_pos: r > 0)(r_bnd: r < Spec.b 6)(N: Array Spec.Bit)
: Spec.sponge.absorb (f := Spec.Keccak.P 6 24) (pad := Spec.«pad10*1») (r := ⟨r, ⟨r_pos, r_bnd⟩⟩) N = IR.array_absorb r r_bnd (Array.chunks_exact r (N ++ Spec.«pad10*1» r N.size))
:= by
  unfold Spec.sponge.absorb IR.array_absorb IR.array_absorb.upd
  simp [*, Vector.setWidth, Vector.append_cast_left]

def IR.array_absorb.unfold(r: Nat)(r_bnd: r < Spec.b 6)(arr: Array (Spec.Bitstring r))(i: Nat)
: IR.array_absorb r r_bnd arr init i =
    if i < arr.size then
      let init := IR.array_absorb.upd r r_bnd init arr[i]!
      IR.array_absorb r r_bnd arr init (i + 1)
    else
      init
:= by
  simp [IR.array_absorb]
  by_cases h: i < arr.size
  · simp [*]
    rw [←List.getElem_cons_drop h]
    simp [←getElem!_pos]
  · simp [*, ←getElem!_pos, List.drop_of_length_le, not_lt.mp]

def IR.absorb.loop (s: List Bool) (chunks: List (List Bool))(i: Nat := 0): List Bool := Id.run do
  let mut s := s.setWidth (Spec.b 6)
  for Pi in chunks.drop i do
    s := IR.keccak_p (IR.xor s Pi)
  return s

def IR.absorb.unfold(s: List Bool)(chunks: List (List Bool))
: IR.absorb s chunks = IR.absorb.loop s chunks
:= by simp only [absorb, loop, List.drop_zero]

def IR.absorb.loop.unfold(init: List Bool)(chunks: List (List Bool))(i: Nat)
: IR.absorb.loop init chunks i =
    let init := (init.setWidth (Spec.b 6))
    if i < chunks.length then
      let init := IR.keccak_p (IR.xor init chunks[i]!)
      IR.absorb.loop init chunks (i + 1)
    else
      init
:= by
  simp [loop]
  by_cases h: i < chunks.length
  · simp [*]
    rw [←List.getElem_cons_drop h]
    simp [←getElem!_pos]
  · simp [*, List.drop_of_length_le, not_lt.mp]

private theorem Vector.toList_xor(b1 b2: Vector Bool n)
: (b1 ^^^ b2).toList = IR.xor b1.toList b2.toList
:= by
  apply List.ext_getElem
  · simp
  simp [←getElem!_pos]
  intro i i_idx
  simp [HXor.hXor, Xor.xor, Vector.getElem!_ofFn, i_idx, ←getElem!_pos]
  simp [IR.xor, i_idx, List.getElem!_zipWith]

theorem IR.absorb.refinement'  (r: Nat)(r_pos: r > 0)(r_bnd: 8*r < Spec.b 6)(chunks : Array (Spec.Bitstring (8*r)))(init: Spec.Bitstring (Spec.b 6))(i: Nat)
: (array_absorb (8 * r) r_bnd chunks init i).toList = IR.absorb.loop init.toList (chunks.toList.map (·.toList)) i
:= by
  rw [IR.array_absorb.unfold]
  rw [IR.absorb.loop.unfold]
  simp
  if cond: i < chunks.size then
    simp [cond, IR.array_absorb.upd]
    rw [IR.absorb.refinement' r r_pos r_bnd]
    simp [Spec.Keccak.toList_P]
    simp [Vector.toList_xor]
  else
    simp [cond]

theorem IR.absorb.refinement(r: Nat)
  (r_pos   : r > 0        := by scalar_tac)
  (r_bnd   : r < Spec.b 6 := by scalar_tac)
  (r_mtpl_8: 8 ∣ r        := by scalar_tac)
: (Spec.sponge.absorb (f := Spec.Keccak.P 6 24) (pad := Spec.«pad10*1») (r := ⟨r, ⟨r_pos, r_bnd⟩⟩) N).toList
= IR.absorb (List.replicate (Spec.b 6) false) (List.chunks_exact r (N ++ Spec.«pad10*1» r N.size).toList)
:= by
  rw [IR.array_absorb.refinement (r_pos := r_pos) (r_bnd := r_bnd)]
  obtain ⟨r', rfl⟩ := r_mtpl_8
  rw [IR.absorb.refinement' (r_pos := by omega)]
  rw [IR.absorb.unfold, Array.toList_chunks_exact]
  simp only [Vector.toArray_replicate, Array.toList_replicate, Array.toList_append]

attribute [-simp] Bool.if_false_right Bool.if_false_left Bool.if_true_right Bool.if_true_left IR.xor_append in
set_option maxHeartbeats 1000000 in
@[progress]
theorem algos.sponge_absorb_final.spec
  (input : StateArray) (rest : Std.Slice Std.U8) (extra : Std.U8) (r : Std.Usize)
: r.val ≥ 6
→ r.val ≤ 200
→ rest.length < r
→ extra.toBits[7]! = false
→ ∃ output,
  sponge_absorb_final input rest extra r = .ok output ∧
  output.toBits = IR.absorb input.toBits [rest.toBits ++ (extra.toBits.setWidth (8*r- 8*rest.length - 1)) ++ [true]]
:= by
  intro r_big_enough r_bnd length_rest_lt extra_padding_no_collision
  unfold sponge_absorb_final
  progress*
  simp [*, Std.Array.toBits, IR.absorb, IR.keccak_p]
  congr 3
  apply List.ext_getElem
  · simp +decide
  simp +decide [←getElem!_pos]

  have: 128#u8.toBits = List.replicate 7 false ++ [true] := by decide
  simp only [this, List.replicate_append_replicate, ←List.append_assoc, Nat.mul_sub, ‹8*r.val - 8 + 7 = 8*r.val - 1›']
  /-

  +────────────────────────────────────────────────────────────+
  |                    input                                   |
  +────────────────────────────────────────────────────────────+
                                                               ↑
  +─────────────────+────────────+                             |
  |       rest      |   extra    |                             |
  +─────────────────+────────────+                             |
                                                               |
                    +────────────────────────────+             |
                    |···························1|             |
                    +────────────────────────────+             |
                    ↑                          ↑ ↑             |
                    |                          | |             |
                    rest.length                | r             1600
                                              r-1
  -/
  intro i i_idx
  simp [IR.xor_assoc, IR.getElem!_xor, i_idx]
  rw [(show input.val.toBits[i]! = (input.val.toBits[i]! ^^ false) from by simp)]
  simp only [Bool.xor_assoc]
  rw [←apply_ite (f := (fun (x: Bool) => input.val.toBits[i]! ^^ x))]
  simp only [Bool.false_bne, Bool.bne_right_inj]

  -- TODO: I would like `simp_scalar` to do all of this.
  rw [Nat.sub_add_cancel]; swap; { scalar_tac}
  rw [←Nat.mul_comm 8]
  rw [Nat.sub_add_cancel]; swap; { scalar_tac}
  rw [←Nat.add_sub_assoc]; swap; { scalar_tac}
  simp

  if i < 8*rest.length then
    simp_ifs
    simp_lists
    simp
  else if i < 8*r.val - 1 then
    simp_ifs
    simp_lists
    simp [Std.UScalar.getElem!_toBits, ←Nat.mul_comm 8]
    simp_ifs
  else if i < 8*r.val then
    simp [*, ‹i = 8*r - 1›']
    simp_ifs
    simp_lists
    if rest.length = r - 1 then
      simp [*, Nat.mul_sub, ‹8*r.val - 1 - (8*r.val - 8) = 7›']
    else
      rw [getElem!_neg]; case h => simp [Std.UScalar.length_toBits]; scalar_tac
      simp
  else
    simp_ifs
    simp_lists
    simp

@[simp]
theorem IR.length_absorb_loop(s: List Bool)(bs: List (List Bool))(i: Nat)
: (absorb.loop s bs i).length = Spec.b 6
:= by
  rw [absorb.loop.unfold]
  by_cases i < bs.length <;> simp [*]
  rw [IR.length_absorb_loop]

@[simp]
theorem IR.absorb_absorb(s: List Bool)(bs bs2: List (List Bool))
: absorb (absorb s bs) bs2 = absorb s (bs ++ bs2)
:= by
  simp only [absorb.unfold]
  have len_absorb := IR.length_absorb_loop s bs 0
  simp [absorb.loop] at *
  rw [List.setWidth_of_length_eq]
  simpa using len_absorb

theorem Spec.«size_pad10*1» (x m : Nat)
: x > 0
→ (Spec.«pad10*1» x m).size = (x - (m + 2) % x) % x + 2
:= by
  intro x_pos
  have: ((-m.cast -2) % x.cast).toNat = (x - (m + 2) % x) % x := by
    zify
    simp [Int.emod_nonneg, *, Nat.ne_zero_of_lt x_pos]
    zmodify
    simp
    ring
  simp [Spec.«pad10*1», this]
  simp +arith

theorem Spec.«pad10*1_mod» (x m : Nat)
: (Spec.«pad10*1» x (m % x)) = (Spec.«pad10*1» x m)
:= by simp [«pad10*1»]; congr 4; zmodify

theorem Spec.«size_pad10*1_eq_ite» (x m : Nat)
: x >= 2
→ (Spec.«pad10*1» x m).size = if m%x = x - 1 then 1 + x else x - m % x
:= by
  intro x_gt
  have x_pos: x > 0 := by omega
  rw [←Spec.«pad10*1_mod»]
  generalize m'_def: m % x = m'
  have m'_lt: m' < x := by simp [←m'_def, Nat.mod_lt, x_pos]
  simp [Spec.«size_pad10*1», x_pos]
  split
  · simp +arith [*, ‹1 < x›', le_of_lt, ←Nat.sub_add_comm, Nat.mod_eq_of_lt]
  · if m' = x - 2 then
      simp +arith [*, ‹1 < x›', le_of_lt, ←Nat.sub_add_comm, Nat.mod_eq_of_lt]
      omega
    else
      simp [*, ‹m' + 2 < x›', le_of_lt,  Nat.mod_eq_of_lt, ←Nat.sub_add_comm]

theorem Spec.«size_pad10*1_of_mtpl_8»(r bs_len: Nat)
: r > 0
→ (Spec.«pad10*1» (8*r) (8*bs_len)).size = 8*(r - (bs_len % r))
:= by
  intro r_pos
  rw [←Spec.«pad10*1_mod»]
  generalize r'_def: 8*r = r'
  have: r' > 0 := by omega
  have: r' >= 2 := by omega
  generalize bs_len'_def: (8 * bs_len) % r' = bs_len'
  simp [←r'_def, Nat.mul_mod_mul_left] at bs_len'_def
  have bs_len'_lt: bs_len' < r' := by simp [←r'_def, ←bs_len'_def, Nat.mod_lt, r_pos]

  simp [Spec.«size_pad10*1_eq_ite», this, Nat.mul_mod_mul_right, Nat.mod_eq_of_lt, bs_len'_lt]
  split <;> simp [*, Nat.mul_sub]
  omega
