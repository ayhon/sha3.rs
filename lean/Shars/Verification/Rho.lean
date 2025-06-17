import Aeneas
import Shars.BitVec
import Shars.Definitions.Algos
import Sha3.Spec
import Aeneas.SimpLists.Init
import Sha3.Facts
import Init.Data.Vector.Lemmas
import Init.Data.Nat.Basic
import Shars.Verification.Utils
import Shars.Verification.Auxiliary

set_option maxHeartbeats 1000000
attribute [-simp] List.getElem!_eq_getElem?_getD Aeneas.Std.UScalarTy.U64_numBits_eq
attribute [ext (iff := false)] List.ext_getElem!

open Aeneas hiding Std.Array
open Std.alloc.vec


-- TODO: Move this elsewhere
instance[Inhabited T]: Inhabited (Aeneas.Std.Array T n) where default := ⟨List.replicate n.val default, by simp⟩

@[scalar_tac_simps]
def Spec.Keccak.ρ.sequence: Array (Fin 5 × Fin 5) := #[(1,0), (0,2), (2,1), (1,2), (2,3), (3,3), (3,0), (0,1), (1,3), (3,1), (1,4), (4,4), (4,0), (0,3), (3,4), (4,3), (3,2), (2,2), (2,0), (0,4), (4,2), (2,4), (4,1), (1,1)]
@[simp] theorem Spec.Keccak.ρ.size_sequence: ρ.sequence.size = 24 := by simp [sequence]

@[simp] def Spec.Keccak.ρ.sequence.step(t: Nat)
  (t_succ_idx: t + 1 < 24)
: let (x,y) := sequence[t]!
  let (x', y') := sequence[t+1]!
  x'.val = y.val ∧ y'.val = (2*x + 3*y).val
:= by simp [Nat.add_lt_iff_lt_sub_right] at t_succ_idx;
      revert t; native_decide

theorem algos.RHO_OFFSETS.spec'(t: Fin 24)
: let (x,y) := Spec.Keccak.ρ.sequence[t]!
  algos.RHO_OFFSETS.val[x]!.val[y]!.val = Spec.Keccak.ρ.offset (l:= 6) t.val
:= by revert t; native_decide

theorem algos.RHO_OFFSETS.spec(t x y: Nat)
  (t_idx: t < 24)
: Spec.Keccak.ρ.sequence[t]!.1.val = x
→ Spec.Keccak.ρ.sequence[t]!.2.val = y
→ algos.RHO_OFFSETS.val[x]!.val[y]!.val = Spec.Keccak.ρ.offset (l:= 6) t
:= by
  intro x_val y_val
  have:= algos.RHO_OFFSETS.spec' ⟨t, t_idx⟩
  simpa [*] using this


def IR.rho.bitmangling(state res: List Bool)(x y offset: Nat)(z_start: Nat := 0): List Bool := Id.run do
  let mut res := res
  for z in [z_start:Spec.w 6] do
    res := res.set (IR.encodeIndex x y z) <| state[IR.encodeIndex x y ((z + Spec.w 6 - offset % Spec.w 6) % Spec.w 6)]!
  return res

theorem IR.rho.length_bitmangling(state res: List Bool)(x y offset: Nat)
: (bitmangling state res x y offset).length = res.length
:= by
  simp [bitmangling]
  generalize List.range' 0 (Spec.w 6) = ls
  induction ls generalizing res
  case nil => simp
  case cons hd tl ih => simp [ih]

theorem IR.rho.getElem!_bitmangling_pos.aux(state res: List Bool)(x y offset: Nat)(i: Nat)(len: Nat)
  (x_lt: x < 5)
  (y_lt: y < 5)
  (i_lt: i < len)
  (encoded_lt_res: encodeIndex x y i < res.length)
  (encoded_lt_state: encodeIndex x y i < state.length)
: (List.foldl (fun b a => b.set (encodeIndex x y a) state[encodeIndex x y ((a + Spec.w 6 - offset % Spec.w 6) % Spec.w 6)]!) res
      (List.range' 0 len))[encodeIndex x y i]! =
  state[encodeIndex x y ((i + Spec.w 6 - offset % Spec.w 6) % Spec.w 6)]!
:= by
  cases len
  case zero => simp at i_lt
  case succ len' =>
    simp [List.range'_concat]
    if cond: len' = i then
      simp [cond]
      rw [List.getElem!_set]
      simp [List.length_fold_set, *]
    else
      simp [cond, List.getElem!_set_ne]
      rw [IR.rho.getElem!_bitmangling_pos.aux (len := len')]
      all_goals (first | assumption | omega)


theorem IR.rho.getElem!_bitmangling_pos(state res: List Bool)(x y offset: Nat)(i: Nat)
  (x_lt: x < 5)
  (y_lt: y < 5)
  (i_lt: i < Spec.w 6)
  (len_state: state.length = Spec.b 6)
  (len_res: res.length = Spec.b 6)
: (bitmangling state res x y offset)[IR.encodeIndex x y i]! = state[IR.encodeIndex x y ((i +  Spec.w 6 - offset % Spec.w 6) % Spec.w 6)]!
:= by
  have encoded_idx: IR.encodeIndex x y i < res.length := by
    simp [encodeIndex, len_res]
    scalar_tac
  have encoded_idx: IR.encodeIndex x y i < state.length := by
    simp [encodeIndex, len_state]
    scalar_tac
  simp [bitmangling]
  rw [IR.rho.getElem!_bitmangling_pos.aux (len := Spec.w 6)]
  all_goals assumption

theorem IR.rho.getElem!_bitmangling_neg.aux(state res: List Bool)(x y offset: Nat)(i: Nat)(len: Nat)
  (x_lt: x < 5)
  (y_lt: y < 5)
  (x'_lt: x' < 5)
  (y'_lt: y' < 5)
  (i_lt: i < Spec.w 6)
  (len_lt: len ≤ Spec.w 6)
  (encoded_lt_res: encodeIndex x y i < res.length)
  (encoded_lt_state: encodeIndex x y i < state.length)
  (ineq: ¬ (x' = x ∧ y' = y))
: (List.foldl (fun b a => b.set (encodeIndex x y a) state[encodeIndex x y ((a + Spec.w 6 - offset % Spec.w 6) % Spec.w 6)]!) res
      (List.range' 0 len))[encodeIndex x' y' i]! =
  res[encodeIndex x' y' i]!
:= by
  cases len
  case zero => simp [*]
  case succ len' =>
    simp [List.range'_concat]
    have: encodeIndex x y len' ≠ encodeIndex x' y' i := by
      apply IR.encode_eq_encode_iff_eq x x' y y' len' i x_lt y_lt (by omega) x'_lt y'_lt (by omega) |>.not.mpr
      intro; simp at *; omega
    rw [List.getElem!_set_neg]
    case a => simp [this]
    rw [aux]
    all_goals (first | assumption | omega)

theorem IR.rho.getElem!_bitmangling_neg(state res: List Bool)(x x' y y' offset: Nat)(i: Nat)
  (x_lt: x < 5)
  (y_lt: y < 5)
  (x'_lt: x' < 5)
  (y'_lt: y' < 5)
  (i_lt: i < Spec.w 6)
  (len_state: state.length = Spec.b 6)
  (len_res: res.length = Spec.b 6)
: ¬ (x' = x ∧ y' = y) → (bitmangling state res x y offset)[IR.encodeIndex x' y' i]! = res[encodeIndex x' y' i]!
:= by
  intro neq
  have encoded_idx: IR.encodeIndex x y i < res.length := by
    simp [encodeIndex, len_res]
    scalar_tac
  have encoded_idx: IR.encodeIndex x y i < state.length := by
    simp [encodeIndex, len_state]
    scalar_tac
  simp [bitmangling]
  rw [IR.rho.getElem!_bitmangling_neg.aux (len := Spec.w 6)]
  all_goals (first | assumption | simp)

def IR.rho.loop(state res: List Bool)(offset: Nat := 0)(x_init: Nat := 1)(y_init: Nat := 0): List Bool := Id.run do
  let mut (x, y) := (x_init, y_init)
  let mut res := res
  for t in [offset:24] do
    res := bitmangling state res x y (@Spec.Keccak.ρ.offset 6 t)
    (x, y) := (y, (2*x + 3*y) % 5)
  return res

set_option linter.unusedTactic false in -- Prevent the `done` tactic from producing warnings. I like to use it
                                        -- in (first | ... | ...) tacticals to check whether simp closed the goal.
theorem algos.rho.bitmangling.spec(input state: List Std.U64)(x' y': Nat)(offset: Std.U32)(x y z: Nat)
  (x'_lt: x' < 5)
  (y'_lt: y' < 5)
  (x_lt: x < 5)
  (y_lt: y < 5)
  (z_lt: z < Spec.w 6)
  (len_state: state.length = 25)
  (len_res: input.length = 25)
: (state.set (5 * y' + x') (Std.core.num.U64.rotate_left input[5 * y' + x']! offset)).toBits[IR.encodeIndex x y z]!
= (IR.rho.bitmangling input.toBits state.toBits x' y' offset.val)[IR.encodeIndex x y z]!
:= by
  have: 5 * y + x < 25 := Nat.lt_packing_right x_lt y_lt
  if cond: x = x' ∧ y = y' then
    rcases cond with ⟨rfl, rfl⟩
    rw [IR.rho.getElem!_bitmangling_pos]
    all_goals (first | simp [*, List.length_toBits, Spec.b, Spec.w]; done | try scalar_tac)
    have: ((z + Spec.w 6 - ↑offset % Spec.w 6) % Spec.w 6) < Spec.w 6 := by simp [Nat.mod_lt, Spec.w]
    simp [*, List.getElem!_encodeIndex_toBits, Std.core.num.U64.rotate_left]
    simp_lists
    rw [List.toBits_getElem!]; case i_idx => scalar_tac
    simp_lists
    simp +decide [Spec.w]
  else
    rw [IR.rho.getElem!_bitmangling_neg]
    all_goals (first | simp [*, List.length_toBits, Spec.b]; done | try scalar_tac)
    have: 5*y' + x' ≠ 5 * y + x := by omega
    simp [List.getElem!_toBits, IR.encodeIndex_xy, z_lt, this]

@[progress]
theorem algos.rho_loop.spec(input res : StateArray) (x y : Std.Usize) (t: Std.U32)
: t.val <= 24
→ x.val < 5
→ y.val < 5
→ ((h: t.val < 24) → Spec.Keccak.ρ.sequence[t.val]!.1.val = x.val ∧ Spec.Keccak.ρ.sequence[t.val]!.2.val = y.val )
→ ∃ output,
  rho_loop input x y res t = .ok output ∧
  output.toBits = IR.rho.loop input.toBits res.toBits t.val x.val y.val
:= by
  intro t_lt x_lt y_lt sequence_prev
  rw [rho_loop]
  progress*
  · simp [*]
    intro t_succ_idx
    have prev:= sequence_prev (by omega)
    have:= Spec.Keccak.ρ.sequence.step t (by assumption)
    simpa [prev, Fin.eq_of_val_eq, Fin.val_add, Fin.val_mul] using this

  · simp only [*, Std.Array.toBits]
    simp only [IR.rho.loop, Id.run, Fin.isValue, Id.pure_eq, Id.bind_eq,
      Std.Range.forIn_eq_forIn_range', Std.Range.size, List.forIn_yield_eq_foldl]
    simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, Nat.reduceSubDiff]
    simp only [List.range'_advance_left (show 24 - t.val > 0 from by scalar_tac)]
    simp only [Fin.isValue, List.foldl_cons, Fin.val_natCast]
    congr 2
    · have prev:= sequence_prev (by scalar_tac)
      have := algos.RHO_OFFSETS.spec t x y (by scalar_tac) prev.left prev.right
      simp [*]
      apply List.ext_toBits <;> simp [List.length_toBits, IR.rho.length_bitmangling]
      intro x' y' z'
      simp [algos.rho.bitmangling.spec, *]
    · congr 1; omega
  case isFalse =>
    simp [IR.rho.loop, ‹t.val = 24›']
termination_by 24 - t.val
decreasing_by scalar_decr_tac

theorem IR.rho.bitmangling.step(state res: List Bool)(x y offset: Nat)(z: Nat)
: bitmangling state res x y offset z =
  if z < Spec.w 6 then
    let res := res.set (IR.encodeIndex x y z) <| state[IR.encodeIndex x y ((z + Spec.w 6 - offset % Spec.w 6) % Spec.w 6)]!
    bitmangling state res x y offset (z + 1)
  else res
:= by
  simp [bitmangling]
  if cond: z < Spec.w 6 then
    simp [cond, List.range'_advance_left, Nat.sub_add_eq]
  else
    simp [cond, not_lt.mp cond, Nat.sub_eq_zero_of_le]

def Spec.Keccak.ρ.loop.inner(A A': StateArray l)(x y : Fin 5)(t: Fin 24)(z: Nat := 0): StateArray l := Id.run do
  let mut A' := A'
  for z in List.finRange (w l) |>.drop z do
    A' := A'.set x y z <| A.get x y (z - ρ.offset t)
  return A'

theorem Spec.Keccak.ρ.loop.inner.step(A A': Spec.Keccak.StateArray 6)(x y : Fin 5)(t: Fin 24)(z: Nat)
: Spec.Keccak.ρ.loop.inner A A' x y t z =
    if z < Spec.w 6 then
      let A' := A'.set x y z <| A.get x y (z.cast - ρ.offset t)
      Spec.Keccak.ρ.loop.inner A A' x y t (z + 1)
    else
      A'
:= by
  simp [inner]
  if cond: z < Spec.w 6 then
    simp [cond, ←List.cons_getElem_drop_succ, Fin.natCast_def, Nat.mod_eq_of_lt]
  else
    simp [cond, not_lt.mp]

theorem IR.rho.bitmangling.refinement'(A A': Spec.Keccak.StateArray 6)(x y : Fin 5)(t: Fin 24)(z: Nat)
: (Spec.Keccak.ρ.loop.inner A A' x y t z).toBits = IR.rho.bitmangling A.toBits A'.toBits x.val y.val (@Spec.Keccak.ρ.offset 6 t) z
:= by
  rw [bitmangling.step, Spec.Keccak.ρ.loop.inner.step]
  split
  · simp [*]
    rw [IR.rho.bitmangling.refinement']
    congr
    -- TODO: This should be a theorem, toBits_set or something like that.
    simp +arith +decide [Spec.Keccak.StateArray.set, Spec.Keccak.StateArray.get, Spec.Keccak.StateArray.toBits,
      Spec.Keccak.StateArray.encodeIndex, encodeIndex, Nat.mod_eq_of_lt, *, Spec.Keccak.ρ.offset, Fin.val_sub, ←getElem!_pos]
    rw [Nat.add_sub_assoc]
    case h => simp +decide [le_of_lt, Nat.mod_lt]
  · rfl

def Spec.Keccak.ρ.loop(A: StateArray l)(A': StateArray l := A)(x : Fin 5 := 1)(y : Fin 5 := 0)(offset: Nat := 0): StateArray l := Id.run do
  let mut (x, y): Fin 5 × Fin 5 := (x,y)
  let mut A' := A'
  for t in List.finRange 24 |>.drop offset do
    A' := Spec.Keccak.ρ.loop.inner A A' x y t
    (x, y) := (y, 2*x + 3*y)
  return A'

theorem Spec.Keccak.ρ.loop.step(A A': StateArray l)(x y : Fin 5)(t: Nat)
: loop A A' x y t =
    if t < 24 then
      let A' := Spec.Keccak.ρ.loop.inner A A' x y t
      let (x,y) := (y, 2*x + 3*y)
      loop A A' x y (t + 1)
    else
      A'
:= by
  simp [loop]
  if cond: t < 24 then
    simp [cond, ←List.cons_getElem_drop_succ, Fin.natCast_def, Nat.mod_eq_of_lt]
  else
    simp [cond, not_lt.mp]

theorem IR.rho.loop.step(state res: List Bool)(t x y: Nat)
: loop state res t x y =
    if t < 24 then
      let res := bitmangling state res x y (@Spec.Keccak.ρ.offset 6 t)
      let (x, y) := (y, (2*x + 3*y) % 5)
      loop state res (t + 1) x y
    else
      res
:= by
  simp [loop]
  if cond: t < 24 then
    simp +arith [cond, List.range'_advance_left, Nat.sub_right_comm 24 t]
  else
    simp [cond, List.range'_eq_nil_iff.mpr, Nat.sub_eq_zero_of_le, not_lt.mp]

theorem Spec.Keccak.ρ.unfold(A: StateArray l)
: ρ A = ρ.loop A
:= by congr

theorem IR.rho.loop.refinement'(state res: Spec.Keccak.StateArray 6)(x y: Fin 5)(t: Nat)
: (Spec.Keccak.ρ.loop state res x y t).toBits = IR.rho.loop state.toBits res.toBits t x.val y.val
:= by
  /- sorry -/
  rw [Spec.Keccak.ρ.loop.step, IR.rho.loop.step]
  if cond: t < 24 then
    simp only [cond, ↓reduceIte, Fin.isValue]
    rw [IR.rho.loop.refinement']
    simp only [cond, bitmangling.refinement', Nat.mod_eq_of_lt, Fin.val_add, Fin.val_mul, Fin.natCast_def]
    congr 1
    zmodify
  else
    simp [cond]
termination_by 24 - t

@[progress]
theorem algos.rho.spec(input: algos.StateArray)
: ∃ output,
  algos.rho input = .ok output ∧ output.toBits = (Spec.Keccak.ρ input.toSpec).toBits
:= by
  /- rw [Spec.Keccak.ρ.loop] -/
  simp [rho, Spec.Keccak.ρ.unfold]
  progress with rho_loop.spec as ⟨ res, res_post ⟩
  simp +decide [*, IR.rho.loop.refinement', List.toStateArray]
