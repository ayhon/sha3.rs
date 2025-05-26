import Aeneas
import Shars.BitVec
import Shars.Definitions.Algos
import Sha3.Spec
/- import Sha3.Utils -/
import Aeneas.SimpLists.Init
import Sha3.Facts
import Init.Data.Vector.Lemmas
import Init.Data.Nat.Basic
import Shars.Verification.Utils
import Shars.Verification.Auxiliary

set_option maxHeartbeats 1000000
attribute [-simp] List.getElem!_eq_getElem?_getD
attribute [ext (iff := false)] List.ext_getElem!
attribute [simp] Aeneas.Std.Slice.set

open Aeneas hiding Std.Array
open Std.alloc.vec

def Spec.Keccak.ρ.sequence_point(n: Nat): Fin 5 × Fin 5 := n.repeat (fun (x,y) => (y, 2 * x + 3 * y)) (1, 0)

def Spec.Keccak.ρ.sequence := Vector.range 24 |>.map sequence_point

@[progress]
theorem algos.rho.offset.spec (t : Std.U32)
: t.val < 24
→ ∃ output,
  offset t = .ok output ∧
  output.val = (@Spec.Keccak.ρ.offset 6 t.val).val
:= by
  intro bounded
  unfold rho.offset Spec.Keccak.ρ.offset
  progress* by scalar_tac
  · calc i.val * i1.val
    _ ≤ 24 * i1.val := by
      apply Nat.mul_le_mul_right
      scalar_tac
    _ ≤ 24 * 25 := by
      apply Nat.mul_le_mul_left
      scalar_tac
    _ ≤ _ := by scalar_tac
  simp [*, Spec.w]

def Spec.Keccak.ρ.inner_loop(input res: Spec.Keccak.StateArray 6)(t: Fin 24)(x y: Fin 5)(z: Nat) := Id.run do
  let mut res' := res
  for z in List.finRange (Spec.w 6) |>.drop z do
    res' := res'.set x y z.val <| input.get x y (z - Spec.Keccak.ρ.offset t)
  return res'

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

theorem List.range'_advance_left: len > 0 → List.range' start len = start :: List.range' (start + 1) (len - 1) := by 
  intros
  have ⟨n, n_val⟩ := Nat.exists_add_one_eq.mpr ‹len > 0›
  simp only [←n_val]
  rfl

theorem List.range'_advance_right: len > 0 → List.range' start len = List.range' start (len - 1) ++ [start + len - 1] := by 
  intros
  have ⟨n, n_val⟩ := Nat.exists_add_one_eq.mpr ‹len > 0›
  simp only [←n_val, List.range'_concat]
  simp

theorem length_fold_set[Inhabited β](init: List β)(ls: List α)
  (idx_f: α → Nat)
  (value_f: α → β)
: (List.foldl (fun b a => b.set (idx_f a) (value_f a)) (init := init) ls).length = init.length
:= by induction ls generalizing init <;> simp [*]

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
      simp [length_fold_set, *]
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

attribute [-simp] Aeneas.Std.UScalarTy.U64_numBits_eq

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
    simp [List.getElem!_toBits, IR.encodeIndex_xy, IR.encodeIndex_z, *, Std.core.num.U64.rotate_left]
    /- rw [List.getElem!_set]; case h => simp [len_state, *] -/
    /- rw [Aeneas.Std.U64.getElem!_toBits_rotate_left]; case i_idx => simp [Nat.mod_lt, Spec.w] -/
    simp_lists 
    simp only [Nat.mod_eq_of_lt, *]
    simp [Spec.w]
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
→ ∃ output,
  rho_loop input x y res t = .ok output ∧
  output.toBits = IR.rho.loop input.toBits res.toBits t.val x.val y.val
:= by
  intro t_lt x_lt y_lt
  rw [rho_loop]
  progress*
  · simp only [*, Std.Array.toBits]
    simp only [IR.rho.loop, Id.run, Fin.isValue, Id.pure_eq, Id.bind_eq,
      Std.Range.forIn_eq_forIn_range', Std.Range.size, List.forIn_yield_eq_foldl]
    simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, Nat.reduceSubDiff]
    simp only [List.range'_advance_left (show 24 - t.val > 0 from by scalar_tac)]
    simp only [Fin.isValue, List.foldl_cons, Fin.val_natCast]
    congr 2
    · simp [*]
      ext i
      · simp [List.length_toBits, IR.rho.length_bitmangling]
      assume i < Spec.b 6; 
      case otherwise => 
        rw [getElem!_neg]; case h => simp [List.length_toBits, Spec.w]; scalar_tac
        rw [getElem!_neg]; case h => simp [IR.rho.length_bitmangling]; scalar_tac
      have ⟨x', y', z', encode_xyz_def, x'_lt, y'_lt, z'_lt⟩:= IR.decode_surjective i (by assumption)
      rw [←encode_xyz_def, algos.rho.bitmangling.spec]
      all_goals (first | assumption | simp [*])
    · congr 1; omega
  case isFalse =>
    simp [IR.rho.loop, ‹t.val = 24›']
termination_by 24 - t.val
decreasing_by scalar_decr_tac

def Spec.Keccak.ρ.loop.inner(A A': StateArray l)(x y : Fin 5)(t: Fin 24)(z: Nat := 0): StateArray l := Id.run do
  let mut A' := A'
  for z in List.finRange (w l) |>.drop z do
    A' := A'.set x y z <| A.get x y (z - ρ.offset t)
  return A'

/- example(ls: List α)(n: Nat): n < ls.length → ls.drop n = ls[n] :: ls.drop (n + 1) := by exact -/
/-   fun a => List.drop_eq_getElem_cons sorry -/

/- theorem apply_foldl(ls: List α)(init: β)(upd: β → α → β)(f: β → β')⦃g: β' → β⦄ -/
/-   (leftInv: Function.LeftInverse g f) -/
/- : f (ls.foldl upd init) = ls.foldl (fun acc i => f $ upd (g acc) i) (f init) -/
/- := by -/
/-   induction ls using List.reverseRecOn -/
/-   case nil => simp only [List.foldl_nil] -/
/-   case append_singleton preffix last ih => -/
/-     simp only [Function.LeftInverse] at leftInv -/
/-     simp [←ih, leftInv] -/

/- @[simp] -/
/- theorem List.drop_pmap.{u_1, u_2} {α : Type u_1} {β : Type u_2} {P : α → Prop} (f : (a : α) → P a → β) (l : List α) -/
/-   (H : ∀ a ∈ l, P a)(n: Nat) -/
/- : (List.pmap f l H).drop n = List.pmap f (l.drop n) (fun x x_in_drop => H x (List.mem_of_mem_drop x_in_drop)) -/
/- := by ext i : 1; simp -/

/- #check (show ∀ x ∈ List.range' 0 (Spec.w 6), x < Spec.w 6 from by intro x x_in; simpa using x_in) -/
/- #check -- ∀ x ∈ List.range' 0 (Spec.w 6), x < Spec.w 6 -/
/-   List.finRange (Spec.w 6) -/ 
/- #check List.range' 0 (Spec.w 6) |>.pmap Fin.mk (by intro x x_in; simpa using x_in) -/

/- theorem foldl_spec{ι₀ ι₁ α₀ α₁} -/
/-   {ls0: List ι₀}{upd0: α₀ → ι₀ → α₀}{init0: α₀} -/
/-   {ls1: List ι₁}{upd1: α₁ → ι₁ → α₁}{init1: α₁} -/
/-   (inv : α₀ → α₁ → Prop) -/
/-   (idx_rel : ι₀ → ι₁ → Prop) -/
/-   (pre: inv init0 init1) -/
/-   (eq_length: ls0.length = ls1.length) -/
/-   (step: ∀ {i: Nat} (_: i < ls0.length), idx_rel ls0[i] ls1[i] →  ∀ a0 a1, inv a0 a1 → inv (upd0 a0 ls0[i]) (upd1 a1 ls1[i])) -/
/- : inv (ls0.foldl upd0 init0) (ls1.foldl upd1 init1) -/
/- := by -/
/-   sorry -/

/- theorem foldl_range{ls: List ι}{upd: α → ι → α}{init: α} -/
/- : ls.foldl upd init = (List.range' 0 ls.length).attach.foldl (fun a (i: {x // x ∈ List.range' 0 ls.length}) => -/
/-     have: i.val < ls.length := by simpa using i.property -/
/-     upd a ls[i.val]) init -/
/- := by -/ 
/-   sorry -/

/- theorem foldl_finRange{ls: List ι}{upd: α → ι → α}{init: α} -/
/- : ls.foldl upd init = (List.finRange ls.length).foldl (fun a i => upd a ls[i]) init -/
/- := by -/ 
/-   sorry -/

/- theorem foldl_finRange_step{ls: List ι}{upd: α → Fin (ls.length) → α}{init: α}(i: Nat) -/
/- : (List.finRange ls.length |>.drop i).foldl upd = if i < ls.length then (List.finRange ls.length |>.drop (i + 1)).foldl upd -/
/- := by -/ 
/-   sorry -/

/- theorem foldl_step{ls: List ι}{upd: α → ι → α}{init: α} -/
/- : ls.foldl upd init = (List.range' 0 ls.length).attach.foldl (fun a (i: {x // x ∈ List.range' 0 ls.length}) => -/
/-     have: i.val < ls.length := by simpa using i.property -/
/-     upd a ls[i.val]) init -/
/- := by -/ 
/-   sorry -/

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
    simp +arith +decide [Spec.Keccak.StateArray.set, Spec.Keccak.StateArray.get, Spec.Keccak.StateArray.toBits, Spec.Keccak.StateArray.toBitsSubtype,
      Spec.Keccak.StateArray.encodeIndex, encodeIndex, Nat.mod_eq_of_lt, *, Spec.Keccak.ρ.offset, Fin.val_sub, ←getElem!_pos]
    rw [Nat.add_sub_assoc]
    case h => simp +decide [le_of_lt, Nat.mod_lt]
  · rfl

/- theorem IR.rho.bitmangling.refinement(A A': Spec.Keccak.StateArray 6)(x y : Fin 5)(t: Fin 24)(z: Nat) -/
/- : (Spec.Keccak.ρ.loop.inner A A' x y t z).toBits = IR.rho.bitmangling A.toBits A'.toBits x.val y.val (@Spec.Keccak.ρ.offset 6 t) z -/
/- := by -/
/-   simp only [Fin.isValue, Spec.Keccak.ρ.loop.inner, Id.run, Id.pure_eq, Id.bind_eq, -/
/-     List.forIn_yield_eq_foldl, bitmangling, Array.getElem!_toList, Vector.getElem!_toArray, -/
/-     Std.Range.forIn_eq_forIn_range', Std.Range.size, add_tsub_cancel_right, Nat.div_one] -/
/-   /1- have: List.finRange (Spec.w 6) = (List.range' 0 (Spec.w 6)).pmap Fin.mk (by intro x x_in; simpa using x_in) := by simp +decide -1/ -/
/-   /1- rw [this] -1/ -/

/-   generalize upd_def: (fun acc i => -/
/-     (Spec.Keccak.StateArray.set x y i (Spec.Keccak.StateArray.get x y (i - Spec.Keccak.ρ.offset t.val) A) acc)) = upd -/
/-   generalize upd'_def: (fun (b: List Bool) (a: Nat) => -/
/-     b.set (encodeIndex x.val (y.val) a) A.toVector[encodeIndex (x.val) (y.val) ((a + Spec.w 6 - (Spec.Keccak.ρ.offset ↑t).val % Spec.w 6) % Spec.w 6)]!) = upd' -/

/-   rw [apply_foldl (leftInv := Spec.Keccak.StateArray.LeftInverse_toBits)] -/
/-   simp [List.finRange_eq_pmap_range, List.pmap_eq_map, List.foldl_pmap] -/
/-   rw [List.foldl_subtype, List.unattach_attach, List.range_eq_range', List.drop_range', Nat.zero_add] -/
/-   intro st z' z'_in -/
/-   simp only [Fin.isValue, ←upd_def, ←upd'_def] -/
/-   open Spec.Keccak in simp only [StateArray.set, StateArray.get, StateArray.toBits, StateArray.encodeIndex, encodeIndex] -/
/-   unfold List.toStateArray -/
/-   simp [List.range_eq_range', List.drop_range'] at z'_in -/
/-   have: z' < Spec.w 6 := by omega -/
/-   simp [Fin.val_sub, (Spec.Keccak.ρ.offset t.val).isLt, Nat.mod_eq_of_lt] -/
/-   -- TODO: I need to carry the property that the list has length 1600 up to here, somehow -/
/-   split -/
/-   · simp +arith [Nat.add_sub_assoc, (Spec.Keccak.ρ.offset t.val).isLt, le_of_lt, ←getElem!_pos] -/
/-   · sorry -/

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

/- private theorem List.foldl_congr{ls ls': List α} -/
/- : ls = ls' -/
/- → upd = upd' -/
/- → init = init' -/
/- → ls.foldl upd init = ls'.foldl upd' init' -/
/- := by rintro rfl rfl rfl; rfl -/

/- theorem toBits_foldl(ls: List α)(init: Spec.Keccak.StateArray 6)(upd: _) -/
/- : let upd' (acc: {ls: List Bool // ls.length = 1600})(i: α):= { val := (upd (acc.val.toStateArray (by simp)) i).toBits, property := by simp +decide} -/
/-   let init': {ls: List Bool // ls.length = 1600} := { -/
/-     val := init.toBits -/
/-     property := by simp +decide -/
/-   } -/
/-   (ls.foldl upd init).toBits = -/ 
/-   ls.foldl  (fun acc i => upd' acc i) init' -/
/- := by -/
/-   sorry -/

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
  simp +decide [*, IR.rho.loop.refinement', List.toBits_toStateArray]
  
