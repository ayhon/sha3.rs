import Aeneas
import Shars.BitVec
import Shars.Definitions.Simple
import Sha3.Spec
/- import Sha3.Utils -/
import Aeneas.SimpLists.Init
import Sha3.Facts
import Init.Data.Vector.Lemmas
import Init.Data.Nat.Basic
import Shars.Verification.Simple.Utils
import Shars.Verification.Simple.Auxiliary

set_option maxHeartbeats 1000000
attribute [-simp] List.getElem!_eq_getElem?_getD
attribute [simp] Aeneas.Std.Slice.set

open Aeneas hiding Std.Array
open Std.alloc.vec

def Spec.Keccak.ρ.sequence_point(n: Nat): Fin 5 × Fin 5 := n.repeat (fun (x,y) => (y, 2 * x + 3 * y)) (1, 0)

def Spec.Keccak.ρ.sequence := Vector.range 24 |>.map sequence_point


@[progress]
theorem simple.rho_offset.spec (t : Std.Usize)
: t.val < 24
→ ∃ output,
  rho_offset t = .ok output ∧
  output.val = (@Spec.Keccak.ρ.offset 6 t.val).val
:= by
  intro bounded
  unfold rho_offset Spec.Keccak.ρ.offset
  progress* by scalar_tac
  · calc i.val * i1.val
    _ ≤ 24 * i1.val := by
      apply Nat.mul_le_mul_right
      scalar_tac
    _ ≤ 24 * 25 := by
      apply Nat.mul_le_mul_left
      scalar_tac
    _ ≤ Std.Usize.max := by scalar_tac
  simp [*]

def Spec.Keccak.ρ.inner_loop(input res: Spec.Keccak.StateArray 6)(t: Fin 24)(x y: Fin 5)(z: Nat) := Id.run do
  let mut res' := res
  for z in List.finRange (Spec.w 6) |>.drop z do
    res' := res'.set x y z.val <| input.get x y (z - Spec.Keccak.ρ.offset t)
  return res'

def Spec.Keccak.ρ.loop(input res: Spec.Keccak.StateArray 6)(t : Nat)(x y: Fin 5) := Id.run do
  let mut (x',y') := (x,y)
  let mut res' := res
  for t in List.finRange 24 |>.drop t do
    res' := ρ.inner_loop input res' t x' y' 0
    (x',y') := (y', 2*x' + 3*y')
  return res'

theorem Spec.Keccak.ρ.loop.spec(input: Spec.Keccak.StateArray 6)
: ρ.loop input input 0 1 0 = ρ input
:= by simp [ρ,ρ.loop, ρ.inner_loop]

-- example(x: Nat)(x_lt: x < n)(eq: n = m): Fin.cast eq ⟨x, x_lt⟩ = ⟨x, eq ▸ x_lt⟩ := by
--   rfl

@[progress]
theorem simple.rho.inner_loop.spec(input res : StateArray) (t x y z : Std.Usize)
: t.val < 24
→ x.val < 5
→ y.val < 5
→ z.val ≤ Spec.w 6
→ ∃ output,
  rho.inner_loop res input t x y z = .ok output ∧
  output.toSpec = Spec.Keccak.ρ.inner_loop input.toSpec res.toSpec t.val.cast x.val.cast y.val.cast z.val.cast
:= by
  intro t_lt x_lt y_lt z_lt
  rw [rho.inner_loop, Spec.Keccak.ρ.inner_loop]
  split
  . let* ⟨ i, i_post ⟩ ← rho_offset.spec
    let* ⟨ i1, i1_post ⟩ ← Std.Usize.sub_spec'
    let* ⟨ i2, i2_post ⟩ ← Std.Usize.add_spec
    let* ⟨ z2, z2_post ⟩ ← Std.Usize.rem_spec
    let* ⟨ b, b_post ⟩ ← StateArray.index.spec
    let* ⟨ x_1, x_2, x_post_1, x_post_2 ⟩ ← StateArray.index_mut.spec
    let* ⟨ z1, z1_post ⟩ ← Std.Usize.add_spec
    let* ⟨ res, res_post ⟩ ← spec

    simp [*, Spec.Keccak.ρ.inner_loop, Nat.mod_eq_of_lt]
    simp_lists [List.drop_eq_getElem_cons]
    -- simp [Fin.cast_of_mk]
    congr 3
    zmodify
    ring
  case isFalse =>
    simp [‹z.val = Spec.w 6›']
    simp_lists
termination_by Spec.w 6 - z.val
decreasing_by scalar_decr_tac

@[progress]
theorem simple.rho_loop.spec(input: simple.StateArray)
(x y : Std.Usize) (res: simple.StateArray) (t: Std.Usize)
: t.val <= 24
→ x.val < 5
→ y.val < 5
→ ∃ output,
  rho_loop input x y res t = .ok output ∧
  output.toSpec = Spec.Keccak.ρ.loop input.toSpec res.toSpec t.val.cast x.val.cast y.val.cast
:= by
  intro t_loop_bnd x_idx y_idx
  rw [rho_loop]
  split
  case isTrue t_lt =>
    let* ⟨ res1, res1_post ⟩ ← rho.inner_loop.spec
    let* ⟨ i, i_post ⟩ ← Std.Usize.mul_spec
    let* ⟨ i1, i1_post ⟩ ← Std.Usize.mul_spec
    let* ⟨ i2, i2_post ⟩ ← Std.Usize.add_spec
    let* ⟨ lhs, lhs_post ⟩ ← Std.Usize.rem_spec
    let* ⟨ t1, t1_post ⟩ ← Std.Usize.add_spec
    let* ⟨ rest, rest_post ⟩ ← spec input

    simp [*, Spec.Keccak.ρ.loop]
    simp_lists [List.drop_eq_getElem_cons]
    congr 4
    zmodify [Fin.val_ofNat]
  case isFalse =>
    simp [‹t.val = 24›', Spec.Keccak.ρ.loop]
termination_by 24 - t.val
decreasing_by scalar_decr_tac

@[progress]
theorem simple.rho.spec(input: simple.StateArray)
: ∃ output,
  simple.rho input = .ok output ∧ output.toSpec = Spec.Keccak.ρ input.toSpec
:= by
  /- rw [Spec.Keccak.ρ.loop] -/
  simp [rho, ClonesimpleStateArray.clone]
  progress as ⟨res, res_post⟩
  simp [res_post, Spec.Keccak.ρ.loop.spec]
