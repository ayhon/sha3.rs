import Aeneas
import Shars.BitVec
import Shars.Definitions.Simple
import Sha3.Spec
/- import Sha3.Utils -/
import Aeneas.SimpLists.Init
import Sha3.Facts
import Init.Data.Vector.Lemmas
import Init.Data.Nat.Basic

theorem and_imp_of_ite{cond: Prop}[Decidable cond]: (if cond then P else Q) = ((cond → P) ∧ ((¬ cond) → Q)) := by
  split <;> simp [*]

attribute [simp] Id.run Id.pure_eq Id.bind_eq

attribute [simp_lists_simps] lt_inf_iff le_inf_iff true_and and_true not_lt not_le
attribute [simp_lists_simps] List.drop_eq_nil_of_le List.forIn_yield_eq_foldl List.foldl_nil
attribute [simp_lists_simps] List.getElem_finRange List.foldl_cons
attribute [simp_lists_simps] List.getElem?_set_eq


@[simp_lists_simps]   
theorem getElem!_zipWith[Inhabited α][Inhabited β](f: α → α → β)(xs ys: List α)
: ∀ i < xs.length.min ys.length,
  (xs.zipWith f ys)[i]! = f xs[i]! ys[i]!
:= by
  intro i i_idx
  cases xs <;> cases ys <;> cases i <;> simp at *
  apply getElem!_zipWith
  apply Nat.le_min.mpr
  assumption

