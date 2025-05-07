/- import Sha3.Utils -/
import Aeneas
import Aeneas.SimpLists.Init

set_option maxHeartbeats 100000

/- theorem and_imp_of_ite{cond: Prop}[Decidable cond]: (if cond then P else Q) = ((cond → P) ∧ ((¬ cond) → Q)) := by split <;> simp [*] -/

attribute [simp] Id.run Id.pure_eq Id.bind_eq
attribute [-simp] List.getElem!_eq_getElem?_getD
attribute [simp] Aeneas.Std.Slice.set
/- attribute [simp] Aeneas.Std.Slice.set -/

attribute [simp_lists_simps] lt_inf_iff le_inf_iff true_and and_true not_lt not_le
attribute [simp_lists_simps] List.drop_eq_nil_of_le List.forIn_yield_eq_foldl List.foldl_nil
attribute [simp_lists_simps] List.getElem_finRange List.foldl_cons
attribute [simp_lists_simps] List.getElem?_set_eq


attribute [simp_lists_simps] List.length_append List.take_append_eq_append_take List.take_zipWith List.length_zipWith List.length_take
attribute [simp_lists_simps] List.take_of_length_le List.length_drop List.drop_eq_nil_of_le List.drop_append_eq_append_drop
attribute [simp_lists_simps] List.nil_append List.zipWith_nil_left List.append_nil List.drop_drop List.take_take

attribute [simp_lists_simps] List.getElem!_drop

attribute [simp_lists_simps] List.getElem!_append_left List.getElem!_append_right

attribute [simp_lists_simps] Nat.min_eq_left
attribute [simp_lists_simps] Nat.min_eq_right
attribute [simp_lists_simps] getElem!_neg

attribute [simp_lists_simps] List.length_replicate List.getElem!_replicate

attribute [simp_lists_simps] List.length_map List.length_finRange


attribute [simp_lists_simps] List.append_left_eq_self List.replicate_eq_nil_iff

attribute [simp_lists_simps] List.take_append_drop
