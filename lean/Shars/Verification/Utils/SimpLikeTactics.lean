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

@[zmodify_simps]
theorem Fin.zmod_eq_iff_val_eq {n} : ∀ {i j : Fin n}, i = j ↔ (i.val: ZMod n) = (j.val: ZMod n) := by
  intros i j
  constructor
  · rintro rfl; rfl
  · intro eq
    apply eq_of_val_eq
    have := (ZMod.natCast_eq_natCast_iff' i.val j.val n).mp eq
    simpa only [Nat.mod_eq_of_lt, i.isLt, j.isLt] using this

attribute [zmodify_simps] Fin.val_add Fin.val_mul Fin.val_natCast Fin.val_ofNat
@[zmodify_simps] theorem Fin.val_neg(a: Fin n): (-a).val = (n - a.val) % n := by simp only [Fin.neg_def]
@[zmodify_simps] theorem Fin.val_sub(a b: Fin n): (a - b).val = (n - b.val + a.val) % n := by simp only [Fin.sub_def]
@[zmodify_simps] theorem Fin.val_mod(a b: Fin n): (a % b).val = a.val % b.val := by simp only [Fin.mod_def]


attribute [zmodify_simps] Fin.val_natCast Aeneas.ReduceZMod.reduceZMod ZMod.natCast_mod


attribute [simp_lists_simps] List.flatten_cons -- List.flatten_nil List.flatten_concat List.flatten_append

@[scalar_tac_simps]
theorem Nat.div_sub_self(a b: Nat)
:(a - b) / b = a / b - 1 := by
  by_cases b > 0
  case neg h => simp at h; subst h; simp
  by_cases a >= b
  case pos h =>
    have: a = (a - b) + b := (Nat.sub_eq_iff_eq_add h).mp rfl
    rw [this, Nat.add_sub_cancel, Nat.add_div_right, Nat.add_sub_cancel]
    assumption
  case neg h =>
    simp at h
    simp [Nat.div_eq_of_lt h, Nat.sub_eq_zero_of_le (le_of_lt h)]

@[scalar_tac_simps]
theorem Nat.div_sub_mult_left(a b: Nat)
:(a - b*i) / b = a / b - i := by
  by_cases b > 0
  case neg h => simp at h; subst h; simp
  case pos =>
    cases i
    case zero => simp
    case succ i' =>
      simp [Nat.mul_add, Nat.sub_add_eq, Nat.div_sub_self]
      rw [Nat.div_sub_mult_left]

