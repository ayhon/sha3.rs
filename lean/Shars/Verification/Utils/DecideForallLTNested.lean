import Mathlib

namespace DecideForallLTNested

/- #count_heartbeats in -/
/- example: ∀ j, j < 10 → [0][j]! = 0 := by decide -/
/- #count_heartbeats in -/
/- example: ∀ j, j < 10 → j ∈ List.range 10 := by decide -/

instance move_non_LT_condition_to_conclusion
  (C: Nat → Prop)(P: Nat → Prop)
 [cond: DecidablePred C]:[Decidable (∀ i, P i ∨ (¬ C i) )] → Decidable (∀ i, C i → P i)
 | isTrue h => isTrue <| by
      intro i C_i
      replace h := h i
      simpa [C_i] using h
 | isFalse h => isFalse <| by
      intro neg
      apply h
      intro i
      cases cond i <;> simp [*]

instance forall_with_LT_condition_on_left_conjunct
  (C: Nat → Prop)(P: Nat → Prop)(n: Nat)
  [cond: DecidablePred C]: [Decidable (∀ i, i < n → P i ∨ C i)] → Decidable (∀ i, (i < n → P i) ∨ C i)
  | isTrue h => isTrue <| by
        intro i
        match cond i with
        | isTrue h2 =>
          simp [*]
        | isFalse h2 =>
          simp [h2]
          intro lt
          simpa [h2] using h i lt
  | isFalse h => isFalse <| by
        intro neg
        apply h
        intro i lt
        match cond i with
        | isTrue h => simp [*]
        | isFalse h =>
          simpa [h, lt] using neg i

instance pop_non_LT_condition_to_conjunction
  (C P T: Nat → Prop)
  [decC: DecidablePred C][decT: DecidablePred T]
  : [Decidable (∀ i, P i ∨ (C i ∨ (¬ T i)))] → Decidable (∀ i, (T i → P i) ∨ C i)
| isTrue h => isTrue <| by
      intro i
      match decC i with
      | isTrue hC =>
        simp [*]
      | isFalse hC =>
        simp [hC]
        intro hT
        simpa [hC, hT] using h i
| isFalse h => isFalse <| by
      intro neg
      apply h
      intro i
      match decC i with
      | isTrue hC => simp [hC]
      | isFalse hC =>
        simp [hC]
        match decT i with
        | isTrue hT => simpa [hC, hT] using neg i
        | isFalse hT => simp [hT]

/- #count_heartbeats in -/
/- example: ∀ j, j < 10 → [0][j]! = 0 := by decide -/
/- set_option diagnostics true in -/
/- #count_heartbeats in -/
/- example: ∀ j, j < 10 → j ∈ List.range 10 := by decide -/

/- #count_heartbeats in -/
/- example: ∀ (j: Nat), j > 2 → j < 10 → [0,1][j]! = 0 := by decide -/
/- #count_heartbeats in -/
/- example: ∀ (j: Nat), j > 2 → j > 3 → j < 10 → [0,1][j]! = 0 := by decide -/
/- #count_heartbeats in -/
/- example: ∀ (j: Nat), j > 2 → j > 3 → j > 4 → j < 10 → [0,1][j]! = 0 := by decide -/
/- #count_heartbeats in -/
/- example: ∀ (j: Nat), j > 2 → j > 3 → j > 4 → j < 6 → j = 5 := by decide -/
/- #count_heartbeats in -/
/- example: ∀ (j: Nat), j > 2 → j > 3 → j > 4 → j > 5 → j < 7 → j = 6 := by decide -/
/- #count_heartbeats in -/
/- example: ∀ (j: Nat), j > 2 → j > 3 → j > 4 → j > 5 → j > 6 → j < 8 → j = 7 := by decide -/
