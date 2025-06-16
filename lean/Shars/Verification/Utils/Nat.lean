import Mathlib.Data.Nat.Init

@[simp] theorem Nat.mul_add_one_sub_mul(a b: Nat): a * (b + 1) - a * b = a := by
  simp [Nat.mul_add, Nat.add_comm]

theorem Nat.div_spec(n q: Nat){d: Nat}
: 0 < d
→ (q = n / d ↔ d * q ≤ n ∧ n < d * (q + 1))
:= by
  intro d_pos
  apply Iff.intro
  · rintro rfl
    simp [Nat.mul_div_le, Nat.lt_mul_div_succ, d_pos]
  · rintro ⟨lb, ub⟩
    apply Nat.le_antisymm
    · have := Nat.div_le_div_right (c := d) lb
      rw [Nat.mul_div_cancel_left _ d_pos] at this
      exact this
    · have := Nat.div_lt_of_lt_mul ub
      have := Nat.le_of_lt_add_one this
      exact this
