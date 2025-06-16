import Mathlib


-- import Mathlib.Data.Nat.Init
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

@[simp] theorem Nat.mul_sub_successive(a b: Nat)
: a * (b + 1) - a * b = a
:= by simp only [Nat.mul_add, Nat.mul_one, Nat.add_sub_cancel_left]

theorem Nat.add_mul_mod_mul{m x y r: Nat}
: 0 < r → y < m → (m*x + y) % (m*r) = m * (x % r) + y
:= by
  intro r_pos y_lt
  have m_pos: 0 < m := by omega
  rw [Nat.add_mod]
  rw [Nat.mul_mod_mul_left]
  rw [Nat.mod_eq_of_lt (show y < m * r from by
    induction r
    case zero => simp at *
    case succ n' ih => simp [Nat.mul_add]; omega
  )]
  rw [Nat.mod_eq_of_lt]
  calc
    _ ≤ m * (r - 1) + y := by simp; apply Nat.mul_le_mul_left; simp [r_pos, Nat.mod_lt, le_sub_one_of_lt]
    _ < m * (r - 1) + m := by simp [y_lt]
    _ = m * r := by simp [Nat.mul_sub]; rw [Nat.sub_add_cancel]; apply le_mul_of_le_of_one_le _ r_pos; simp
