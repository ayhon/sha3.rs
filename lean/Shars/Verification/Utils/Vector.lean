import Sha3.Spec
import Shars.Verification.Utils.List

theorem Vector.append_cast(b1: Vector α n)(b2: Vector α m)
  (h1: n = n')(h2: m = m')
: b1.cast h1 ++ b2.cast h2 = (b1 ++ b2).cast (show n + m = n' + m' from by simp [h1, h2])
:= by ext i i_idx; by_cases i < n <;> simp [h1 ▸ i_idx, *, Vector.getElem_append]

theorem Vector.append_cast_left(b1: Vector α n)(b2: Vector α m)
  (h: n = n')
: b1.cast h ++ b2 = (b1 ++ b2).cast (show n + m = n' + m from by simp [h])
:= by rw [←Vector.cast_rfl (n := m) (xs := b2)]; apply Vector.append_cast

theorem Vector.append_cast_right(b1: Vector α n)(b2: Vector α m)
  (h: m = m')
: b1 ++ b2.cast h = (b1 ++ b2).cast (show n + m = n + m' from by simp [h])
:= by rw [←Vector.cast_rfl (n := n) (xs := b1)]; apply Vector.append_cast

@[simp] theorem Vector.getElem!_mk {xs : Array α}[Inhabited α] {size : xs.size = n} {i : Nat} :
    (Vector.mk xs size)[i]! = xs[i]! := by
    if h : i < n then
      simp only [getElem!_pos, h, size, Vector.getElem_mk]
    else
      simp only [not_false_eq_true, getElem!_neg, h, size]

@[simp]
theorem Vector.toList_setWidth[Inhabited α](v: Vector α n)(m: Nat)
: (v.setWidth m).toList = v.toList.setWidth m
:= by simp [Vector.setWidth, List.setWidth]
