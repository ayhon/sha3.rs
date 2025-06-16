import Aeneas

-- TODO: Move to somewhere more useful
@[simp] theorem Aeneas.Std.UScalar.numBits_pos(ty: Std.UScalarTy): ty.numBits > 0 := by cases ty <;> simp
