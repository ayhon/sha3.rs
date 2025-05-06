import Shars.Definitions.Simple

@[simp, scalar_tac_simps] theorem simple.L.spec: L =    6#usize := by native_decide
@[simp, scalar_tac_simps] theorem simple.W.spec': W =   64#usize := by native_decide
@[simp, scalar_tac_simps] theorem simple.B.spec: B = 1600#usize := by native_decide

attribute [local simp] Aeneas.Std.eval_global

@[simp, scalar_tac_simps] theorem simple.SHA3_SUFFIX.spec: SHA3_SUFFIX = ⟨[false, true], by simp⟩ := by simp [SHA3_SUFFIX, SHA3_SUFFIX_body, Aeneas.Std.Array.make]
@[simp, scalar_tac_simps] theorem simple.SHAKE_SUFFIX.spec: SHAKE_SUFFIX = ⟨[true, true, true, true], by simp⟩ := by simp [SHAKE_SUFFIX, SHAKE_SUFFIX_body, Aeneas.Std.Array.repeat]
