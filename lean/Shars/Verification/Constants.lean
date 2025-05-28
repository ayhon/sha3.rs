import Shars.Definitions.Algos

attribute [local simp] Aeneas.Std.eval_global

@[simp, scalar_tac_simps] theorem algos.W.spec': W =   64#usize := by simp [W, W_body]

@[simp, scalar_tac_simps] theorem  algos.SHA3_EXTRA.spec: SHA3_EXTRA  = ⟨0b00000110, by decide⟩ := by simp +decide [SHA3_EXTRA, SHA3_EXTRA_body]
@[simp, scalar_tac_simps] theorem algos.SHAKE_EXTRA.spec: SHAKE_EXTRA = ⟨0b00011111, by decide⟩ := by simp +decide [SHAKE_EXTRA, SHAKE_EXTRA_body]
