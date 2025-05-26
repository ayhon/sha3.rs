import Aeneas
import Shars.BitVec
import Shars.Definitions.Algos
import Sha3.Spec
/- import Sha3.Utils -/
import Aeneas.SimpLists.Init
import Sha3.Facts
import Init.Data.Vector.Lemmas
import Init.Data.Nat.Basic
import Shars.Verification.Refinement

-- TODO: Consider moving this out of Utils


@[ext]
theorem Spec.Keccak.StateArray.ext{a b: StateArray l}
{point_eq: ∀ (x y: Fin 5)(z: Fin (w l)), a.get x y z = b.get x y z}
: a = b
:= by
  obtain ⟨a⟩ := a
  obtain ⟨b⟩ := b
  have bv_point_eq: ∀ (c: Fin (Spec.b l)), a[c] = b[c] := by
    simp [get] at point_eq
    intro c
    have := point_eq (decodeIndex c).1 (decodeIndex c).2.1 (decodeIndex c).2.2
    simp [Spec.Keccak.StateArray.decode_encode c] at this
    assumption
  simp
  ext i i_idx
  exact bv_point_eq ⟨i, i_idx⟩

@[simp]
theorem Spec.Keccak.StateArray.get_ofFn{f: Fin 5 × Fin 5 × Fin (w l) → Spec.Bit}(x y: Fin 5)(z: Fin (w l))
: (StateArray.ofFn f).get x y z = f (x,y,z)
:= by simp [ofFn, get, BitVec.ofFn, encode_decode]

theorem Bool.toNat_mod2_self(b: Bool)
: b.toNat % 2 = b.toNat
:= by cases b <;> simp

theorem Spec.Keccak.StateArray.get_set(a: Spec.Keccak.StateArray l)(x x' y y': Fin 5)(z z': Fin (w l))
: (a.set x' y' z' val).get x y z = if x' = x ∧ y' = y ∧ z' = z then val else a.get x y z
:= by
  simp [get, set, Vector.getElem_set]
  split
  case isTrue h =>
    replace h := encode_inj x x' y y' z z' |>.mp <| Fin.eq_of_val_eq h.symm
    simp [h]
  case isFalse h =>
    rw [ite_cond_eq_false]
    simp; rintro rfl rfl rfl; exact h rfl

@[simp]
theorem Spec.Keccak.StateArray.get_set_eq(a: Spec.Keccak.StateArray l)(x y : Fin 5)(z : Fin (w l))
: (a.set x y z val).get x y z = val
:= by simp [get_set]

@[simp]
theorem Spec.Keccak.StateArray.get_set_neq(a: Spec.Keccak.StateArray l)(x x' y y': Fin 5)(z z': Fin (w l))
: (x,y,z) ≠ (x',y',z')
→ (a.set x' y' z' val).get x y z = a.get x y z
:= by
  intros not_cond
  rw [get_set]
  simp [not_cond]; rintro rfl rfl rfl; simp at not_cond

theorem Spec.Keccak.StateArray.get_set_pos(a: Spec.Keccak.StateArray l)(x x' y y': Fin 5)(z z': Fin (w l))
(eq: (x,y,z) = (x',y',z'))
: (a.set x y z val).get x' y' z' = val
:= by simp at eq; simp [eq]


abbrev IR.encodeIndex(x y z: Nat): Nat := Spec.w 6 * (5 * y + x) + z

theorem IR.encodeIndex_z(x y z: Nat)
  (z_lt: z < Spec.w 6)
: IR.encodeIndex x y z % Spec.w 6 = z
:= by simp [IR.encodeIndex, z_lt, Nat.mod_eq_of_lt, *]

theorem IR.encodeIndex_xy(x y z: Nat)
  (z_lt: z < Spec.w 6)
: IR.encodeIndex x y z / Spec.w 6 = 5 * y + x
:= by simp [IR.encodeIndex, Nat.mul_add_div, *]

-- TODO: Decide where to move these theorems.
@[simp] theorem Aeneas.Std.U64.numBits_spec: U64.numBits = Spec.w 6 := by simp +decide [numBits]
@[simp] theorem Aeneas.Std.UScalarTy.U64_numBits_spec: UScalarTy.U64.numBits = Spec.w 6 := by simp +decide [numBits]

@[simp] theorem List.getElem!_encodeIndex_toBits(ls: List (Aeneas.Std.U64))(x y z: Nat)
  (z_lt: z < Spec.w 6)
: ls.toBits[IR.encodeIndex x y z]! = ls[5*y + x]!.toBits[z]!
:= by simp only [List.getElem!_toBits, IR.encodeIndex_z, IR.encodeIndex_xy, z_lt, Aeneas.Std.UScalarTy.U64_numBits_spec]

abbrev IR.decodeIndex(c: Nat) := (c / Spec.w 6 % 5, c / Spec.w 6 / 5, c % Spec.w 6)

theorem IR.decode_encode(x y z: Nat): x < 5 → y < 5 → z < Spec.w 6 → decodeIndex (encodeIndex x y z) = (x, y, z) := by
  intro x_lt y_lt z_lt
  have:= Spec.Keccak.StateArray.encode_decode ⟨x, x_lt⟩ ⟨y, y_lt⟩ ⟨z, z_lt⟩
  simp [Spec.Keccak.StateArray.decodeIndex, Spec.Keccak.StateArray.encodeIndex] at this
  simp [decodeIndex, encodeIndex, this]

@[simp]
theorem IR.encode_eq_encode_iff_eq(x x' y y' z z': Nat)
: x < 5 → y < 5 → z < Spec.w 6
→ x' < 5 → y' < 5 → z' < Spec.w 6
→ (encodeIndex x y z = encodeIndex x' y' z' ↔ (x, y, z) = (x', y', z')) := by
  intros
  apply Iff.intro
  case mp =>
    intro eq
    replace eq := congrArg (f := IR.decodeIndex) eq
    simp only [IR.decode_encode, *] at eq
    simpa using eq
  case mpr =>
    rintro ⟨rfl, rfl, rfl⟩; rfl

theorem IR.encode_decode(c: Nat): c < Spec.b 6 → (encodeIndex (decodeIndex c).1 (decodeIndex c).2.1 (decodeIndex c).2.2) = c := by
  intro c_lt
  have:= Spec.Keccak.StateArray.decode_encode ⟨c, c_lt⟩
  simp [Spec.Keccak.StateArray.decodeIndex, Spec.Keccak.StateArray.encodeIndex] at this
  simp [decodeIndex, encodeIndex, this]

theorem IR.decode_surjective(c: Nat)
: c < Spec.b 6 → ∃ x y z, IR.encodeIndex x y z = c ∧ x < 5 ∧ y < 5 ∧ z < Spec.w 6
:= by
  intro c_lt
  have:= Spec.Keccak.StateArray.decode_encode ⟨c, c_lt⟩
  simp [Spec.Keccak.StateArray.decodeIndex, Spec.Keccak.StateArray.encodeIndex] at this
  let xyz := Spec.Keccak.StateArray.decodeIndex (l := 6) ⟨c, c_lt⟩
  exists xyz.1, xyz.2.1, xyz.2.2
  have := xyz.1.isLt
  have := xyz.2.1.isLt 
  have := xyz.2.2.isLt
  unfold xyz at*
  simp [Spec.Keccak.StateArray.decodeIndex] at *
  simp [Spec.Keccak.StateArray.decodeIndex, encodeIndex, this, xyz, *]
