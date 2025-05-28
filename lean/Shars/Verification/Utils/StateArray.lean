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
import Shars.Verification.Utils.BitVec

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
:= by 
  -- TODO: Remove Vector.ofFn' once https://github.com/leanprover/lean4/pull/8499 is included in the used Lean version
  simp [get, ofFn, Vector.ofFn', encode_decode]

@[simp]
theorem List.get_toStateArray(ls: List Bool)
(len_ls: ls.length = Spec.b 6)
: ls.toStateArray.get x y z = ls[Spec.Keccak.StateArray.encodeIndex x y z]!
:= by simp [Spec.Keccak.StateArray.get, List.toStateArray, len_ls]

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

@[simp]
def IR.encodeIndex_spec(x y: Fin 5)(z: Fin (Spec.w 6))
: (Spec.Keccak.StateArray.encodeIndex x y z).val = IR.encodeIndex x y z
:= by rfl

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

theorem List.getElem!_encodeIndex_toBits(ls: List (Aeneas.Std.U64))(x y z: Nat)
  (z_lt: z < Spec.w 6)
: ls.toBits[IR.encodeIndex x y z]! = ls[5*y + x]!.toBits[z]!
:= by simp only [List.getElem!_toBits, IR.encodeIndex_z, IR.encodeIndex_xy, z_lt, Aeneas.Std.UScalarTy.U64_numBits_spec]

abbrev IR.decodeIndex(c: Nat) := (c / Spec.w 6 % 5, c / Spec.w 6 / 5, c % Spec.w 6)

@[simp]
def IR.decodeIndex_encodeIndex(x y: Fin 5)(z: Fin (Spec.w 6))
: (Spec.Keccak.StateArray.decodeIndex (l := 6) ⟨(IR.encodeIndex x y z ), by simp [←IR.encodeIndex_spec] ⟩) = (x,y,z)
:= by simp [←encodeIndex_spec, Spec.Keccak.StateArray.encode_decode]

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
: c < Spec.b 6 → ∃ (x y: Fin 5)(z: Fin (Spec.w 6)), IR.encodeIndex x.val y.val z.val = c
:= by
  intro c_lt
  have:= Spec.Keccak.StateArray.decode_encode ⟨c, c_lt⟩
  simp [Spec.Keccak.StateArray.decodeIndex, Spec.Keccak.StateArray.encodeIndex] at this
  let xyz := Spec.Keccak.StateArray.decodeIndex (l := 6) ⟨c, c_lt⟩
  exists xyz.1, xyz.2.1, xyz.2.2

@[simp] theorem Spec.Keccak.StateArray.getElem!_toVector(state: StateArray l)(i: Fin (Spec.b l))
: state.toVector[i]! = state.get (decodeIndex i).1 (decodeIndex i).2.1 (decodeIndex i).2.2
:= by simp [get, decode_encode', ←getElem!_pos]

@[simp] theorem Spec.Keccak.StateArray.getElem!_toBits(state: StateArray 6)(i: Nat)
 (i_idx: i < Spec.b 6)
: state.toBits[i]! = state.get (decodeIndex ⟨i, i_idx⟩).1 (decodeIndex ⟨i, i_idx⟩).2.1 (decodeIndex ⟨i, i_idx⟩).2.2
:= by simp [-List.getElem!_eq_getElem?_getD, get, Spec.Keccak.StateArray.getElem!_toVector, ←getElem!_pos]

@[simp] theorem Spec.Keccak.StateArray.getElem!_toBits_encodeIndex(state: StateArray 6)
 (x y: Fin 5)(z: Fin (Spec.w 6))
: state.toBits[encodeIndex x y z]! = state.get x y z
:= by simp only [Fin.getElem!_fin,  Array.getElem!_toList, Vector.getElem!_toArray, get, ← getElem!_pos]

/- @[simp] theorem List.get_toStateArray(ls: List Bool)(x y: Fin 5)(z: Fin (Spec.w 6)) -/
/-   (len_ls: ls.length = 1600) -/
/- : ls.toStateArray.get x y z = ls[Spec.Keccak.StateArray.encodeIndex x y z]! -/
/- := by -/
/-   simp +decide [-getElem!_eq_getElem?_getD, Bool.default_bool,toStateArray, len_ls, Spec.Keccak.StateArray.get] -/
/-   rw [←getElem!_pos] -/

@[simp]
theorem Aeneas.Std.UScalar.bv_xor(u1 u2: UScalar ty): (u1 ^^^ u2).bv = u1.bv ^^^ u2.bv := by
  simp only [HXor.hXor, Aeneas.Std.UScalar.xor]

theorem Aeneas.Std.UScalar.getElem!_xor_toBits(u1 u2: UScalar ty)(i: Nat)
: (u1 ^^^ u2).toBits[i]! = (u1.toBits[i]! ^^ u2.toBits[i]!)
:= by
  assume i_idx: i < ty.numBits; case otherwise => simp [getElem!_neg, *]
  simp [toBits, i_idx]

