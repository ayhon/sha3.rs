import Aeneas
import Shars.Definitions.Algos
import Sha3.Spec
import Shars.Verification.Utils.List


/- def Aeneas.Std.Array.toBitVec{size: Std.Usize}(self: Std.Array Bool size): BitVec (size.val) := -/
/-   (BitVec.ofBoolListLE <| self.val).cast (by simp) -/
/- def Aeneas.Std.Slice.toBitVec(self: Aeneas.Std.Slice Bool): BitVec self.length := -/
/-   (BitVec.ofBoolListLE self.val).cast (by simp) -/

def Aeneas.Std.UScalar.toBits(u: Aeneas.Std.UScalar ty): List Bool := List.ofFn (u.bv[·])
@[simp] theorem Aeneas.Std.UScalar.length_toBits(u: Aeneas.Std.UScalar ty): u.toBits.length = ty.numBits := by
  simp only [toBits, Fin.getElem_fin, List.length_ofFn]

def List.toBits(ls: List (Aeneas.Std.UScalar ty)): List Bool := ls.map (·.toBits) |>.flatten
def List.length_toBits(ls: List (Aeneas.Std.UScalar ty))
: ls.toBits.length = ls.length * ty.numBits
:= by
  rw [toBits]
  have: ∀ xs ∈ (ls.map (·.toBits)), xs.length = ty.numBits := by simp
  rw [List.length_flatten_of_uniform this]
  simp [toBits, Nat.mul_comm]

def Aeneas.Std.Array.toBits(arr: Aeneas.Std.Array (Aeneas.Std.UScalar ty) n): List Bool := arr.val.toBits
@[simp] def Aeneas.Std.Array.length_toBits(arr: Aeneas.Std.Array (Aeneas.Std.UScalar ty) n)
: arr.toBits.length = n * ty.numBits
:= by simp only [toBits, List.length_toBits, arr.property]

def Aeneas.Std.Slice.toBits(arr: Aeneas.Std.Slice (Aeneas.Std.UScalar ty)): List Bool := arr.val.toBits
@[simp] def Aeneas.Std.Slice.length_toBits(arr: Aeneas.Std.Slice (Aeneas.Std.UScalar ty))
: arr.toBits.length = arr.length * ty.numBits
:= by simp only [toBits, List.length_toBits]

@[reducible, simp]
def algos.StateArray.toSpec(self: algos.StateArray): List Bool := self.toBits

/- abbrev Aeneas.Std.Array.toArray{size: Usize}(self: Aeneas.Std.Array α size): _root_.Array α := Array.mk self.val -/
/- abbrev Aeneas.Std.Slice.toArray(self: Aeneas.Std.Slice α): _root_.Array α := Array.mk self.val -/
