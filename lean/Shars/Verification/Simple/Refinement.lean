import Aeneas
import Shars.Definitions.Simple
import Shars.Verification.Simple.Utils
import Sha3.Spec


abbrev List.toBitVec(self: List Bool): BitVec self.length := BitVec.ofBoolListLE self
abbrev Vector.toBitVec(self: Vector Bool n): BitVec n := self.toList.toBitVec.cast (by simp)

/- def Aeneas.Std.Array.toBitVec{size: Std.Usize}(self: Std.Array Bool size): BitVec (size.val) := -/
/-   (BitVec.ofBoolListLE <| self.val).cast (by simp) -/
/- def Aeneas.Std.Slice.toBitVec(self: Aeneas.Std.Slice Bool): BitVec self.length := -/
/-   (BitVec.ofBoolListLE self.val).cast (by simp) -/

def simple.StateArray.toSpec(self: simple.StateArray): Spec.Keccak.StateArray 6 :=
  Spec.Keccak.StateArray.ofBitVec <| self.val.toBitVec.cast (by simp [Spec.w, Spec.b])

/- abbrev Aeneas.Std.Array.toArray{size: Usize}(self: Aeneas.Std.Array α size): _root_.Array α := Array.mk self.val -/
/- abbrev Aeneas.Std.Slice.toArray(self: Aeneas.Std.Slice α): _root_.Array α := Array.mk self.val -/

