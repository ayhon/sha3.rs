import Sha3.Utils
import Aeneas
/- def BitVec.toArray(bv: BitVec n): Array Bool := Array.finRange n |>.map (bv[·]) -/
/- def BitVec.ofFn(f: Fin n → Bool): BitVec n := (BitVec.ofBoolListLE <| List.ofFn f).cast (List.length_ofFn f) -/
/- def BitVec.set(i: Fin n)(b: Bool)(bv: BitVec n): BitVec n := bv ^^^ (((bv[i] ^^ b).toNat : BitVec n) <<< i.val) -/

/- def BitVec.toByteArray(bv: BitVec n): ByteArray := -/
/-   let paddedLen := (n + 7)/8 -/
/-   let bv' := bv.setWidth (paddedLen*8) -/
/-   ByteArray.mk <| Array.finRange paddedLen -/
/-     |>.map fun i => -/
/-       let x := List.finRange 8 |>.map (fun o => -/
/-         2^o.val * if bv'[8*i.val+o.val]'(by omega) then 1 else 0 -/
/-       ) |>.sum -/
/-       UInt8.ofNat x -/


@[simp] theorem BitVec.getElem!_ofBoolListLE{ls: List Bool}{i: Nat}
: (BitVec.ofBoolListLE ls)[i]! = ls[i]!
:= by
  if i_idx: i < ls.length then
    repeat rw [getElem!_pos (h := by simpa using i_idx)]
    apply BitVec.getElem_ofBoolListLE
  else
    repeat rw [getElem!_neg (h := by simpa using i_idx)]

theorem BitVec.cast_pivot{bv: BitVec n}{bv2: BitVec m}{eq: n = m}
: bv.cast eq = bv2 ↔ bv = bv2.cast eq.symm
:= by
  apply Iff.intro
  case mp =>
    intro _
    have: (bv.cast eq).cast eq.symm = bv2.cast eq.symm := by congr
    simpa using this
  case mpr =>
    intro _
    have: bv.cast eq = (bv2.cast eq.symm).cast eq := by congr
    simpa using this

theorem BitVec.cast_left{bv: BitVec n}{bv2: BitVec m}(eq: n = m)
: bv.cast eq = bv2 → bv = bv2.cast eq.symm
:= by apply BitVec.cast_pivot.mp

theorem BitVec.cast_right{bv: BitVec n}{bv2: BitVec m}(eq: m = n)
: bv = bv2.cast eq → bv.cast eq.symm = bv2
:= by apply BitVec.cast_pivot.mpr

@[simp] theorem BitVec.getElem!_cast (h : w = v) (x : BitVec w)(i: Nat) : (x.cast h)[i]! = x[i]! := by
  subst h; simp

@[simp]
theorem BitVec.length_toList(bv: BitVec n)
: bv.toList.length = n
:= by simp [toList]

@[simp]
theorem BitVec.ofBoolListLE_set(ls: List Bool)(i: Nat)(b: Bool)
: {i_idx: i < ls.length}
→ BitVec.ofBoolListLE (ls.set i b) = ((BitVec.ofBoolListLE ls).set ⟨i, i_idx⟩ b).cast (by simp)
:= by
  intro i_idx
  ext j j_idx
  simp at j_idx
  simp [BitVec.getElem_set]
  split <;> simp [*]

def BitVec.set!{n: Nat}(i: Nat)(b: Bool)(bv: BitVec n): BitVec n :=
  if _: i < n then
    bv.set ⟨i, ‹i < n›⟩ b
  else bv

theorem BitVec.set!_eq_set{n: Nat}(i: Nat)(b: Bool)(bv: BitVec n)⦃i_idx: i < n⦄
: bv.set! i b = bv.set ⟨i, i_idx⟩ b
:= by simp only [set!, reduceDIte, i_idx]
