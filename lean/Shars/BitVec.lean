import Sha3.Utils
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


@[ext]
theorem BitVec.ext{bv1 bv2: BitVec n}
{point_eq: ∀ i: Nat, (_: i < n) → bv1[i] = bv2[i]}
: bv1 = bv2 
:= by
  obtain ⟨⟨a, a_lt⟩⟩ := bv1
  obtain ⟨⟨b, b_lt⟩⟩ := bv2
  simp 
  simp [BitVec.getElem_eq_testBit_toNat] at point_eq
  apply Nat.eq_of_testBit_eq
  intro i
  if h: i < n then
    exact point_eq i h
  else
    have: a < 2 ^i := calc
      a < 2 ^n := a_lt
      _ ≤ 2 ^i := Nat.pow_le_pow_of_le Nat.one_lt_two (Nat.le_of_not_gt h)
    simp [Nat.testBit_lt_two_pow this]
    have: b < 2 ^i := calc
      b < 2 ^n := b_lt
      _ ≤ 2 ^i := Nat.pow_le_pow_of_le Nat.one_lt_two (Nat.le_of_not_gt h)
    simp [Nat.testBit_lt_two_pow this]


theorem BitVec.getElem_set{bv: BitVec n}{b: Bool}{i: Fin n}{j: Nat}
:  {j_lt: j < n}
→ (bv.set i b)[j] = if i = j then b else bv[j]
:= by 
  intro j_lt
  have n_pos: n > 0 := by cases n <;> (first | cases i.isLt | apply Nat.zero_lt_succ )

  rw [set]
  split
  case isTrue h => 
    subst h
    simp [Nat.testBit, BitVec.getLsbD]
    cases bv[i] <;> cases b <;> simp [n_pos]
  case isFalse =>
    simp
    if h: j < i then
      simp [h]
    else
      have: j > i := by omega
      simp [this, h]
      cases bv[i] <;> cases b <;> simp [n_pos, (by simp; omega: decide (j - i = 0) = false)]

@[simp] theorem BitVec.cast_set(h: n = m)(bv: BitVec n)(i: Nat)(b: Bool)(i_idx: i < n)
: (bv.set ⟨i, i_idx⟩ b).cast h = (bv.cast h).set ⟨i, h ▸ i_idx⟩ b
:= by subst h; ext; rw [cast_eq, cast_eq]

@[simp] theorem BitVec.getElem_ofBoolListLE{ls: List Bool}{i: Nat}
: ∀ (h: i < ls.length), (BitVec.ofBoolListLE ls)[i] = ls[i]
:= by
  let rec odd_div(x: Nat): (2*x + 1) / 2 = x := by
    cases x 
    case zero => simp only [Nat.mul_zero, Nat.zero_add, Nat.reduceDiv]
    case succ => 
      rw [Nat.mul_add, Nat.add_assoc, Nat.add_comm _ 1, ←Nat.add_assoc]
      rw [Nat.add_div_right (H := Nat.two_pos), Nat.add_right_cancel_iff, Nat.add_comm]
      apply odd_div
  intro i_lt
  cases ls
  case nil => contradiction
  case cons hd tl =>
    simp [BitVec.ofBoolListLE, BitVec.getElem_eq_testBit_toNat]
    cases i
    case zero => simp [Nat.mod_eq_of_lt (Bool.toNat_lt hd)]
    case succ i' => 
      have: ((ofBoolListLE tl).toNat * 2 + hd.toNat).testBit (i' + 1) = (ofBoolListLE tl).toNat.testBit i' := by 
        cases hd <;> simp [Nat.testBit_succ]; rw [Nat.mul_comm, odd_div]
      simp [this] at i_lt ⊢
      rw [←BitVec.getElem_eq_testBit_toNat (ofBoolListLE tl) i']
      apply BitVec.getElem_ofBoolListLE i_lt

@[simp] theorem BitVec.getElem!_ofBoolListLE{ls: List Bool}{i: Nat}
: (BitVec.ofBoolListLE ls)[i]! = ls[i]!
:= by 
  if i_idx: i < ls.length then
    repeat rw [getElem!_pos (h := by simpa using i_idx)]
    apply BitVec.getElem_ofBoolListLE
  else
    repeat rw [getElem!_neg (h := by simpa using i_idx)]


@[simp] theorem BitVec.getElem_ofFn(f: Fin n → Bool)(i: Nat){i_idx: i < n}
: (BitVec.ofFn f)[i] = f ⟨i, i_idx⟩
:= by simp [ofFn]

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
