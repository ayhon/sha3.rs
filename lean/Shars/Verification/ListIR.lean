import Sha3.Spec
import Aeneas.ScalarTac
import Aeneas.SimpLists
import Shars.Verification.Refinement
import Shars.Verification.Utils
import Shars.Verification.Utils.SimpLikeTactics

attribute [-simp] List.getElem!_eq_getElem?_getD

def ListIR.xor_long_at(s rest: List Bool)(offset: Nat): List Bool :=
  s.take offset ++ (s.drop offset |>.zipWith (· ^^ ·) rest) ++ s.drop (offset + rest.length)
def ListIR.xor_long(s rest: List Bool): List Bool := xor_long_at s rest 0

theorem ListIR.xor_long.def(s rest: List Bool)
: xor_long s rest = s.zipWith (· ^^ ·) rest ++ s.drop rest.length
:= by simp [xor_long, xor_long_at]

@[simp, scalar_tac_simps]
theorem ListIR.length_xor_long_at(s rest: List Bool)
: (xor_long_at s rest offset).length = s.length
:= by simp [xor_long_at, List.length_zipWith]; omega

def ListIR.list_keccak_p(s: List Bool): List Bool :=
  let state := s.toBitVec.setWidth (Spec.b 6)
  let state := Spec.Keccak.P 6 24 state
  state.toList

@[simp]
theorem ListIR.length_list_keccak_p(ls: List Bool)
: (list_keccak_p ls).length = 1600
:= by simp [list_keccak_p, Spec.b, Spec.w]

def ListIR.absorb' (f: List Bool → List Bool) (s: List Bool) (chunks: List (List Bool)): List Bool := Id.run do
  let mut s := s.setWidth 1600
  for Pi in chunks do
    s := f (xor_long s Pi)
  return s

@[simp]
theorem ListIR.length_absorb'(s: List Bool)(chunks: List (List Bool))
: (absorb' list_keccak_p s chunks).length = 1600
:= by
  simp [absorb']
  cases chunks using List.reverseRecOn <;> simp

theorem ListIR.xor_long_at_twice_compatible(a b c: List Bool)(offset: Nat)
(compatible_offset: offset2 = b.length + offset)
: xor_long_at (xor_long_at a b offset) c (offset2) -- Not offset + b.length so if offset is 0, it's defeq to b.length
= xor_long_at a (b ++ c) offset
:= by
  subst compatible_offset
  simp only [xor_long_at]
  simp_lists
  simp only [List.append_assoc]
  congr 2

  by_cases offset_idx: offset ≥ a.length
  case pos => simp_lists
  case neg =>
    simp at offset_idx
    simp [offset_idx, le_of_lt]
    by_cases h: (a.length - offset) ≤ b.length
    case pos => simp_lists
    case neg =>
      simp [le_of_lt (not_le.mp h)]
      simp +arith

@[simp_lists_simps]
theorem ListIR.getElem!_xor_long_at_inside(a b: List Bool)(offset i: Nat)
: offset ≤ i ∧ i < offset + b.length
→ i < a.length
→ (ListIR.xor_long_at a b offset)[i]! = (a[i]! ^^ b[i - offset]!)
:= by
  intro cond i_idx
  simp [xor_long_at]
  simp_lists
  simp +arith [cond]

@[simp_lists_simps]
theorem ListIR.getElem!_xor_long_at_outside(a b: List Bool)(offset i: Nat)
: ¬ (offset ≤ i ∧ i < offset + b.length)
→ (xor_long_at a b offset)[i]! = a[i]!
:= by
  intro cond
  simp only [not_le, not_lt, not_and_or] at cond
  by_cases h: i < a.length
  case neg =>
    have : ¬ i < (xor_long_at a b offset).length := by simpa using h
    simp_lists
  simp [xor_long_at]
  obtain h | h := cond
  · simp_lists
  · simp_lists
    congr
    scalar_tac

@[simp_lists_simps]
theorem ListIR.getElem!_xor_long_at(a b: List Bool)(offset i: Nat)
: (xor_long_at a b offset)[i]! = if offset ≤ i ∧ i < offset + b.length ∧ i < a.length then a[i]! ^^ b[i - offset]! else a[i]!
:= by
  split
  case isTrue inRange =>
    obtain ⟨range, idx⟩ := inRange
    simp_lists
  case isFalse oob =>
    simp [-not_and, not_and_or] at oob
    obtain i_under | i_over | i_oob := oob
    · simp_lists
    · simp_lists
    · have : ¬ i < (xor_long_at a b offset).length := by simpa using i_oob
      simp_lists

theorem ListIR.xor_long_of_xor_long_at(a b: List Bool)(offset: Nat)
: xor_long_at a b offset = xor_long a (List.replicate offset false ++ b)
:= by
  apply List.ext_getElem!
  · simp [xor_long]
  intro i
  simp [xor_long]
  simp_lists
  split
  case isTrue _ =>
    simp_ifs [Nat.sub_zero]
  case isFalse _ =>
    simp_ifs
    split
    case isTrue h => simp
    case isFalse h => rfl

theorem ListIR.xor_long_at_twice_separate(a b c: List Bool)(offset: Nat)
(compatible_offset: offset2 ≥ offset + b.length)
: xor_long_at (xor_long_at a b offset) c (offset2) -- Not offset + b.length so if offset is 0, it's defeq to b.length
= xor_long_at a (b ++ List.replicate (offset2 - (b.length + offset)) false ++ c) offset
:= by
  apply List.ext_getElem!
  case hl => simp
  intro i

  by_cases i_idx: i < a.length
  case neg => simp_lists

  simp_lists
  split
  case pos.isTrue first_range =>
    simp_ifs
    congr 2
    scalar_tac
  case pos.isFalse not_first_range =>
    split
    case isTrue second_range =>
      simp_ifs
    case isFalse not_second_range =>
      by_cases in_middle: offset + b.length ≤ i ∧ i < offset2
      case pos =>
        simp_ifs
        simp
      case neg =>
        simp_ifs

theorem ListIR.absorb'_absorb'(s: List Bool)(bs bs2: List (List Bool))
: let f := list_keccak_p
  absorb' f (absorb' f s bs) bs2 = absorb' f s (bs ++ bs2)
:= by
  have len_absorb := length_absorb' s bs
  simp [absorb'] at *
  rw [List.setWidth_of_length_eq]
  simpa using len_absorb
