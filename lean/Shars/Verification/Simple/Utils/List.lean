import Init.Data.Vector.Lemmas
import Mathlib

theorem List.foldl_of_foldl_map(f: α' → α)(upd: β → α → β)(upd' : β → α' → β)(init: β)(ls: List α')
: upd' = (upd · <| f ·)
→ List.foldl upd' init ls = List.foldl upd init (ls.map f) 
:= by rintro rfl; revert init; induction ls <;> simp [*]

theorem List.val_finRange_eq_range(n: Nat)
: (List.finRange n).map Fin.val = List.range n
:= by cases n <;> simp

theorem List.drop_range'(i s n: Nat): (List.range' s n |>.drop i) = List.range' (s + i) (n - i) := by
  cases i 
  case zero => simp
  case succ i' => 
    cases n
    case zero => simp
    case succ n' => 
      rw [List.range'_succ, List.drop_succ_cons, Nat.add_comm i', ←Nat.add_assoc, Nat.sub_add_eq, Nat.add_sub_cancel]
      apply List.drop_range'

theorem List.drop_range(i n: Nat): (List.range n |>.drop i) = List.range' i (n-i) := by
  simp [List.range_eq_range', List.drop_range' (s := 0)]

theorem getElem_eq_getElem! [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
  [Inhabited elem] (c : cont) (i : idx) (h : dom c i) 
: getElem c i h = getElem! c i
:= by
  have : Decidable (dom c i) := .isTrue h
  simp [getElem!_def, getElem?_def, h]
