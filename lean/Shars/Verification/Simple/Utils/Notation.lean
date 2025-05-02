import Aeneas

notation "‹" term "›'" => (by scalar_tac: term)


syntax "assume " (atomic(ident " : "))? term : tactic

macro_rules
  | `(tactic| assume $e) => `(tactic| assume h : $e)

macro_rules
  | `(tactic| assume $h : $e) =>
    `(tactic| refine if $h:ident : $e then ?_ else ?otherwise)
