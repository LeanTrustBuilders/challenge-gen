import Fixture.Basic

/-! `open NS (a)` naming a declaration from outside the project, and an instance of a `Prop`-valued
class whose proof is a tactic block naming a lemma it does not use. -/

open Nat (succ)

namespace Fixture

def three : Nat := succ 2

/-- Never used by a proof below, though a tactic names it. -/
theorem unused_lemma : 2 + 2 = 4 := rfl

class IsPositive (n : Nat) : Prop where
  pos : 0 < n

instance : IsPositive three where
  pos := by simp [unused_lemma, three]

end Fixture

namespace Nat

/-- An unnamed instance in a namespace of another package: Lean gives it a suffixed name. -/
instance : Fixture.IsPositive 1 := ⟨Nat.one_pos⟩

end Nat
