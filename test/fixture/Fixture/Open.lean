import Fixture.Basic

/-! `open NS (a)` naming a declaration from outside the project, instances of a `Prop`-valued
class, and names Lean generates for instances. -/

open Nat (succ)

namespace Fixture

def three : Nat := succ 2

class IsPositive (n : Nat) : Prop where
  pos : 0 < n

instance : IsPositive three where
  pos := by simp [three]

section
variable {m : Nat} [IsPositive m]

/-- Its proof uses `[IsPositive m]`, which its statement does not mention: an instance takes the
variables its value uses, so its value cannot become `sorry` without changing its signature. -/
instance : IsPositive (m * 1) := by simpa using (inferInstance : IsPositive m)

end

/-- Derived in the namespace of the definition, `Fixture.Wrap`, not the current one. -/
def Wrap.Num := Nat
deriving BEq

/-- A parameter with a tactic default: an `autoParam` in the structure's type. -/
structure Sized (n : Nat := by exact 3) where
  val : Fin (n + 1)

end Fixture

namespace Nat

/-- An unnamed instance in a namespace of another package: Lean gives it a suffixed name. -/
instance : Fixture.IsPositive 1 := ⟨Nat.one_pos⟩

end Nat
