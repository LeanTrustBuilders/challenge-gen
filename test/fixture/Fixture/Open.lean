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

/-- Only its embedded proof uses `[IsPositive m]`: with that proof replaced by `sorry`, the instance
would not take it, unless the `sorry` mentions it. -/
instance : IsPositive (m + 0) := ⟨by have := (inferInstance : IsPositive m).pos; omega⟩

end

section
variable (k : Nat) (hk : 0 < k)

/-- Only its embedded proof uses `hk`. -/
def predBelow : { j : Nat // j < k } := ⟨k - 1, by omega⟩

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
