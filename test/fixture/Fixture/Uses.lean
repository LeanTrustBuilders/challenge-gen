import Fixture.Notation

open Fixture

namespace Fixture.Uses

variable {α : Type} [HasZero' α]

def zeroBox : Box α := { val := HasZero'.zero }

def Code := Nat
deriving BEq

theorem quad (n : Nat) : ⟪⟪n⟫⟫ = 4 * n := by
  simp only [double]
  omega

/-- Declared after `quad`, and unrelated to it. -/
def unrelated : Nat := 7

omit [HasZero' α] in
theorem box_val (b : Box α) : b.val = b.val := rfl

end Fixture.Uses
