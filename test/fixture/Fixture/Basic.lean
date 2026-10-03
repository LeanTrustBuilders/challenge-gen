import TrustAnnotations
import Fixture.Structures

/-! An annotated definition, and a claim whose proof calls a lemma. -/

namespace Fixture

/-- The predecessor, meant for positive numbers. -/
@[domain (0 < n) "the predecessor of 0 is 0, by convention"]
def pred' (n : Nat) : Nat := n - 1

/-- Called by a proof only. -/
theorem helper (n : Nat) : n - 1 ≤ n := Nat.sub_le n 1

@[claim "the predecessor is smaller"]
theorem pred'_lt (n : Nat) (h : 0 < n) : pred' n < n := by
  have := helper n
  unfold pred'
  omega

/-- A `Prop`-valued class: its instances are proofs. -/
class IsSmall (n : Nat) : Prop where
  small : n < 10

instance : IsSmall 3 := ⟨by decide⟩

def smallVal (n : Nat) [IsSmall n] : Nat := n

/-- Its statement needs the instance `IsSmall 3`, a proof. -/
theorem smallVal_three : smallVal 3 = 3 := rfl

end Fixture
