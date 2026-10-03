import Fixture.Basic

/-! A `noncomputable section` left open at the end of the file, as is usual. -/

noncomputable section

open Classical

namespace Fixture

/-- Picked by choice: compiles only as noncomputable. -/
def pick (α : Type) [Nonempty α] : α := Classical.choice inferInstance

theorem pick_eq (α : Type) [Nonempty α] : pick α = pick α := rfl

end Fixture
