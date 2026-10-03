module

@[expose] public noncomputable section

/-! The module system's wrapper, noncomputable, and closed. -/

namespace Fixture

/-- Picked by choice: compiles only as noncomputable. -/
def pick' (α : Type) [Nonempty α] : α := Classical.choice inferInstance

end Fixture

end
