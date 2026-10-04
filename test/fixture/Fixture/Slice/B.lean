module

public import Fixture.Other

/-! In the slice, importing a module outside it that imports `Fixture.Slice.A`. -/

@[expose] public section

namespace Fixture.Slice

theorem twiceBase_eq : twiceBase = 2 * base := rfl

/-- `posBase`, and the theorem Lean made of its proof, come with the import of `Fixture.Other`: not
to be checked. -/
theorem posBase_val : posBase.val = base := rfl

end Fixture.Slice
