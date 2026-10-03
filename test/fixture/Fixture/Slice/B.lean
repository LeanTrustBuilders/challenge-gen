import Fixture.Other

/-! In the slice, importing a module outside it that imports `Fixture.Slice.A`. -/

namespace Fixture.Slice

theorem twiceBase_eq : twiceBase = 2 * base := rfl

end Fixture.Slice
