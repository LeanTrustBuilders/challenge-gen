import Fixture.Basic

/-! Two namespaces opened separately and closed by one `end`, in a section left open. -/

noncomputable section

namespace Fixture
namespace Nested

def four : Nat := 4

end Fixture.Nested

theorem four_eq : Fixture.Nested.four = 4 := rfl
