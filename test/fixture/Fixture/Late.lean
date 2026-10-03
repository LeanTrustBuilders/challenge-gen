import Fixture.Basic

/-! The scoped notation `ℵ`, which `Fixture.Early` does not see. -/

namespace Fixture

scoped notation "ℵ" => (0 : Nat)

end Fixture
