module

/-! A module whose public definition, its value not exposed, uses a private one. -/

public section

namespace Fixture

private def secret : Nat := 7

/-- Its value is not exposed, so it may use `secret`. -/
def revealed : Nat := secret + 1

end Fixture

end
