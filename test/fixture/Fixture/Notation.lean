import Fixture.Basic

namespace Fixture

def double (n : Nat) : Nat := 2 * n

notation:max "⟪" n "⟫" => double n

section
variable (m : Nat)

theorem double_pos (h : 0 < m) : 0 < ⟪m⟫ := by
  unfold double
  omega

end

section
local notation "⦃" n "⦄" => double (double n)

theorem quad' (n : Nat) : ⦃n⦄ = 4 * n := by
  simp only [double]
  omega

end

end Fixture
