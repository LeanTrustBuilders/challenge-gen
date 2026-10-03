import Fixture.Basic

/-! A namespace named after a structure, entered for a declaration that does not need the
structure, with a `variable` binder holding parentheses. -/

set_option autoImplicit false

namespace Fixture

structure Pair where
  fst : Nat
  snd : Nat

end Fixture

namespace Fixture.Pair

variable (g : (Nat → Nat))

theorem app_eq : g 0 = g 0 := rfl

end Fixture.Pair
