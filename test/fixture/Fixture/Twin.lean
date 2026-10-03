import Fixture.Basic

/-! A command declaring two constants at the same position, as Mathlib's `irreducible_def` declares
`foo` and `foo_def`. -/

/-- `def_with_eq n : T := v` declares `n` and the theorem `n_def : n = v`. -/
macro "def_with_eq " n:ident " : " t:term " := " v:term : command =>
  `(def $n : $t := $v
    theorem $(Lean.mkIdent (n.getId.appendAfter "_def")) : $n = $v := rfl)

namespace Fixture

def_with_eq seven : Nat := 7

theorem seven_pos : 0 < seven := by decide

end Fixture
