import Fixture.Structures

/-! A proof of the statement of one in another module, which Lean made apart. -/

namespace Fixture

/-- Its proof, `0 < 1`, is that of `one`'s, made in another module: Lean made `oneAgain._proof_1`.
In one file with `one`, it would take `one._proof_1`. -/
def oneAgain : Positive × Positive := (one, ⟨1, by decide⟩)

end Fixture
