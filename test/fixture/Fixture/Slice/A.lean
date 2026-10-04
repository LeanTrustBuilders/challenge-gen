module

/-! In the slice `Fixture.Slice`, imported by a module outside it. -/

@[expose] public section

namespace Fixture.Slice

def base : Nat := 5

def posBase : { n : Nat // 0 < n } := ⟨5, by decide⟩

end Fixture.Slice
