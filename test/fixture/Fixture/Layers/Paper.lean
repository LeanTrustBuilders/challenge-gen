module

public import Fixture.Layers.Dep

/-! A paper on the dependency: its challenge imports the library only. -/

@[expose] public section

namespace Fixture.Layers

theorem paper_main (n : Nat) (h : 0 < n) : (scaledPos n h).val = libBase * n := rfl

end Fixture.Layers
