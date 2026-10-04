module

/-! The library a paper's challenge may import (`--import Fixture.Layers.Lib`). -/

@[expose] public section

namespace Fixture.Layers

def libBase : Nat := 3

theorem libBase_pos : 0 < libBase := by decide

end Fixture.Layers
