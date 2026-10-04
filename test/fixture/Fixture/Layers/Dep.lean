module

public import Fixture.Layers.Lib

/-! A dependency the paper builds on, which its challenge copies rather than imports. -/

@[expose] public section

namespace Fixture.Layers

def scaled (n : Nat) : Nat := libBase * n

theorem scaled_pos (n : Nat) (h : 0 < n) : 0 < scaled n := Nat.mul_pos libBase_pos h

/-- Its value uses a lemma of this module, which the paper's challenge must then leave to check. -/
def scaledPos (n : Nat) (h : 0 < n) : { m : Nat // 0 < m } := ⟨scaled n, scaled_pos n h⟩

/-- Not needed by the paper. -/
def unused : Nat := 0

end Fixture.Layers
