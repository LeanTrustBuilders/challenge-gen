import Fixture.Basic

/-! `include` and `omit` as commands: each changes the statements that follow. -/

namespace Fixture.Inc

structure Big where
  n : Nat

section
variable (n : Nat) (hn : 0 < n)
include hn

/-- `hn` is a hypothesis only because of `include hn`. -/
theorem pos_succ : 0 < n + 1 := Nat.succ_pos n

omit hn

theorem le_succ : n ≤ n + 1 := Nat.le_succ n

end

/-- Values are kept: these compile only if `pos_succ` takes `hn` and `le_succ` does not. -/
def usesPos : 0 < 3 + 1 := pos_succ 3 (by decide)

def usesLe : 3 ≤ 3 + 1 := le_succ 3

section
def early : Nat := 1
variable (b : Big)
include b
theorem late : b = b := rfl
end

end Fixture.Inc
