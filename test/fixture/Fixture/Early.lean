import Fixture.Basic

/-! A binder named like a scoped notation that a module this one does not import declares, in a
namespace this one opens: here `ℵ` is an identifier. -/

open Fixture

def earlyId (ℵ : Nat) : Nat := ℵ
