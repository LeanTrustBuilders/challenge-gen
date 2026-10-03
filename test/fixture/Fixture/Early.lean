import Fixture.Notation

/-! A binder named like a scoped notation that a module this one does not import declares, in a
namespace this one opens: here `ℵ` is an identifier. The notation `⟪_⟫` this module does import
must still parse when the module is parsed again against its own imports. -/

open Fixture

def earlyId (ℵ : Nat) : Nat := ⟪ℵ⟫
