module

@[expose] public section

/-! A structure, a class, and definitions with proofs and tactics in them, in a module. -/

set_option autoImplicit false

namespace Fixture

universe u

structure Box (α : Type u) where
  val : α
  size : Nat := by exact 0

def Positive : Type := { n : Nat // 0 < n }

def one : Positive := ⟨1, by decide⟩

/-- Its proof states what `one`'s does: Lean takes the theorem it made of that one,
`one._proof_1`. -/
def alsoOne : Positive := ⟨1, by decide⟩

def two : Nat := by exact 2

class HasZero' (α : Type u) where
  zero : α

instance : HasZero' Nat := ⟨0⟩

/-- A pair, its extensionality lemma declared apart from it. -/
structure Duo where
  fst : Nat
  snd : Nat

@[ext] theorem Duo.ext' {p q : Duo} (h₁ : p.fst = q.fst) (h₂ : p.snd = q.snd) : p = q := by
  cases p; cases q; simp_all

/-- Its proof calls `ext`, which finds `Duo.ext'` only if it is registered. -/
def duoSelf (p : Duo) : { q : Duo // q = p } := ⟨⟨p.fst, p.snd⟩, by ext <;> rfl⟩

end Fixture
