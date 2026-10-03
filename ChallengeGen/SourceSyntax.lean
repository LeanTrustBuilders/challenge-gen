module

public import Lean

@[expose] public section

/-!
# Re-parsing a project's source, and reading declaration keywords off the syntax

The extraction re-parses each source file against the already-loaded environment, and decides from
a command's syntax whether it is a theorem whose proof is replaced by `sorry`. The keyword a
declaration was written with cannot be recovered from the compiled environment: Mathlib's `lemma`
is a macro that rewrites itself to `theorem` before elaboration.
-/

open Lean

namespace ChallengeGen

/-! ## Declaration keywords, as syntax kinds

The keyword a declaration was written with survives only in the parse tree. These are the kinds to
look for; the lists are plural because more than one package defines the same keyword.
-/

/-- Command kinds meaning "written with `lemma`".

Mathlib's `lemma` is declared at the root (`syntax (name := lemma) …` in `Mathlib/Tactic/Lemma.lean`)
and takes priority over the Batteries one, which it exists to override — but a project may have
either, so both count. -/
def lemmaSyntaxKinds : Array SyntaxNodeKind := #[`lemma, `Batteries.Tactic.Lemma.lemmaCmd]

/-- Command kinds meaning "written with `theorem`", the plain keyword and every `lemma` synonym:
the "has a proof that is replaced by `sorry`" test. -/
def theoremSyntaxKinds : Array SyntaxNodeKind :=
  #[``Lean.Parser.Command.theorem] ++ lemmaSyntaxKinds

/-- Command kinds declaring a `structure` or a `class`; both parse as `Command.structure`, differing
only in whether they begin with `structureTk` or `classTk`. -/
def structureSyntaxKinds : Array SyntaxNodeKind := #[``Lean.Parser.Command.structure]

/-! ## Searching a command's syntax -/

/-- The first descendant of `root` whose kind is one of `kinds`, breadth-first.

Searching the whole tree rather than only the head is what sees through the wrapper commands a
declaration can be nested in — `set_option … in`, `open … in`, `omit … in`. It stays specific
despite that: a declaration keyword is a *command* node, and no term ever contains one, so a `def`'s
syntax cannot match `theoremSyntaxKinds`. -/
partial def findFirstOfKinds? (root : Syntax) (kinds : Array SyntaxNodeKind) : Option Syntax :=
  Id.run do
  let mut worklist : Array Syntax := #[root]
  while !worklist.isEmpty do
    let stx := worklist.back!
    worklist := worklist.pop
    if kinds.contains stx.getKind then return some stx
    for arg in stx.getArgs do
      worklist := worklist.push arg
  return none

@[inherit_doc findFirstOfKinds?]
def findFirstOfKind? (root : Syntax) (kind : SyntaxNodeKind) : Option Syntax :=
  findFirstOfKinds? root #[kind]

/-- True if any node of `stx` has one of `kinds`. See `findFirstOfKinds?` for why the whole tree. -/
def containsSyntaxKind (stx : Syntax) (kinds : Array SyntaxNodeKind) : Bool :=
  (findFirstOfKinds? stx kinds).isSome

/-! ## Parsing a file -/

/-- Every top-level command of `source`, re-parsed against `env`, with the module header dropped.

Elaboration errors are expected and ignored. `env` already contains every declaration in the file —
it is the environment the project was loaded into — so each declaration command fails with
"declaration already exists" almost immediately, which is exactly why this is cheap enough to run
over a whole project. Only the parsed `Syntax` is consumed, and the parser produces that either way.

Positions on the returned syntax are byte offsets into `source`; a caller wanting lines can convert
through `source.toFileMap`. -/
def parseCommands (env : Environment) (source : String) (filePath : String) : IO (Array Syntax) := do
  let inputCtx := Lean.Parser.mkInputContext source filePath
  let (_, parserState, messages) ← Lean.Parser.parseHeader inputCtx
  let cmdState := Lean.Elab.Command.mkState env messages {}
  let s ← Lean.Elab.IO.processCommands inputCtx parserState cmdState
  return s.commands.filter (·.getKind != ``Lean.Parser.Module.header)

end ChallengeGen
