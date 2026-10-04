# ChallengeGen

One Lean file per declaration of a compiled project, which compiles on its own: the declaration and
everything its text needs, copied from the project's source, with the proofs of theorems replaced by
`sorry` and imports cut down to what lies outside the project. Such a file is a challenge for
[Comparator](https://github.com/leanprover/comparator), with the project as the solution: beside
it, challenge-gen writes Comparator's configuration, which lists the theorems to check.

Depends on Lean core and [MeaningGraph](https://github.com/LeanTrustBuilders/meaning-graph).

## What a file holds

The file is a module, which `public import`s the libraries it needs. The declarations are copied
verbatim, with the `namespace`, `section`, `open`, `variable`, `universe`, `set_option` and notation
commands around them, so the file reads the way its author wrote it, and each has the visibility it
has in the project: the text of a module of the project keeps its own `public section`s and
`@[expose]`, and that of a file that is not a module sits in an `@[expose] public section`. Then:

- a theorem's proof is replaced by `sorry`. Every other declaration is copied whole: a definition or
  an instance with the proofs inside its value, a structure with its fields' tactic defaults, a
  definition with its `deriving` clause;
- the annotations of [TrustAnnotations](https://github.com/LeanTrustBuilders/annotations)
  (`@[claim]`, `@[specifies]`, `@[domain]`, …) are removed, with their import and their options,
  and so is `@[ext]` on a theorem;
- `variable` binders that mention a declaration left out are dropped, and so are the `include` and
  `omit` entries naming them; sections and namespaces left empty, and `set_option` lines with no
  effect, go too;
- an `instance` written without a name gets the name the project gave it, since Lean would name it
  otherwise in another file;
- the options the project is built with, its lakefile's `leanOptions` as Lake records them for each
  module, are set again when they are Lean's own and change what the file means or whether it
  compiles (`autoImplicit`, `maxSynthPendingDepth`, `backward.*`, …), not only what Lean reports
  (`pp.*`, `linter.*`, `warningAsError`);
- nothing declared after the target is kept.

What a declaration needs comes from MeaningGraph: what its statement mentions, proofs included,
when its proof became `sorry`; everything its term mentions, the lemmas its proofs call included,
when it is kept whole; in both cases its source dependencies (coercion instances, what a notation
expands to). The notations its source uses come along, and so do the other declarations its
command defines (`@[to_additive]`, `@[simps]`, `irreducible_def`), each with what it needs in turn.
So does a declaration whose auxiliary theorem or definition it uses: Lean makes a proof inside
`foo` a theorem `foo._proof_1`, and takes it again for a later proof of the same statement.

The project can be a slice of a library (`--root Mathlib.Probability`): the rest of the library is
then imported, and a module of the slice that those imports already bring is not copied.

## Comparator

Comparator requires every constant that a checked theorem's statement reaches to be the same in the
challenge and in the solution, values included, except the theorems it checks: those it compares by
statement, and their proofs must use no axiom but the permitted ones. The configuration
`<file>.json` lists these: the theorems Comparator reaches from the target, following statements
and the values of definitions, and stopping at theorems. A lemma left `sorry` that a definition
uses (`argmax := (exists_argmax f).choose`) is among them, so the solution has to prove it; one that
only a proof uses is not. So are the theorems Lean makes of the proofs inside a definition
(`foo._proof_1`): elaborated again in the file, such a proof need not be the project's.

The configuration follows the layout Palomar asks for: the file as the module `Challenge`, a module
`Solution` that imports the project, and only `propext`, `Quot.sound` and `Classical.choice`
permitted.

## Use

Build the project, and `challenge-gen` with the project's Lean toolchain (`main` or the branch
`lean-v<toolchain>`), then, in the project:

```
lake env challenge-gen --root MyProject --decl MyProject.main_theorem --out challenges
```

writes `challenges/MyProject___main_theorem.lean` and `challenges/MyProject___main_theorem.json`.
Without `--decl`, it writes the files of every declaration of the project. The options are in
`challenge-gen --help`.

From Lean, `ChallengeGen.writeChallenges (MeaningGraph.Context.of env root) srcDir out targets`, in
an environment with the project imported. `anchorIdOf` gives a file's name.

## Limits

A file does not compile when its text needs something that no dependency records:
- a constant named by a literal (``` ``foo ```), as metaprograms do;
- a lemma that a tactic block in a definition names but its proof does not use (`simp only [foo]`);
- a registration made by a standalone `attribute` command other than `to_additive` and `to_dual`,
  such as the `@[simp]` lemmas a tactic block in a definition relies on;
- a library that does not use the module system, which a module cannot import.

A private declaration's name holds the name of its module, so it is another constant in the file
than in the project, and Comparator rejects a statement that reaches one: challenge-gen says so.

## Versions

`main` is on the Lean toolchain of Mathlib's master. Every hour, the workflow Follow Mathlib's
toolchain checks: when Mathlib has moved, it keeps the old toolchain on a branch
`lean-v<toolchain>`, moves `main` to the new one once it builds with its tests, after MeaningGraph
and TrustAnnotations have moved, and tags it `v<toolchain>`. A build that fails opens an issue
labelled `toolchain` instead. The branches of older toolchains get no further changes.

## Tests

`lake build ChallengeGenTest` runs the `#guard` checks in `ChallengeGen/Test.lean`. After
`lake build`, `test/run.sh` writes the files of every declaration of `test/fixture`, compiles each
one, checks what some of them hold, and checks that each target states what the fixture states and
that its configuration lists the theorems Comparator must check.

Those last checks work on any project: `test/fidelity.py <project> <files> <root module> <work dir>`
compiles the files challenge-gen wrote for the project and compares each target's elaborated type
with the project's own; a file can compile and still state another theorem. It also walks each file
as Comparator does from the theorems its configuration lists, and reports a constant reached whose
statement or value uses `sorry` outside the proof of one of them.
