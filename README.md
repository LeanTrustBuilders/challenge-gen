# ChallengeGen

One Lean file per declaration of a compiled project, which compiles on its own: the declaration and
everything its text needs, copied from the project's source, with proofs replaced by `sorry` and
imports cut down to what lies outside the project. Such a file states one problem, for whoever has
to produce the proof.

Depends on Lean core and [MeaningGraph](https://github.com/LeanTrustBuilders/meaning-graph).

## What a file holds

The declarations are copied verbatim, with the `namespace`, `section`, `open`, `variable`,
`universe`, `set_option` and notation commands around them, so the file reads the way its author
wrote it. Then:

- a theorem's proof is replaced by `sorry`, and so are the proofs inside a definition's value,
  except a tactic block that is the whole value: Lean decides from it which section variables the
  definition takes;
- a field's default `:= by tac` becomes `:= sorry`, and a definition's `deriving` clause becomes
  `instance … := sorry`;
- the annotations of [TrustAnnotations](https://github.com/LeanTrustBuilders/annotations)
  (`@[claim]`, `@[specifies]`, `@[domain]`, …) are removed, with their import and their options,
  and so is `@[ext]` on a theorem;
- `variable` binders and `omit` entries that mention a declaration left out are dropped, as are
  sections and namespaces left empty and `set_option` lines with no effect;
- `noncomputable section` stays; the module system's `@[expose]`, `public` and `meta` go, since the
  file is not a module;
- the options the project is built with, its lakefile's `leanOptions` as Lake records them for each
  module, are set again when they are Lean's own and change what the file means or whether it
  compiles (`autoImplicit`, `maxSynthPendingDepth`, `backward.*`, …), not only what Lean reports
  (`pp.*`, `linter.*`, `warningAsError`);
- nothing declared after the target is kept.

What a declaration needs comes from MeaningGraph: what its statement mentions, when its proof became
`sorry`; everything its term mentions, the lemmas its proofs call included, when it is kept whole;
in both cases its source dependencies (coercion instances, what a notation expands to). The
notations its source uses come along, and so do the other declarations its command defines
(`@[to_additive]`, `@[simps]`), each with what it needs in turn.

## Use

Build the project, and `challenge-gen` with the project's Lean toolchain (`main` or the branch
`lean-v<toolchain>`), then, in the project:

```
lake env challenge-gen --root MyProject --decl MyProject.main_theorem --out challenges
```

writes `challenges/MyProject___main_theorem.lean`. Without `--decl`, it writes the file of every
declaration of the project. The options are in `challenge-gen --help`.

From Lean, `ChallengeGen.writeChallenges (MeaningGraph.Context.of env root) srcDir out targets`, in
an environment with the project imported. `anchorIdOf` gives a file's name.

## Limits

A file does not compile when its text needs something that no dependency records:
- a constant named by a literal (``` ``foo ```), as metaprograms do;
- a lemma that a kept tactic block names but its proof does not use (`simp only [foo]`);
- a registration made by a standalone `attribute` command other than `to_additive` and `to_dual`,
  such as the `@[simp]` lemmas a kept tactic block relies on.

## Versions

`main` is on the Lean toolchain of Mathlib's master. Every hour, the workflow Follow Mathlib's
toolchain checks: when Mathlib has moved, it keeps the old toolchain on a branch
`lean-v<toolchain>`, moves `main` to the new one once it builds with its tests, after MeaningGraph
and TrustAnnotations have moved, and tags it `v<toolchain>`. A build that fails opens an issue
labelled `toolchain` instead. The branches of older toolchains get no further changes.

## Tests

`lake build ChallengeGenTest` runs the `#guard` checks in `ChallengeGen/Test.lean`. After
`lake build`, `test/run.sh` writes the file of every declaration of `test/fixture`, compiles each
one, checks what some of them hold, and checks that each target states what the fixture states.

That last check works on any project: `test/fidelity.py <project> <files> <root module> <work dir>`
compiles the files challenge-gen wrote for the project and compares each target's elaborated type
with the project's own. A file can compile and still state another theorem.
