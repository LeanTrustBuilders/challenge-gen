module

public import ChallengeGen.Basic
public import ChallengeGen.SourceSyntax
public import ChallengeGen.Extract

@[expose] public section

/-!
# Standalone Lean files, one per declaration

Turns a declaration of a compiled project into a file that compiles on its own: its dependencies
inlined, its proofs replaced by `sorry`, its imports cut down to the external frontier. One such
file is a self-contained statement of one problem, which is what makes it usable as a challenge
for something that has to produce the proof.

The file is made of the project's own source text: each declaration verbatim, with the surrounding
`namespace`/`open`/`variable`/notation context replayed, so it reads the way its author wrote it.
`ChallengeGen.writeChallenges` writes the files; it needs a live `Environment` with the project
imported, and the project's source files.
-/
