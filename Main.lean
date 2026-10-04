import ChallengeGen

open Lean ChallengeGen

def usage : String := "\
challenge-gen: one standalone Lean file per declaration of a compiled project, made of the
project's own source text, with its dependencies inlined and its theorems' proofs replaced by
`sorry`: a challenge for Comparator, with the project as the solution.

Run inside the project, under `lake env`:

  lake env challenge-gen --root <Prefix> [options]

Options:
  --root <Prefix>      root module prefix of the project (required), e.g. LeanMachineLearning
  --decl <Name>        write the file of this declaration (repeatable; default: every declaration
                       of the project)
  --decls-file <file>  the same, one name per line
  --out <dir>          output directory (default: challenges)
  --src-dir <dir>      where the project's sources are (default: .); the sources of other
                       modules a file copies are found on LEAN_SRC_PATH, which `lake env` sets
  --import <Prefix>    the files may import the modules under this prefix and every module they
                       import (repeatable); they copy what they need of every other module.
                       Default: they import every module outside the root
  --module <Module>    import this module instead of every module under the root (repeatable)

Each file is named after its declaration: `Foo.bar` is written to `Foo___bar.lean`, and beside it
`Foo___bar.json`, Comparator's configuration, which lists the theorems to check. A file Comparator
cannot check gets none, and challenge-gen says why.
"

structure Config where
  root : Name := .anonymous
  decls : Array Name := #[]
  out : System.FilePath := "challenges"
  srcDir : System.FilePath := "."
  modules : Array Name := #[]
  imports : Array Name := #[]

partial def parseArgs (args : List String) (cfg : Config) : IO (Except String Config) :=
  match args with
  | [] => return .ok cfg
  | "--root" :: v :: rest => parseArgs rest { cfg with root := v.toName }
  | "--decl" :: v :: rest => parseArgs rest { cfg with decls := cfg.decls.push v.toName }
  | "--decls-file" :: v :: rest => do
    let names := ((← IO.FS.readFile v).splitOn "\n").map (·.trimAscii.toString)
      |>.filter (fun s => !s.isEmpty && !s.startsWith "#") |>.map (·.toName)
    parseArgs rest { cfg with decls := cfg.decls ++ names.toArray }
  | "--out" :: v :: rest => parseArgs rest { cfg with out := v }
  | "--src-dir" :: v :: rest => parseArgs rest { cfg with srcDir := v }
  | "--module" :: v :: rest => parseArgs rest { cfg with modules := cfg.modules.push v.toName }
  | "--import" :: v :: rest => parseArgs rest { cfg with imports := cfg.imports.push v.toName }
  | a :: _ => return .error s!"unknown argument `{a}`"

/-- The modules of the project rooted at `root` whose source files are under `srcDir`: `root` itself
and every module below it, sorted. -/
def discoverModules (srcDir : System.FilePath) (root : Name) : IO (Array Name) := do
  let mut mods : Array Name := #[]
  if ← (moduleSourcePath srcDir root).pathExists then mods := mods.push root
  let rootDir := moduleSourcePath srcDir root |>.withExtension ""
  if ← rootDir.isDir then
    for path in ← rootDir.walkDir do
      if path.extension == some "lean" then
        let rel := (path.toString.drop (rootDir.toString.length + 1)).toString
        let parts := (System.FilePath.mk rel |>.withExtension "").components
        mods := mods.push (parts.foldl Name.str root)
  return mods.qsort (·.toString < ·.toString)

unsafe def main (args : List String) : IO UInt32 := do
  -- Lean's own options, registered before any module is imported: the only ones every file knows.
  let builtinOptions : Std.HashSet Name :=
    (← getOptionDecls).foldl (init := {}) fun s n _ => s.insert n
  -- Imported modules' `initialize` declarations must run, so that their environment extensions are
  -- registered and receive their imported entries: the source is parsed with them.
  enableInitializersExecution
  if args.any (· ∈ ["--help", "-h"]) then
    IO.println usage; return 0
  match ← parseArgs args {} with
  | .error e => IO.eprintln s!"{e}\n\n{usage}"; return 2
  | .ok cfg =>
    if cfg.root.isAnonymous then
      IO.eprintln s!"--root is required\n\n{usage}"; return 2
    try
      initSearchPath (← findSysroot)
      let mods ← if cfg.modules.isEmpty then discoverModules cfg.srcDir cfg.root
        else pure cfg.modules
      if mods.isEmpty then
        throw <| IO.userError s!"no module {cfg.root} under {cfg.srcDir}"
      let env ← importModules (mods.map ({ module := · })) {} (loadExts := true)
      -- The project, whose declarations the files copy: the root's modules, or every module but
      -- those the files may import.
      let ctx ← if cfg.imports.isEmpty then pure (MeaningGraph.Context.of env cfg.root) else do
        for p in cfg.imports do
          unless env.header.moduleNames.any (MeaningGraph.hasPrefixName · p) do
            throw <| IO.userError s!"no module under {p}, given to --import"
        let importable := importableModules env cfg.imports
        pure (MeaningGraph.Context.ofModules env (!importable.contains ·))
      let underRoot (n : Name) : Bool :=
        (MeaningGraph.moduleNameOf env n).any (MeaningGraph.hasPrefixName · cfg.root)
      let targets := if cfg.decls.isEmpty then (projectDeclarations ctx).filter underRoot
        else cfg.decls
      let unknown := targets.filter (!ctx.exposed.contains ·)
      unless unknown.isEmpty do
        throw <| IO.userError
          s!"not declarations of {cfg.root}: {", ".intercalate (unknown.toList.map toString)}"
      IO.FS.createDirAll cfg.out
      let n ← writeChallenges ctx cfg.srcDir cfg.out targets builtinOptions
      IO.println s!"wrote {n} files to {cfg.out}"
      return 0
    catch e =>
      IO.eprintln s!"error: {e}"; return 1
