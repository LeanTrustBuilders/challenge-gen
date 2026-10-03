module

public import Lean
public import Lean.DeclarationRange

@[expose] public section

/-!
# Names, files and ranges

Small helpers the extraction is built on. `anchorIdOf` in particular is a *contract* rather than a
convenience: it is the name of the file written for a declaration, so a tool that links to those
files has to compute the stem the same way. One definition, imported by both.
-/

open Lean

namespace ChallengeGen

/-- The components of a name, as strings. -/
def nameComponents : Name → List String
  | .anonymous => []
  | .num p n => nameComponents p ++ [toString n]
  | .str p s => nameComponents p ++ [s]

/-- The namespace `n` and all of its ancestor namespaces, innermost first. -/
partial def namespaceAncestors : Name → List Name
  | .anonymous => []
  | n => n :: namespaceAncestors n.getPrefix

/-- Maps a declaration name to an identifier safe to use as a filename, URL, and HTML anchor:
namespace dots become `___`, and the characters forbidden in filenames on some operating systems
(Windows: `< > : " / \ | ? *`) are replaced by fullwidth Unicode lookalikes that are legal
everywhere. Notation declarations such as `«term𝓛[_|_;_]»` would otherwise produce a `|` in the
filename, which is illegal on Windows and rejected by Lean's module-name portability check. -/
def anchorIdOf (name : Name) : String :=
  let safeChar : Char → Char := fun c =>
    match c with
    | '<' => '＜' | '>' => '＞' | ':' => '：' | '"' => '＂' | '/' => '／'
    | '\\' => '＼' | '|' => '｜' | '?' => '？' | '*' => '＊'
    | _ => c
  (String.intercalate "___" (name.toString.splitOn ".")).map safeChar

/-- The source file of `moduleName`, under the project's source directory. -/
def moduleSourcePath (projectDir : System.FilePath) (moduleName : Name) : System.FilePath :=
  projectDir / s!"{moduleName.toString.replace "." "/"}.lean"

/-- The `Core.Context` the extraction runs its `CoreM` and `MetaM` actions in. -/
def coreContext : Core.Context :=
  { fileName := "<challenge-gen>", fileMap := default, options := {},
    currNamespace := .anonymous, openDecls := [], maxHeartbeats := 0, maxRecDepth := 8000 }

/-- Runs a `CoreM` action against an already-imported environment. -/
def runCoreIO {α : Type} (env : Environment) (x : CoreM α) : IO α := do
  x.toIO' coreContext { env := env, ngen := { namePrefix := `_challengeGen } }

/-- Runs a `MetaM` action against an already-imported environment. -/
def runMetaIO {α : Type} (env : Environment) (x : MetaM α) : IO α :=
  runCoreIO env (x.run' {} {})

/-- Retrieves declaration source ranges, returning `none` on failure. -/
def findRanges? (env : Environment) (name : Name) : IO (Option DeclarationRanges) := do
  try
    runCoreIO env (findDeclarationRanges? name)
  catch _ =>
    pure none

end ChallengeGen
