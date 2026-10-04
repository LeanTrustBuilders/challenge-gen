#!/usr/bin/env python3
"""Compiles challenge files and compares each target's statement with the project's own.

Usage: test/fidelity.py PROJECT_DIR FILES_DIR ROOT_MODULE WORK_DIR [JOBS]

For each `<target>.lean` in FILES_DIR (as challenge-gen names them), compiles a copy with a probe
printing the target's elaborated type, under PROJECT_DIR's `lake env`, and compares that type with
the one printed in a file importing ROOT_MODULE (both also import `Lean`, for the probe). Types are
printed with `pp.all`, every argument and universe explicit and no notation, and with every binder
renamed, so neither notation, `open`s nor binder names play a part. Proofs inside a
type are erased first: one statement may elaborate a proof in place where the other abstracted it
into an auxiliary lemma, and by proof irrelevance they state the same. Private targets are
skipped.

Each file is also checked against its `<target>.json`, Comparator's configuration: walking the file
as Comparator does from the theorems to check, no constant reached may use `sorry` but in the proof
of one of them, and each of these must be a theorem of the file, its name read as Comparator reads
it (`String.toName`). A file that fails this is `UNLISTED`.

Writes WORK_DIR/fidelity.txt and prints a count of `same`, `DIFFERS`, `UNLISTED`, `fail` (does not
compile) and `no-project` (not found in the project); exits with 1 if any file differs, is
unlisted or fails.
"""
import collections
import concurrent.futures as cf
import json
import pathlib
import re
import subprocess
import sys

project, files_dir, root, work = map(pathlib.Path, sys.argv[1:5])
jobs = int(sys.argv[5]) if len(sys.argv) > 5 else 8
work.mkdir(parents=True, exist_ok=True)
files = sorted(p for p in files_dir.glob("*.lean") if not p.name.startswith("_private"))

# `anchorIdOf` writes these characters, forbidden in some file systems, as fullwidth lookalikes.
FULLWIDTH = str.maketrans("＜＞：＂／＼｜？＊", "<>:\"/\\|?*")


def name_of(path):
    return path.stem.replace("___", ".").translate(FULLWIDTH)


# Every binder named `x`, so that statements are compared up to the names of their binders, which
# say nothing of what is stated.
PRELUDE = """
open Lean in
partial def challengeGenAnon : Expr → Expr
  | .forallE _ d b bi => .forallE `x (challengeGenAnon d) (challengeGenAnon b) bi
  | .lam _ d b bi => .lam `x (challengeGenAnon d) (challengeGenAnon b) bi
  | .letE _ t v b nd => .letE `x (challengeGenAnon t) (challengeGenAnon v) (challengeGenAnon b) nd
  | .app f a => .app (challengeGenAnon f) (challengeGenAnon a)
  | .mdata m e => .mdata m (challengeGenAnon e)
  | .proj s i e => .proj s i (challengeGenAnon e)
  | e => e
"""


def probe(key, name):
    # The name goes in as a string, decoded at run time, so that one that does not parse fails alone.
    literal = json.dumps("`" + name, ensure_ascii=False)
    return ("\nopen Lean Meta in\n#eval show MetaM Unit from do\n"
            f"  let n := (Syntax.decodeNameLit {literal}).getD .anonymous\n"
            "  let t ← try some <$> (do\n"
            "      let e ← Meta.transform (← getConstInfo n).type (pre := fun e => do\n"
            "        if (← Meta.isProof e) then return .done (mkConst `proof) else return .continue)\n"
            "      let f ← withOptions (·.setBool `pp.all true) (ppExpr (challengeGenAnon e))\n"
            "      pure (f.pretty 100000)) catch _ => pure none\n"
            f"  IO.println s!\"@@@{key}@@@{{t.getD \"MISSING\"}}@@@END\"\n")


def listing(names):
    """Walks the file as Comparator does from `names`, the theorems to check: through the
    statements, the constructors of inductive types and the values of definitions, stopping at
    theorems to check and at imported constants. Prints each constant reached whose statement or
    value uses `sorry`, and each of `names` that is not a theorem of the file."""
    literals = ", ".join(json.dumps(n, ensure_ascii=False) for n in names)
    return f"""
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let listed : Array Name := #[{literals}].map String.toName
  for n in listed do
    unless (env.find? n).any (· matches .thmInfo _) do
      IO.println s!"@@@NOTTHM@@@{{n.toString (escape := false)}}@@@END"
  let mut seen : Std.HashSet Name := {{}}
  let mut todo := listed
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n || !env.constants.map₂.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let value := if listed.contains n then #[] else
      ((ci.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
    let used := ci.type.getUsedConstants ++ value
    if used.contains ``sorryAx then
      IO.println s!"@@@SORRY@@@{{n.toString (escape := false)}}@@@END"
    todo := todo ++ used
    match ci with
    | .inductInfo i => todo := todo ++ i.ctors.toArray
    | .ctorInfo c => todo := todo.push c.induct
    | _ => pure ()
"""


def types(output):
    return {m.group(1): m.group(2) for m in re.finditer(r"@@@(\d+)@@@(.*?)@@@END", output, re.S)
            if m.group(2) != "MISSING"}


def lean(path):
    return subprocess.run(["lake", "env", "lean", str(path)], cwd=project,
                          capture_output=True, text=True, timeout=1800)


reference = work / "Project.lean"
reference.write_text(f"import Lean\nimport {root}\n" + PRELUDE
                     + "".join(probe(i, name_of(p)) for i, p in enumerate(files)))
expected = types(lean(reference).stdout)


def check(indexed):
    key, path = indexed
    copy = work / path.name
    # The probe runs in `MetaM`: `Lean` is imported first, beside the file's own imports.
    text = path.read_text()
    assert text.startswith("module\n"), path
    listed = json.loads(path.with_suffix(".json").read_text())["theorem_names"]
    copy.write_text("module\n\npublic import Lean\n" + text[len("module\n"):] + PRELUDE
                    + probe(key, name_of(path)) + listing(listed))
    result = lean(copy)
    if result.returncode != 0:
        return path.name, "fail", result.stdout + result.stderr
    unlisted = re.findall(r"@@@SORRY@@@(.*?)@@@END", result.stdout)
    not_theorems = re.findall(r"@@@NOTTHM@@@(.*?)@@@END", result.stdout)
    if unlisted or not_theorems:
        return path.name, "UNLISTED", (f"  reached, uses sorry, not to be checked: {unlisted}\n"
                                       f"  to be checked, not a theorem: {not_theorems}\n")
    want = expected.get(str(key))
    if want is None:
        return path.name, "no-project", ""
    got = types(result.stdout).get(str(key))
    return (path.name, "same", "") if got == want else (
        path.name, "DIFFERS", f"  file:    {got}\n  project: {want}\n")


with cf.ThreadPoolExecutor(jobs) as pool:
    results = list(pool.map(check, enumerate(files)))
with open(work / "fidelity.txt", "w") as report:
    for name, status, detail in results:
        report.write(f"{status} {name}\n{detail}")
counts = collections.Counter(status for _, status, _ in results)
print(dict(counts))
sys.exit(1 if counts["DIFFERS"] or counts["UNLISTED"] or counts["fail"] else 0)
