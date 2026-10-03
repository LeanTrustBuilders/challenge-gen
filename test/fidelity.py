#!/usr/bin/env python3
"""Compiles challenge files and compares each target's statement with the project's own.

Usage: test/fidelity.py PROJECT_DIR FILES_DIR ROOT_MODULE WORK_DIR [JOBS]

For each `<target>.lean` in FILES_DIR (as challenge-gen names them), compiles a copy with a probe
printing the target's elaborated type, under PROJECT_DIR's `lake env`, and compares that type with
the one printed in a file importing ROOT_MODULE (both also import `Lean`, for the probe). Types are
printed with `pp.all`: every argument and universe explicit, no notation, and hygienic binders
numbered by position, so neither notation, `open`s nor binder names play a part. Private targets are
skipped. Writes WORK_DIR/fidelity.txt and prints a count of `same`, `DIFFERS`, `fail` (does not
compile) and `no-project` (not found in the project); exits with 1 if any file differs or fails.
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


def probe(key, name):
    # The name goes in as a string, decoded at run time, so that one that does not parse fails alone.
    literal = json.dumps("`" + name, ensure_ascii=False)
    return ("\nopen Lean Meta in\n#eval show MetaM Unit from do\n"
            f"  let n := (Syntax.decodeNameLit {literal}).getD .anonymous\n"
            "  let t ← try some <$> (do\n"
            "      let f ← withOptions (·.setBool `pp.all true) (ppExpr (← getConstInfo n).type)\n"
            "      pure (f.pretty 100000)) catch _ => pure none\n"
            f"  IO.println s!\"@@@{key}@@@{{t.getD \"MISSING\"}}@@@END\"\n")


def types(output):
    return {m.group(1): m.group(2) for m in re.finditer(r"@@@(\d+)@@@(.*?)@@@END", output, re.S)
            if m.group(2) != "MISSING"}


def lean(path):
    return subprocess.run(["lake", "env", "lean", str(path)], cwd=project,
                          capture_output=True, text=True, timeout=1800)


reference = work / "Project.lean"
reference.write_text(f"import Lean\nimport {root}\n"
                     + "".join(probe(i, name_of(p)) for i, p in enumerate(files)))
expected = types(lean(reference).stdout)


def check(indexed):
    key, path = indexed
    copy = work / path.name
    # The probe runs in `MetaM`: `import Lean` goes first, beside the file's own imports.
    copy.write_text("import Lean\n" + path.read_text() + probe(key, name_of(path)))
    result = lean(copy)
    if result.returncode != 0:
        return path.name, "fail", result.stdout + result.stderr
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
sys.exit(1 if counts["DIFFERS"] or counts["fail"] else 0)
