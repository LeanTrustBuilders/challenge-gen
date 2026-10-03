#!/usr/bin/env python3
"""Compiles challenge files and compares each target's statement with the project's own.

Usage: test/fidelity.py PROJECT_DIR FILES_DIR ROOT_MODULE WORK_DIR [JOBS]

For each `<target>.lean` in FILES_DIR (as challenge-gen names them), compiles a copy with a probe
printing the target's elaborated type, under PROJECT_DIR's `lake env`, and compares that type with
the one printed in a file importing ROOT_MODULE (both also import `Lean`, for the probe). The types are compared as raw expressions, so
notation, `open`s and the printer play no part; only the names of hygienic binders are normalized,
since they carry their module. Private targets are skipped. Writes WORK_DIR/fidelity.txt and prints
a count of `same`, `DIFFERS`, `fail` (does not compile) and `no-project` (not found in the
project); exits with 1 if any file differs or fails.
"""
import collections
import concurrent.futures as cf
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


def probe(name):
    return ("\nopen Lean in\n#eval show CoreM Unit from do\n"
            f"  IO.println s!\"@@@{name}@@@{{(← getConstInfo `{name}).type}}@@@END\"\n")


def normalize(text):
    # `inst._@.<Module>.<hash>._hygCtx._hyg.5`: the module differs between a file and the project.
    return re.sub(r"\._@\.\S*?\.(\d+)\._hygCtx\._hyg\.(\d+)", r"✝\1.\2", text)


def types(output):
    return {m.group(1): normalize(m.group(2))
            for m in re.finditer(r"@@@(.*?)@@@(.*?)@@@END", output, re.S)}


def lean(path):
    return subprocess.run(["lake", "env", "lean", str(path)], cwd=project,
                          capture_output=True, text=True, timeout=1800)


reference = work / "Project.lean"
reference.write_text(f"import Lean\nimport {root}\n" + "".join(probe(name_of(p)) for p in files))
expected = types(lean(reference).stdout)


def check(path):
    copy = work / path.name
    # The probe runs in `CoreM`: `import Lean` goes first, beside the file's own imports.
    copy.write_text("import Lean\n" + path.read_text() + probe(name_of(path)))
    result = lean(copy)
    if result.returncode != 0:
        return path.name, "fail", result.stdout + result.stderr
    want = expected.get(name_of(path))
    if want is None:
        return path.name, "no-project", ""
    got = types(result.stdout).get(name_of(path))
    return (path.name, "same", "") if got == want else (
        path.name, "DIFFERS", f"  file:    {got}\n  project: {want}\n")


with cf.ThreadPoolExecutor(jobs) as pool:
    results = list(pool.map(check, files))
with open(work / "fidelity.txt", "w") as report:
    for name, status, detail in results:
        report.write(f"{status} {name}\n{detail}")
counts = collections.Counter(status for _, status, _ in results)
print(dict(counts))
sys.exit(1 if counts["DIFFERS"] or counts["fail"] else 0)
