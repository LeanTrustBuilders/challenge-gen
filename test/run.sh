#!/usr/bin/env bash
# End-to-end test of challenge-gen on test/fixture.
#
# Builds the fixture, writes the file of every one of its declarations, compiles each file with
# `lake env lean` (every one must compile), and checks what a few of them hold. Then writes the
# file of one declaration only.
#
# Usage: test/run.sh [KEEP_DIR]   (after `lake build`)
#   With KEEP_DIR, the generated files are copied to KEEP_DIR.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/.." && pwd)
bin="$root/.lake/build/bin/challenge-gen"
[ -x "$bin" ] || { echo "build challenge-gen first: lake build" >&2; exit 1; }

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

# The fixture is built with ChallengeGen's toolchain, and the annotations package's release for it.
cp -r "$here/fixture" "$work/fixture"
cp "$root/lean-toolchain" "$work/fixture/lean-toolchain"
toolchain=$(sed 's/.*:v//' "$root/lean-toolchain" | tr -d '[:space:]')
sed -i "s/^rev = .*/rev = \"v$toolchain\"/" "$work/fixture/lakefile.toml"
(cd "$work/fixture" && lake build -q >/dev/null)

(cd "$work/fixture" && lake env "$bin" --root Fixture --out "$work/out")
count=$(find "$work/out" -name '*.lean' | wc -l)
[ "$count" -gt 0 ] || { echo "FAIL: no file written" >&2; exit 1; }

failed=0
for f in "$work/out"/*.lean; do
  if ! (cd "$work/fixture" && lake env lean "$f" > "$work/log" 2>&1); then
    echo "FAIL: $(basename "$f") does not compile:" >&2
    sed 's/^/  /' "$work/log" >&2
    failed=$((failed + 1))
  fi
done
[ "$failed" -eq 0 ] || { echo "FAIL: $failed of $count files do not compile" >&2; exit 1; }
echo "ok: the $count files compile"

python3 - "$work/out" <<'EOF'
import pathlib, sys
out = pathlib.Path(sys.argv[1])
def read(name):
    return (out / (name.replace(".", "___") + ".lean")).read_text()
def check(cond, msg):
    if not cond:
        sys.exit(f"FAIL: {msg}")

for f in out.glob("*.lean"):
    text = f.read_text()
    check("import TrustAnnotations" not in text, f"{f.name} imports TrustAnnotations")
    check("set_option autoImplicit false" in text and "set_option maxSynthPendingDepth 3" in text,
          f"{f.name}: an option the project is built with is not set")
    check("pp.unicode.fun" not in text and "linter.unusedVariables" not in text,
          f"{f.name}: an option that changes only what Lean reports is set")
    check("@[claim" not in text and "@[domain" not in text, f"{f.name} keeps an annotation")

claim = read("Fixture.pred'_lt")
check("theorem pred'_lt (n : Nat) (h : 0 < n) : pred' n < n := sorry" in claim,
      "pred'_lt: the proof is replaced by sorry")
check("def pred' (n : Nat) : Nat := n - 1" in claim, "pred'_lt: pred' is inlined")
check("helper" not in claim, "pred'_lt: a lemma its proof calls is inlined")
check(not claim.lstrip().startswith("import"), "pred'_lt: imports, with nothing outside Lean core")

check("instance : IsSmall 3" in read("Fixture.smallVal_three"),
      "smallVal_three: the instance its statement needs, a proof, is missing")

check("⟨1, sorry⟩" in read("Fixture.one"), "one: an embedded proof is kept")
check("def two : Nat := by exact 2" in read("Fixture.two"), "two: a tactic value is replaced")
box = read("Fixture.Box")
check("by exact 0" not in box and "size : Nat := sorry" in box,
      "Box: a field's tactic default is kept")
code = read("Fixture.Uses.Code")
check("deriving" not in code and "instance : BEq (Code) := sorry" in code,
      "Code: the deriving clause is not replaced by an instance")

quad = read("Fixture.Uses.quad")
check('notation:max "⟪" n "⟫" => double n' in quad, "quad: the notation it uses is not replayed")
check("def double" in quad, "quad: what the notation expands to is missing")
check("unrelated" not in quad and "double_pos" not in quad, "quad: an unrelated declaration is inlined")
check("box_val" not in quad, "quad: a declaration after it is inlined")

for name in ["Fixture.pick", "Fixture.pick'"]:
    text = read(name)
    check("noncomputable section" in text, f"{name}: its noncomputable section is lost")
    check("@[expose]" not in text and "public" not in text, f"{name}: the module system is kept")

local = read("Fixture.quad'")
check('local notation "⦃" n "⦄" => double (double n)' in local,
      "quad': the local notation it uses is not replayed")

app_eq = read("Fixture.Pair.app_eq")
check("variable (g : (Nat → Nat))" in app_eq, "Pair.app_eq: a binder holding parentheses is dropped")
check(app_eq.count("set_option autoImplicit false") == 1,
      "Pair.app_eq: its source's setting of an option already set at the top is kept")

check("def_with_eq seven : Nat := 7" in read("Fixture.seven_pos"),
      "seven_pos: a command declaring two constants at one position is lost")

check("include hn" in read("Fixture.Inc.pos_succ"), "pos_succ: its include is not replayed")
check("include b" not in read("Fixture.Inc.early") and "Big" not in read("Fixture.Inc.early"),
      "early: an include naming a binder left out is kept")

box_val = read("Fixture.Uses.box_val")
check("HasZero'" not in box_val, "box_val: a binder outside its closure is kept")
print("ok: proofs, values, annotations, notation, sections, binders, options and closures")
EOF

(cd "$work/fixture" && lake env "$bin" --root Fixture --decl Fixture.Uses.quad --out "$work/one" >/dev/null)
[ "$(ls "$work/one")" = "Fixture___Uses___quad.lean" ] || { echo "FAIL: --decl" >&2; ls "$work/one" >&2; exit 1; }
cmp -s "$work/one/Fixture___Uses___quad.lean" "$work/out/Fixture___Uses___quad.lean" ||
  { echo "FAIL: one declaration's file differs from the same file written with all" >&2; exit 1; }
echo "ok: --decl writes that declaration's file only, the same"

if [ $# -ge 1 ]; then mkdir -p "$1" && cp "$work/out"/*.lean "$1"/; fi
