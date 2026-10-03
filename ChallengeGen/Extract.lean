module

public import MeaningGraph
public import ChallengeGen.Basic
public import ChallengeGen.SourceSyntax

@[expose] public section

/-!
# Standalone Lean files from a project's source

This is an adaptation of Matthew Ballard's `EmitStandalone.lean`
(https://github.com/mattrobball/lean-informal/blob/main/Informal/EmitStandalone.lean).

It copies the **verbatim source text** of each declaration and replays the surrounding
`namespace`/`open`/`variable`/`section` context commands. Notation is therefore preserved exactly as
written, so the output is readable.

## Strategy

1. Re-elaborate each project source file against the already-loaded environment
   (`IO.processCommands`) to recover, per command, its `Syntax` and byte range.
2. Classify each command as a *declaration* (it defines a declaration of the project), a *context*
   command (`namespace`/`end`/`open`/`variable`/`section`/`set_option`/`universe`), or *skip*.
3. Extract each command's source text by byte position. For theorems, the proof body (`declVal`) is
   replaced by `:= sorry` surgically (the rest of the source is untouched).
4. Close each target under what its text needs: `MeaningGraph`'s statement dependencies for a
   declaration whose proof became `sorry`, its term dependencies for one kept whole, and in both
   cases its source dependencies, the notations its source uses and its command's siblings.
5. Per target, keep the context commands plus the declaration commands in that closure, drop
   now-empty sections, and assemble: external `import`s followed by the bodies in module-dependency
   order.

Each source file is processed **once** and cached; assembling a target then only filters and
concatenates strings.
-/

open Lean Lean.Elab Lean.Elab.Command Lean.Parser

namespace ChallengeGen

open MeaningGraph

/-! ## Classified commands -/

/-- How a source command relates to the set of exposed declarations. -/
inductive CmdClass where
  /-- Defines at least one exposed declaration. -/
  | decl
  /-- A `namespace`/`end`/`open`/`variable`/`section`/`set_option`/`universe`/`attribute` command. -/
  | context
  /-- Anything else (a non-exposed declaration, `#check`, …). -/
  | skip
  deriving Inhabited, BEq

/-- A classified source command: its source text (with proof already `sorry`-injected for theorems),
its `Syntax` kind, and the exposed declarations it defines (if any). -/
structure CommandEntry where
  cls : CmdClass
  src : String
  kind : SyntaxNodeKind
  declNames : Array Name := #[]
  /-- For a declaration command, whether its value is replaced by `sorry`: a proof with a value.
  What it needs is then what its statement needs (see `neededDeps`). -/
  valueDropped : Bool := false
  /-- For a `section` command, the command as replayed (`replayedSection`). -/
  sectionSrc? : Option String := none
  /-- For a `namespace`, `section` or `end` command, how many scopes it opens or closes: one per
  component of its name, one for an anonymous `section` or `end`. -/
  scopes : Nat := 1
  /-- For a `namespace` command, the namespace it opens exactly as spelled in the source (used by
  `activePrefixes` for `variable`-pruning; kept relative/possibly-unqualified on purpose, since
  that pruning logic is unaffected by whether a namespace was entered via its full dotted path or
  a name relative to an already-open ancestor). -/
  nsName? : Option Name := none
  /-- For a `namespace` command, the namespace it opens as a *fully qualified* name (i.e.
  including any enclosing `namespace`s it was nested inside), used only to emit existence stubs
  (`nsStubs` in `assembleTarget`). Two `namespace` commands for the same actual namespace, one
  spelled relative to an open ancestor and the other fully dotted, must be recognized as the same
  namespace here — otherwise the assembled file ends up with an extra empty stub for the relative
  spelling that is a distinct (and so ambiguous, once both are in scope) namespace from the real,
  populated one. -/
  qualifiedNsName? : Option Name := none
  /-- For a `variable` command, its binders decomposed as `(source text, identifiers referenced)`,
  so that binders mentioning declarations outside a target's closure can be dropped. -/
  binders : Array (String × Array String) := #[]
  /-- For an `open NS (a b c)` command (the explicit-list form, as opposed to a bare `open NS`),
  `NS` exactly as spelled in the source, and the listed identifiers (`a b c`). Used to drop names
  from the list (or the whole command, if none survive) that aren't part of a target's closure —
  keeping all of them unconditionally would otherwise reference a declaration that was dropped
  (or even `NS` itself, in a target where nothing causes `NS`, or a stub for it, to exist at all).
  `openOnlyIdents` is empty for every other form of `open` (and for every other command kind). -/
  openOnlyNamespace? : Option String := none
  openOnlyIdents : Array String := #[]
  /-- For a standalone `attribute [attrs] a b c` command, the names it targets (`a b c`), so it can
  be dropped when one of them is a project declaration this target does not emit. Empty for every
  other command. -/
  attrTargets : Array String := #[]
  /-- True when such a command applies a *translation* attribute (`to_additive`/`to_dual`). Only
  these are replayed; see `isContextCmd`. -/
  attrIsTranslation : Bool := false
  /-- Extra commands to emit right after this one — used for `instance … := sorry` replacements of a
  definition's `deriving` clause (which can't be re-derived in the minimal file). -/
  appended : Array String := #[]
  /-- For a declaration command, the exposed notation parsers whose syntax appears in its source. The
  notation's expansion (not the parser) is what shows up in the elaborated term, so this syntactic
  signal is the only way to know the verbatim source needs that notation command replayed. -/
  usedNotations : Array Name := #[]
  /-- For a declaration wrapped in `omit … in`, the omitted binders as `(source text, identifiers)`.
  These name `variable` binders, so they must be pruned in step with them: `entryKept` drops a
  binder referencing a declaration outside the target's closure, and an `omit` still naming it would
  then be an undefined reference. Empty for every other command. -/
  omitBinders : Array (String × Array String) := #[]
  /-- For such a declaration, its source with the `omit … in` prefix removed, so `pruneOmit` can
  re-render the prefix (or drop it entirely) without re-deriving the body. -/
  srcNoOmit? : Option String := none
  deriving Inhabited

/-! ## Excluded upstream -/

/-- External modules left out of an extracted file's import block even when the project imports them.

`TrustAnnotations` is the only one. It provides the annotation attributes (`annotationAttributes`)
and nothing a formalization refers to: each records something for a reading tool to pick back out
of the environment, and an extraction of one declaration has nothing to say with them. So the
annotations are stripped (`isDroppedAttribute`) along with any option they are tuned by
(`excludedOptions`), and then the import has nothing left to serve. A file that does not import it
compiles wherever the project's other dependencies are available, Mathlib's web editor included.

The cost is a project that mentions a `TrustAnnotations` *constant* in a declaration this tool
extracts — a tool reading annotations, not a formalization writing them. Such a declaration loses
the import it needs. -/
def excludedImports : Array Name := #[`TrustAnnotations]

@[inherit_doc excludedImports]
def isExcludedImport (m : Name) : Bool := excludedImports.any (hasPrefixName m ·)

/-- Option namespaces registered by an `excludedImports` module. A `set_option` naming one of these
is an `unknown option` error once the import is gone, so both forms — the file-level command and the
`set_option … in <decl>` prefix — are dropped from the extracted file. `specifies` and
`characterization` cover the options `TrustAnnotations` registers
(`specifies.checkTargetMentioned`, `characterization.checkExistence`,
`characterization.checkNotCircular`). -/
def excludedOptions : Array Name := #[`specifies, `characterization]

@[inherit_doc excludedOptions]
def isExcludedOption (o : Name) : Bool := excludedOptions.any (hasPrefixName o ·)

/-- The option a `set_option` command sets and the value it sets it to, read from its source text:
the token after the keyword, and the rest normalized to single-space-separated tokens (so two
spellings of the same setting compare equal). Used for the file-level form, where the command
survives as a context command rather than as part of a declaration's source. -/
def setOptionSetting? (src : String) : Option (Name × String) :=
  let toks := (src.split fun c => c == ' ' || c == '\n' || c == '\t' || c == '\r').toArray
    |>.filterMap fun w =>
      let w := w.trimAscii.toString
      if w.isEmpty then none else some w
  if toks[0]? == some "set_option" then
    toks[1]?.map fun n => (n.toName, " ".intercalate (toks.toList.drop 2))
  else none

@[inherit_doc setOptionSetting?]
def setOptionName? (src : String) : Option Name := (setOptionSetting? src).map (·.1)

/-! ## Syntax inspection -/

/-- The `declVal` syntax node of a declaration (`:= …`, `| … => …`, or `where …`), if present. -/
partial def findDeclValStx? (root : Syntax) : Option Syntax := Id.run do
  let mut worklist : Array Syntax := #[root]
  while !worklist.isEmpty do
    let stx := worklist.back!
    worklist := worklist.pop
    let k := stx.getKind
    if k == ``Parser.Command.declValSimple || k == ``Parser.Command.declValEqns
        || k == ``Parser.Command.whereStructInst then
      return some stx
    unless isQuotation stx do
      for arg in stx.getArgs do
        worklist := worklist.push arg
  return none

/-- The byte range of the *value*/proof part of a declaration, if present. -/
def findDeclVal? (root : Syntax) : Option (String.Pos.Raw × String.Pos.Raw) := do
  let v ← findDeclValStx? root
  match v.getPos?, v.getTailPos? with
  | some s, some e => some (s, e)
  | _, _ => none

/-- True if `stx` declares a `theorem` or `lemma`, whose proof we replace by `sorry`.

`theorem` parses as `Command.declaration` with the keyword node `Command.theorem`; a `lemma` keeps
its own syntax kind until macro expansion. Which kinds count is `theoremSyntaxKinds`: a Batteries `lemma`
counts as much as Mathlib's. -/
def isTheoremDecl (stx : Syntax) : Bool := containsSyntaxKind stx theoremSyntaxKinds

/-- True if `stx` declares a `structure` or a `class` (both parse as `Command.structure`, which
begins with either `structureTk` or `classTk`). -/
def isStructureDecl (stx : Syntax) : Bool := containsSyntaxKind stx structureSyntaxKinds

/-- The byte ranges of the outermost `by …` tactic blocks inside `root` (not recursing into a block
already collected). Used to replace embedded proofs in a *definition's* value with `sorry`. -/
partial def collectByBlocks (root : Syntax) : Array (String.Pos.Raw × String.Pos.Raw) := Id.run do
  let mut acc : Array (String.Pos.Raw × String.Pos.Raw) := #[]
  let mut worklist : Array Syntax := #[root]
  while !worklist.isEmpty do
    let stx := worklist.back!
    worklist := worklist.pop
    if stx.getKind == ``Lean.Parser.Term.byTactic then
      match stx.getPos?, stx.getTailPos? with
      | some s, some e => acc := acc.push (s, e)   -- don't descend into a block we'll replace
      | _, _ => for arg in stx.getArgs do worklist := worklist.push arg
    else if !isQuotation stx then
      for arg in stx.getArgs do
        worklist := worklist.push arg
  return acc

/-- The byte ranges of `by …` blocks that constitute the *entire* value of something — either a
definition's value (`def f … := by tac`) or one structure-instance field (`… where fld := by tac`,
and the `{ fld := by tac }` spelling). Such a block is a direct child of `declValSimple` or of
`Term.structInstFieldDef`; a proof embedded inside a larger term sits deeper.

These must be kept rather than replaced by `sorry`, because for a **definition** Lean decides which
section `variable`s to include from what the value actually mentions, and `sorry` mentions nothing.
Both shapes were observed losing binders and so silently changing a signature:

* `def leftLimWithin (f : α → β) (s : Set α) (a : α) : β := by classical …` under
  `variable {α β : Type*} [LinearOrder α] [TopologicalSpace β]` dropped both instances, breaking
  every use site that passes them positionally (`@leftLimWithin αᵒᵈ β _ _ f s a`);
* `def ofSeq : MartDiffArray P where … mgdiff n i := by …` dropped the `hmgdiff` binder, so
  `ofSeq` shed an argument and every call misaligned.

Sparing only these two shapes is deliberate. Keeping *every* tactic block in a definition was
measured and is far worse: it takes brownian-motion from 2 failures to 71, because a proof embedded
in a larger term generally cannot run in the minimal file, which does not replay the `@[simp]` /
`@[measurability]` registrations it depends on. -/
partial def wholeValueTacticRanges (root : Syntax) : Array (String.Pos.Raw × String.Pos.Raw) :=
  Id.run do
  let mut acc : Array (String.Pos.Raw × String.Pos.Raw) := #[]
  let mut worklist : Array Syntax := #[root]
  while !worklist.isEmpty do
    let stx := worklist.back!
    worklist := worklist.pop
    let k := stx.getKind
    if k == ``Parser.Command.declValSimple || k == ``Lean.Parser.Term.structInstFieldDef then
      for a in stx.getArgs do
        if a.getKind == ``Lean.Parser.Term.byTactic then
          match a.getPos?, a.getTailPos? with
          | some s, some e => acc := acc.push (s, e)
          | _, _ => pure ()
    unless isQuotation stx do
      for a in stx.getArgs do
        worklist := worklist.push a
  return acc

/-- The byte ranges of the `binderTactic` nodes inside `root`, i.e. binder/field defaults written
`:= by tac`.

A default is **not** a `Term.byTactic` node, so a walk looking for those never finds it. Its parser
is `atomic (symbol " := " >> " by ") >> tacticSeq`, meaning the node's range covers the ` := by `
prefix as well as the tactic block — a replacement
therefore has to supply the `:=` itself. -/
partial def collectBinderTactics (root : Syntax) : Array (String.Pos.Raw × String.Pos.Raw) :=
  Id.run do
  let mut acc : Array (String.Pos.Raw × String.Pos.Raw) := #[]
  let mut worklist : Array Syntax := #[root]
  while !worklist.isEmpty do
    let stx := worklist.back!
    worklist := worklist.pop
    if stx.getKind == ``Lean.Parser.Term.binderTactic then
      match stx.getPos?, stx.getTailPos? with
      | some s, some e => acc := acc.push (s, e)   -- don't descend into a block we'll replace
      | _, _ => for arg in stx.getArgs do worklist := worklist.push arg
    else if !isQuotation stx then
      for arg in stx.getArgs do
        worklist := worklist.push arg
  return acc

/-- Every `SyntaxNodeKind` occurring anywhere in `stx` (including `stx` itself). A notation use shows
up here as a node whose kind is the notation parser's name. Quotations are entered, unlike in the
other walks: a quotation's text is parsed with the notations it uses. -/
partial def collectSyntaxKinds (stx : Syntax) : Std.HashSet Name := Id.run do
  let mut acc : Std.HashSet Name := {}
  let mut worklist : Array Syntax := #[stx]
  while !worklist.isEmpty do
    let s := worklist.back!
    worklist := worklist.pop
    acc := acc.insert s.getKind
    for arg in s.getArgs do
      worklist := worklist.push arg
  return acc

/-- True for the notation/syntax-defining commands (needed to parse declarations that use them). -/
def isNotationCmd (k : SyntaxNodeKind) : Bool :=
  k == ``Parser.Command.«notation» || k == ``Parser.Command.«mixfix»
    || k == ``Parser.Command.«macro» || k == ``Parser.Command.«macro_rules»
    || k == ``Parser.Command.«syntax» || k == ``Parser.Command.«elab»

/-- True for the context-management commands we replay verbatim: scoping commands plus the
notation/syntax-defining commands needed to parse the declarations that use them. -/
def isContextCmd (stx : Syntax) : Bool :=
  let k := stx.getKind
  k == ``Parser.Command.namespace || k == ``Parser.Command.«end» || k == ``Parser.Command.«open»
    || k == ``Parser.Command.«variable» || k == ``Parser.Command.«section»
    || k == ``Parser.Command.«set_option» || k == ``Parser.Command.«universe»
    -- `include x` adds the variable `x` to every theorem after it, and `omit` takes one out: lost,
    -- either changes the statements that follow.
    || k == ``Parser.Command.«include» || k == ``Parser.Command.«omit»
    -- A standalone `attribute [...] X` is a *side effect* on `X` rather than a declaration, so
    -- dropping it silently loses whatever it registered. Classified as context here so it can be
    -- considered; `assembleTarget` then replays only the ones carrying a `translationAttributes`
    -- entry, which are the ones whose loss makes *other* declarations fail to elaborate.
    || k == ``Parser.Command.«attribute»
    || isNotationCmd k

/-- The substring of `source` between two byte positions. -/
def slice (source : String) (s e : String.Pos.Raw) : String :=
  ({ str := source, startPos := s, stopPos := e } : Substring.Raw).toString

/-- The first identifier in `stx`, depth first. -/
partial def findFirstIdent? (stx : Syntax) : Option Syntax :=
  if stx.isIdent then some stx else stx.getArgs.findSome? findFirstIdent?

/-- A `section` command as it is replayed: `noncomputable` and the section's name kept, the module
system's `@[expose]`, `public` and `meta` dropped, since an extracted file is not a module.

`noncomputable` has to stay: a definition relying on it (`Classical.choice`, real division) does
not compile without it. The header is read from the source text before the `section` keyword, the
name from the parsed syntax (`sectionHeader "section" (ident)?`). -/
def replayedSection (source : String) (stx : Syntax) : String :=
  let header := match stx.getPos?, stx[1].getPos? with
    | some s, some e => slice source s e
    | _, _ => ""
  let noncomputable_ := (header.splitOn "noncomputable").length > 1
  let name := match stx[2].getOptional? with
    | some id => s!" {id.getId}"
    | none => ""
  (if noncomputable_ then "noncomputable " else "") ++ "section" ++ name

/-- The source `[cmdStart, cmdEnd)` with each edit applied: `(s, e, repl)` replaces the byte range
`[s, e)` with `repl`; a zero-width range (`s == e`) is an insertion. Edits must be non-overlapping. -/
def applyEdits (source : String) (cmdStart cmdEnd : String.Pos.Raw)
    (edits : Array (String.Pos.Raw × String.Pos.Raw × String)) : String := Id.run do
  if edits.isEmpty then return slice source cmdStart cmdEnd
  let sorted := edits.qsort (fun a b => a.1.byteIdx < b.1.byteIdx)
  let mut out := ""
  let mut cursor := cmdStart
  for (s, e, repl) in sorted do
    out := out ++ slice source cursor s ++ repl
    cursor := e
  return out ++ slice source cursor cmdEnd

/-- Information needed to replace a definition's `deriving …` clause with `sorry` instances:
the byte position where the `deriving` keyword starts (everything from here is dropped), and the
generated `instance … := sorry` commands (one per derived class). Returns `none` if the command has
no `deriving` clause or its shape can't be reconstructed (in which case it is left verbatim). -/
def derivingReplacement? (source : String) (stx : Syntax) (cmdEnd : String.Pos.Raw) :
    Option (String.Pos.Raw × Array String) := Id.run do
  -- Only `def` deriving causes the delta-derivation failures; structures derive fine.
  let some defNode := findFirstOfKind? stx ``Parser.Command.definition | return none
  -- The `deriving` keyword atom inside the definition.
  let some derivingAtom := Id.run (do
    let mut wl : Array Syntax := #[defNode]
    while !wl.isEmpty do
      let s := wl.back!; wl := wl.pop
      match s with
      | .atom _ "deriving" => return some s
      | _ => unless isQuotation s do for a in s.getArgs do wl := wl.push a
    return none) | return none
  let some dpos := derivingAtom.getPos? | return none
  let some dtail := derivingAtom.getTailPos? | return none
  -- Class names: the text after `deriving`, comma-separated.
  let classes := (slice source dtail cmdEnd).splitOn "," |>.filterMap (fun c =>
    let c := c.trimAscii.toString
    if c.isEmpty then none else some c)
  if classes.isEmpty then return none
  -- The declaration name and its binders.
  let some declId := findFirstOfKind? defNode ``Parser.Command.declId | return none
  let some idPos := declId.getPos? | return none
  let some idTail := declId.getTailPos? | return none
  let defName := slice source idPos idTail
  let some sig := findFirstOfKind? defNode ``Parser.Command.optDeclSig | return none
  let binderNodes := if sig.getArgs.size ≥ 1 then sig[0].getArgs else #[]
  let mut bindersText := ""
  let mut applyNames : Array String := #[]
  for b in binderNodes do
    match b.getPos?, b.getTailPos? with
    | some s, some e =>
      let btxt := slice source s e
      bindersText := if bindersText.isEmpty then btxt else bindersText ++ " " ++ btxt
      -- Explicit binders (and bare `binderIdent`s) are applied positionally; the rest are inferred.
      if b.getKind == ``Lean.Parser.Term.explicitBinder then
        let before := ((btxt.splitOn ":").headD btxt).replace "(" " " |>.replace ")" " "
        for nm in before.splitOn " " do
          let nm := nm.trimAscii.toString
          unless nm.isEmpty do applyNames := applyNames.push nm
      else if b.isIdent then
        applyNames := applyNames.push b.getId.toString
    | _, _ => return none
  let app := " ".intercalate (defName :: applyNames.toList)
  let bindersClause := if bindersText.isEmpty then "" else " " ++ bindersText
  let instances := classes.map fun c => s!"instance{bindersClause} : {c} ({app}) := sorry"
  return some (dpos, instances.toArray)

/-- Every identifier appearing anywhere in `stx`, as strings.

Identifiers with an anonymous name are not counted: every parenthesis carries one, in the
`hygieneInfo` node of its `hygienicLParen`. Counted, it would resolve against every namespace in
scope to the namespace itself, and so name the declaration of that name (a structure whose namespace
the file is in), dropping every `variable` binder with a parenthesis in it whenever that declaration
is left out. -/
partial def collectIdents (stx : Syntax) : Array String := Id.run do
  let mut acc : Array String := #[]
  let mut worklist : Array Syntax := #[stx]
  while !worklist.isEmpty do
    let s := worklist.back!
    worklist := worklist.pop
    if s.isIdent && !s.getId.isAnonymous then acc := acc.push s.getId.toString
    for a in s.getArgs do
      worklist := worklist.push a
  return acc

/-- Decomposes a `variable` command into its individual binders, each as `(source text, identifiers
referenced)`. The binders are the children of the `many1` node following the `variable` keyword. -/
def decomposeVariable (source : String) (stx : Syntax) : Array (String × Array String) := Id.run do
  let binderNodes := if stx.getArgs.size ≥ 2 then stx[1].getArgs else #[]
  let mut res : Array (String × Array String) := #[]
  for b in binderNodes do
    match b.getPos?, b.getTailPos? with
    | some s, some e => res := res.push (slice source s e, collectIdents b)
    | _, _ => pure ()
  return res

/-- The local names a `variable` binder introduces, parsed from its source text: the identifiers
before the first `:` (so `(a b : T)` / `{a b : T}` / `[inst : T]` give `a b` / `inst`), or — when
there is no `:` and it is not an instance binder — every identifier (so `{a b}` gives `a b`). These
names are locally bound; they must not be mistaken for global declarations that happen to share them
(e.g. a binder `{Ω : Type*}` when the project also defines a top-level `abbrev Ω`). -/
def binderBoundNames (binderSrc : String) : Array String :=
  let s := binderSrc.trimAsciiStart.toString
  let isInst := s.startsWith "["
  let beforeColon :=
    match s.splitOn ":" with
    | [whole] => if isInst then "" else whole   -- no `:` separator
    | head :: _ => head
    | [] => ""
  let isSep (c : Char) : Bool :=
    c == ' ' || c == '(' || c == ')' || c == '{' || c == '}' || c == '[' || c == ']'
      || c == '⦃' || c == '⦄' || c == ','
  (beforeColon.split isSep).toArray.filterMap fun w =>
    let w := w.trimAscii.toString
    if w.isEmpty then none else some w

/-- The head symbol of a `variable` binder's type, as spelled in the source: for
`{𝓕 : Filtration ι mΩ}` this is `Filtration`. `none` when the binder has no `:` separator or its
type does not start with an identifier.

Used to resolve *generalized field notation* written on a bound name: `𝓕.IsComplete` denotes
`Filtration.IsComplete`, a spelling in which the referenced declaration's own name never literally
appears. -/
def binderTypeHead? (binderSrc : String) : Option Name :=
  let s := binderSrc.trimAsciiStart.toString
  match s.splitOn ":" with
  | _ :: rest@(_ :: _) =>
    let afterColon := String.intercalate ":" rest
    let isSep (c : Char) : Bool :=
      c == ' ' || c == '(' || c == ')' || c == '{' || c == '}' || c == '[' || c == ']'
        || c == '⦃' || c == '⦄' || c == ',' || c == '→'
    let toks := (afterColon.split isSep).toArray.filterMap fun w =>
      let w := w.trimAscii.toString
      if w.isEmpty then none else some w
    toks[0]?.map (·.toName)
  | _ => none

/-- The attributes of `TrustAnnotations`: `@[claim]`, `@[specifies]`, `@[characterization]`,
`@[example_of]`, `@[nonexample_of]`, `@[domain]` and `@[up_to]`. Each records something for a
reading tool and changes nothing a later declaration elaborates against. -/
def annotationAttributes : List String :=
  ["claim", "specifies", "characterization", "example_of", "nonexample_of", "domain", "up_to"]

/-- True if this attribute must be dropped from an extracted declaration, given `attrSrc`, the
source text of a single attribute inside an `@[…]` group.

Two cases:

* `@[ext]` on a *theorem*: it generates the converse of the ext lemma **and proves it**, which needs
  the `@[refl]` lemma of the relation in the statement (for `f ≡ᵐ[μ] g`, that is
  `Indistinguishable.refl`). Since that dependency runs through an attribute rather than through any
  term, it is invisible to the dependency analysis and the lemma is not in the closure. Registering
  the lemma for the `ext` tactic is of no use in a file whose proofs are all `sorry`.
* The `annotationAttributes`: their only effect is to record something for a reading tool to pick
  back out, which says nothing in a one-declaration file — a characterization's parts are separate
  declarations, so an extraction of any one of them has at most a part of the claim. Dropping them
  is what lets `excludedImports` leave the `TrustAnnotations` import out of the header — the two go
  together, since an unimported attribute is a hard error.

Three near neighbours are deliberately **kept**, each because it *produces* something the rest of
the file may depend on rather than merely registering one:

* `@[ext]` on a `structure`/`class` (hence the `onStructure` guard) is what defines `Foo.ext` and
  `Foo.ext_iff` in the first place; only the theorem form is inert.
* plain `@[to_additive]` generates the additive sibling — the very thing the command siblings in
  `writeChallenges` work to keep elaborable.
* `@[to_additive existing]` looks inert (it links to a counterpart declared elsewhere rather than
  generating one) but is not: the link it registers is what lets *later* plain `@[to_additive]`
  commands translate a type mentioning the multiplicative declaration. Dropping it was measured to
  turn 5 failures into 339 on the brownian-motion corpus, every one of them a downstream
  `to_additive` translation that could no longer map `Monoid γ` to `AddMonoid γ`.

Matching is on the attribute's own leading token, so the `local`/`scoped` kind prefix — part of the
source text of the attribute, not of the `@[…]` group — is skipped first. -/
def isDroppedAttribute (onStructure : Bool) (attrSrc : String) : Bool :=
  let toks := (attrSrc.split fun c => c == ' ' || c == '\n' || c == '\t' || c == '\r').toArray
    |>.filterMap fun w =>
      let w := w.trimAscii.toString
      if w.isEmpty then none else some w
  let toks := if toks[0]? == some "local" || toks[0]? == some "scoped" then toks.drop 1 else toks
  match toks[0]? with
  | some "ext" => !onStructure
  | some t => annotationAttributes.contains t
  | none => false

/-- The position after the whitespace that starts at `p` in `source`. -/
def skipWhitespace (source : String) (p : String.Pos.Raw) : String.Pos.Raw := Id.run do
  let mut p := p
  while p.byteIdx < source.utf8ByteSize && (p.get source).isWhitespace do
    p := p.next source
  return p

/-- Source edits dropping every `isDroppedAttribute` from the `@[…]` groups in `root`. A group is
re-rendered from the attributes that survive, or removed outright, with the whitespace after it,
when none do. -/
partial def attributeStripEdits (source : String) (root : Syntax) (onStructure : Bool) :
    Array (String.Pos.Raw × String.Pos.Raw × String) := Id.run do
  let mut acc : Array (String.Pos.Raw × String.Pos.Raw × String) := #[]
  let mut worklist : Array Syntax := #[root]
  while !worklist.isEmpty do
    let stx := worklist.back!
    worklist := worklist.pop
    if stx.getKind == ``Lean.Parser.Term.attributes then
      match stx.getPos?, stx.getTailPos? with
      | some s, some e =>
        let instances := (if stx.getArgs.size ≥ 2 then stx[1].getArgs else #[]).filter
          (·.getKind == ``Lean.Parser.Term.attrInstance)
        let texts := instances.filterMap fun i =>
          match i.getPos?, i.getTailPos? with
          | some is, some ie => some (slice source is ie)
          | _, _ => none
        let kept := texts.filter (!isDroppedAttribute onStructure ·)
        if kept.size != texts.size then
          if kept.isEmpty then
            acc := acc.push (s, skipWhitespace source e, "")
          else
            acc := acc.push (s, e, "@[" ++ ", ".intercalate kept.toList ++ "]")
      | _, _ => pure ()
    else if !isQuotation stx then
      for a in stx.getArgs do
        worklist := worklist.push a
  return acc

/-- Source edits dropping every `set_option <excluded> <value> in` prefix in `root`, `<excluded>`
being an `isExcludedOption` name — an option whose registering package the extracted file does not
import, hence an `unknown option` error if left in.

`opt val in <decl>` parses as `Command.in` with the `set_option` as its first child and the ` in`
token as its second, so the range from the node's start to that token's end is exactly the prefix.
The wrapped declaration keeps its own position, so this composes with the other edits. -/
partial def setOptionStripEdits (root : Syntax) :
    Array (String.Pos.Raw × String.Pos.Raw × String) := Id.run do
  let mut acc : Array (String.Pos.Raw × String.Pos.Raw × String) := #[]
  let mut worklist : Array Syntax := #[root]
  while !worklist.isEmpty do
    let stx := worklist.back!
    worklist := worklist.pop
    if stx.getKind == ``Parser.Command.in && stx.getArgs.size ≥ 3
        && stx[0].getKind == ``Parser.Command.«set_option» && stx[0].getArgs.size ≥ 2
        && isExcludedOption stx[0][1].getId then
      match stx.getPos?, stx[1].getTailPos? with
      | some s, some e => acc := acc.push (s, e, "")
      | _, _ => pure ()
    unless isQuotation stx do
      for a in stx.getArgs do
        worklist := worklist.push a
  return acc

/-- Attributes that register a *translation* between a declaration and its multiplicative/additive
or order-dual counterpart. A standalone `attribute [to_dual existing] MeasurableInf₂` is what
teaches `to_dual` the `MeasurableSup₂ ↦ MeasurableInf₂` pairing; without it, later `@[to_dual]`
commands translate that class to itself and emit an ill-typed statement.

Only these are replayed. Other standalone `attribute` commands (`@[simp]`, `@[fun_prop]`,
`@[measurability]`, …) affect *proof* elaboration, which is moot in a file whose proofs are all
`sorry`, and replaying them was measured to be actively harmful: pulling in the module that carries
them made every brownian-motion target include declarations it did not need, taking that corpus
from 2 failures to 1623. -/
def translationAttributes : List String := ["to_additive", "to_dual"]

/-- For a standalone `attribute [attrs] a b c` command, the attributes as written and the names they
target. The parser is `"attribute " "[" sepBy1 (eraseAttr <|> attrInstance) ", " "]" many1 ident`,
so the attributes are the children of `stx[2]` and the targets those of `stx[4]`. -/
def decomposeAttributeCmd? (source : String) (stx : Syntax) :
    Option (Array String × Array String) := do
  guard (stx.getKind == ``Parser.Command.«attribute» && stx.getArgs.size ≥ 5)
  let attrs := stx[2].getArgs.filterMap fun a =>
    if a.isAtom then none
    else match a.getPos?, a.getTailPos? with
      | some s, some e => some (slice source s e)
      | _, _ => none
  let targets := stx[4].getArgs.filterMap fun i =>
    if i.isIdent then some i.getId.toString else none
  pure (attrs, targets)

/-- True if `attrSrc` (one attribute inside an `attribute`/`@[…]` list) is a `translationAttributes`
entry, matched on its leading token so `to_dual existing` and `to_additive (attr := …)` both hit. -/
def isTranslationAttribute (attrSrc : String) : Bool :=
  let toks := (attrSrc.split fun c => c == ' ' || c == '\n' || c == '\t' || c == '\r').toArray
    |>.filterMap fun w =>
      let w := w.trimAscii.toString
      if w.isEmpty then none else some w
  match toks[0]? with
  | some t => translationAttributes.contains t
  | none => false

/-- For a declaration wrapped in `omit … in`, its omitted binders as `(source text, identifiers
referenced)` together with the byte position where the wrapped declaration itself starts.

`omit … in <decl>` parses as `Command.in` with the `Command.omit` as its first child, so the
binders are the children of that command's `many1` node — the same shape `decomposeVariable`
handles for `variable`. -/
def decomposeOmit? (source : String) (stx : Syntax) :
    Option (Array (String × Array String) × String.Pos.Raw) := do
  guard (stx.getKind == ``Parser.Command.in && stx.getArgs.size ≥ 3)
  let om := stx[0]
  guard (om.getKind == ``Parser.Command.omit && om.getArgs.size ≥ 2)
  let innerStart ← stx[2].getPos?
  let binders := om[1].getArgs.filterMap fun b =>
    match b.getPos?, b.getTailPos? with
    | some s, some e => some (slice source s e, collectIdents b)
    | _, _ => none
  pure (binders, innerStart)

/-! ## Phase 1: process one source file -/

/-- Classifies every command of `source`, parsed as `commands` (`parseCommands`). `declPos`
maps the byte index where exposed declarations' ranges start to their names (so a command is a
declaration command iff some such position falls inside it). `notationKinds` maps the syntax kind of
each exposed notation, read without the prefix of a private name, to its declaration. -/
def processFile (env : Environment) (source : String) (commands : Array Syntax)
    (declPos : Std.HashMap Nat (Array Name)) (notationKinds : Std.HashMap Name Name) :
    IO (Array CommandEntry) := do
  let mut entries : Array CommandEntry := #[]
  -- Stack of the fully-qualified namespace prefix in effect *after* each currently-open
  -- `namespace`/`section` frame, so a `namespace` command nested inside another (rather than
  -- spelled with the full dotted path) still gets its true fully-qualified name as `nsName?`
  -- below — e.g. `namespace Learning` then later `namespace IsBayesAlgEnvSeq` must record
  -- `Learning.IsBayesAlgEnvSeq`, the same name a single `namespace Learning.IsBayesAlgEnvSeq`
  -- command would record, since both spellings denote the same namespace. Without this, the two
  -- spellings are treated as unrelated namespaces, and the assembled file ends up with both an
  -- empty stub for the bare name and the real (populated) one for the qualified name, which can
  -- make an unqualified reference to a member of the real one ambiguous.
  let mut nsPrefixStack : Array Name := #[Name.anonymous]
  -- The `end` commands closing the scopes open so far, innermost last. A file may leave scopes open
  -- at its end — `noncomputable section` at the top of a file, with no `end`, is the usual case — and
  -- each one is closed after the file's last command, so that every module's commands are balanced
  -- in the extracted file. Otherwise the scope would swallow the `end` of the `section` each module
  -- is wrapped in, and everything after it would sit in that module's scope.
  let mut closers : Array String := #[]
  for stx in commands do
    let some cmdStart := stx.getPos? | continue
    let some cmdEnd := stx.getTailPos? | continue
    -- Which exposed declarations does this command define?
    let mut names : Array Name := #[]
    for (pos, declared) in declPos do
      if pos ≥ cmdStart.byteIdx && pos < cmdEnd.byteIdx then
        names := names ++ declared
    if !names.isEmpty then
      -- A proof: a theorem or lemma, or a command all of whose declarations are theorems, such as an
      -- `instance` of a `Prop`-valued class. Its value is replaced by `sorry` whole; Lean decides
      -- which section variables a theorem takes from its statement alone, so this cannot change
      -- its signature, and no tactic of it has to run in the extracted file.
      let isProof := isTheoremDecl stx ||
        names.all fun n => (env.find? n).any (· matches .thmInfo _)
      -- Proofs: replace the whole value with `sorry`. Definitions: keep the value verbatim but
      -- replace any embedded `by …` tactic proofs in it with `sorry`, and turn a `deriving` clause
      -- into standalone `instance … := sorry` (it can't be delta-derived in the minimal file).
      let (declEnd, appended) :=
        if isProof then (cmdEnd, #[])
        else match derivingReplacement? source stx cmdEnd with
          | some (dpos, instances) => (dpos, instances)
          | none => (cmdEnd, #[])
      -- Attributes whose elaboration reaches outside this file are dropped from every declaration
      -- command, theorem or not (see `isDroppedAttribute`), as is any `set_option … in` prefix
      -- naming an option the extracted file's imports no longer register (see `excludedOptions`).
      let prefixEdits :=
        attributeStripEdits source stx (isStructureDecl stx) ++ setOptionStripEdits stx
      -- Renders the command from `start`, which is either the command's own start or — for a
      -- declaration wrapped in `omit … in` — the start of the wrapped declaration, so that
      -- `pruneOmit` can re-render the prefix per target. Edits before `start` are irrelevant to
      -- that slice and are dropped, since `applyEdits` reads its edits in position order.
      let mkSrc (start : String.Pos.Raw) : String :=
        let prefixEdits := prefixEdits.filter fun (r : String.Pos.Raw × String.Pos.Raw × String) =>
          r.1.byteIdx ≥ start.byteIdx
        if isProof then
          match findDeclVal? stx with
          | some (valStart, _) => applyEdits source start valStart prefixEdits ++ ":= sorry"
          | none => applyEdits source start cmdEnd prefixEdits
        else
          let edits :=
            if isStructureDecl stx then
              -- A structure/class field's default value (`field : T := by tac`) is a
              -- `Term.binderTactic` in the `structFields` node — neither a `Term.byTactic` nor
              -- part of any `declVal`, so the scan below never sees it and the tactic is emitted
              -- verbatim. It then has to run inside the minimal file, where the lemma sets it
              -- relies on (`measurability`, `fun_prop`, …) are not populated, and every
              -- construction of the structure that omits the field fails with "could not
              -- synthesize default value for field". `binderTactic` spans its own ` := by `, so
              -- the replacement has to restore the `:=`.
              (collectBinderTactics stx).map fun (bs, be) => (bs, be, ":= sorry")
            else
              let byBlocks := match findDeclValStx? stx with
                | some v => collectByBlocks v
                | none => #[]
              -- Keep the blocks that *are* a value rather than sitting inside one: replacing those
              -- would drop the `variable` binders the body mentions and change the declaration's
              -- signature. See `wholeValueTacticRanges`.
              let spared := wholeValueTacticRanges stx
              let byBlocks := byBlocks.filter fun (r : String.Pos.Raw × String.Pos.Raw) =>
                !spared.any fun (s : String.Pos.Raw × String.Pos.Raw) =>
                  s.1.byteIdx == r.1.byteIdx && s.2.byteIdx == r.2.byteIdx
              byBlocks.map fun (bs, be) => (bs, be, "sorry")
          applyEdits source start declEnd (prefixEdits ++ edits)
      let src := mkSrc cmdStart
      let (omitBinders, srcNoOmit?) :=
        match decomposeOmit? source stx with
        | some (binders, innerStart) => (binders, some (mkSrc innerStart))
        | none => (#[], none)
      let usedNotations := (collectSyntaxKinds stx).toArray.filterMap fun k =>
        notationKinds.get? (privateToUserName k)
      let valueDropped := isProof && (findDeclVal? stx).isSome
      entries := entries.push
        { cls := .decl, src, kind := stx.getKind, declNames := names, valueDropped, appended,
          usedNotations, omitBinders, srcNoOmit? }
    else if isContextCmd stx then
      let kind := stx.getKind
      let nsName? := if kind == ``Parser.Command.namespace && stx.getArgs.size ≥ 2 then
        some stx[1].getId else none
      let qualifiedNsName? := nsName?.map (nsPrefixStack.back! ++ ·)
      let sectionSrc? := if kind == ``Parser.Command.«section» && stx.getArgs.size ≥ 3 then
        some (replayedSection source stx) else none
      -- The name a `namespace`, `section` or `end` command carries: one scope per component.
      let scopeName : Name :=
        if let some ns := nsName? then ns
        else if kind == ``Parser.Command.«section» || kind == ``Parser.Command.«end» then
          -- The optional name is the last child; `end`'s is an `identWithPartialTrailingDot`,
          -- which wraps the identifier in another node.
          (stx[stx.getNumArgs - 1]?.bind (findFirstIdent? ·)).map (·.getId) |>.getD .anonymous
        else .anonymous
      let components := nameComponents scopeName
      let scopes := max 1 components.length
      if nsName?.isSome then
        for c in components do
          nsPrefixStack := nsPrefixStack.push (nsPrefixStack.back!.str c)
          closers := closers.push s!"end {c}"
      else if kind == ``Parser.Command.«section» then
        for _ in [0:scopes] do nsPrefixStack := nsPrefixStack.push nsPrefixStack.back!
        closers := closers ++ (if components.isEmpty then #["end"]
          else components.toArray.map (s!"end {·}"))
      else if kind == ``Parser.Command.«end» then
        for _ in [0:scopes] do
          if nsPrefixStack.size > 1 then nsPrefixStack := nsPrefixStack.pop
          closers := closers.pop
      let binders := if kind == ``Parser.Command.«variable» || kind == ``Parser.Command.«include»
          || kind == ``Parser.Command.«omit» then
        decomposeVariable source stx else #[]
      -- `openOnly` is `open NS (a b c)`, parsed as 4 children: the `NS` ident, the `(` token, a
      -- node wrapping the `a b c` idents, and the `)` token. Reading `NS` and the list from their
      -- own (3rd and 1st) children, rather than from a walk of the whole `openOnly` node, avoids
      -- needing to separate them by position — `collectIdents`'s stack-based walk doesn't visit
      -- children left-to-right, so naming isn't reliable from a whole-node walk.
      let (openOnlyNamespace?, openOnlyIdents) :=
        if kind == ``Parser.Command.«open» && stx.getArgs.size ≥ 2
            && stx[1].getKind == ``Parser.Command.openOnly && stx[1].getArgs.size ≥ 3 then
          (some stx[1][0].getId.toString, collectIdents stx[1][2])
        else (none, #[])
      let (attrTargets, attrIsTranslation) :=
        match decomposeAttributeCmd? source stx with
        | some (attrs, targets) => (targets, attrs.any isTranslationAttribute)
        | none => (#[], false)
      entries := entries.push
        { cls := .context, src := slice source cmdStart cmdEnd, kind, sectionSrc?, scopes, nsName?,
          qualifiedNsName?, binders, openOnlyNamespace?, openOnlyIdents, attrTargets,
          attrIsTranslation }
    else
      entries := entries.push { cls := .skip, src := slice source cmdStart cmdEnd, kind := stx.getKind }
  for closer in closers.reverse do
    entries := entries.push { cls := .context, src := closer, kind := ``Parser.Command.«end» }
  return entries

/-! ## Phase 2: per-target filtering and section stripping -/

/-- The last component of a declaration's name, read without the prefix of a private name. -/
def shortName (n : Name) : String :=
  match privateToUserName n with
  | .str _ s => s
  | .num _ i => toString i
  | .anonymous => ""

/-- Restricts declaration entries to those defining a declaration in `keep`; the rest become `skip`.
Context entries are preserved, except that an `open NS (a b c)` loses the identifiers naming a
project declaration left out of the file (and is dropped when none is left): such a name would be
an undefined reference, as would `NS` itself in a target where nothing makes `NS` exist. A name
from outside the project stays, being imported. `NS.a` is looked up as written; when it is not a
constant (`NS` spelled relative to an open namespace), the short name decides: kept when something
in `keep` has it, or when no project declaration does (`projectShortNames`). -/
def restrictToTarget (env : Environment) (rootPrefix : Name) (projectShortNames : Std.HashSet String)
    (entries : Array CommandEntry) (keep : Std.HashSet Name) : Array CommandEntry :=
  let keepShortNames : Std.HashSet String :=
    keep.fold (init := {}) fun s n => s.insert (shortName n)
  let openKept (ns id : String) : Bool :=
    let full := ns.toName ++ id.toName
    if env.contains full then
      !isProjectLocalConst env rootPrefix full || keep.contains full
    else
      keepShortNames.contains id || !projectShortNames.contains id
  entries.map fun e =>
    match e.cls with
    | .decl => if e.declNames.any keep.contains then e else { e with cls := .skip }
    | .context =>
        match e.openOnlyNamespace? with
        | none => e
        | some ns =>
            let kept := e.openOnlyIdents.filter (openKept ns)
            if kept.isEmpty then { e with cls := .skip }
            else if kept.size == e.openOnlyIdents.size then e
            else { e with src := s!"open {ns} ({String.intercalate " " kept.toList})" }
    | .skip => e

/-- Drops every *declaration* emitted after the one defining `target`, keeping context commands so
that `namespace`/`section`/`end` nesting stays balanced.

Nothing a declaration depends on can be defined after it. Within a module Lean requires definition
before use, and across modules a dependency must live in an imported module, which `moduleOrder`
places earlier. So any declaration positioned after the target is provably unnecessary, and is
either a spurious dependency edge or a sibling dragged in by whole-command emission.

Without this, 491 of brownian-motion's 1677 minimal files (29%) ended with a block of unrelated
declarations — the target buried in the middle of the file it is supposed to be the point of. -/
def truncateAfterTarget (involved : Array (Name × Array CommandEntry)) (target : Name) :
    Array (Name × Array CommandEntry) := Id.run do
  -- Which module, and which entry within it, defines the target.
  let mut targetModule? : Option Nat := none
  let mut targetEntry? : Option Nat := none
  for i in [0:involved.size] do
    let (_, entries) := involved[i]!
    for j in [0:entries.size] do
      if entries[j]!.cls == .decl && entries[j]!.declNames.contains target then
        targetModule? := some i
        targetEntry? := some j
  let some tm := targetModule? | return involved
  let some te := targetEntry? | return involved
  return involved.mapIdx fun i (modName, entries) =>
    if i < tm then (modName, entries)
    else
      -- In the target's own module, drop declarations after its entry; in every later module,
      -- drop all of them. Context commands survive either way, to keep nesting balanced.
      (modName, entries.mapIdx fun j e =>
        if e.cls == .decl && (i > tm || j > te) then { e with cls := .skip } else e)

/-! ## Phase 3: assembly -/

/-- The external (non-project) modules to `import` for `modules`. Because project modules are emitted
inline rather than imported, an external (e.g. Mathlib) dependency may only be reachable *through* a
project module. So we walk the import graph transitively through project modules, collecting the
external "frontier" — every external module directly imported by any project module reachable from
`modules`, less the `excludedImports`. `public import`ing those covers their transitive
dependencies. -/
partial def externalImports (env : Environment) (rootPrefix : Name) (modules : Array Name) :
    Array Name := Id.run do
  let directImports (modName : Name) : Array Name := Id.run do
    let some idx := env.getModuleIdx? modName | return #[]
    if h : idx.toNat < env.header.moduleData.size then
      return env.header.moduleData[idx.toNat].imports.map (·.module)
    return #[]
  let mut visited : Std.HashSet Name := {}     -- project modules already walked
  let mut seenExt : Std.HashSet Name := {}     -- external modules already collected
  let mut result : Array Name := #[]
  let mut stack := modules.toList
  while !stack.isEmpty do
    let modName := stack.head!
    stack := stack.tail!
    if visited.contains modName then continue
    visited := visited.insert modName
    for m in directImports modName do
      if m == `Init then continue
      if hasPrefixName m rootPrefix then
        stack := m :: stack            -- project module: recurse into its imports
      else if isExcludedImport m then
        continue                       -- external, but deliberately not imported (see above)
      else if !seenExt.contains m then
        seenExt := seenExt.insert m    -- external module: part of the import frontier
        result := result.push m
  return result

/-- Re-renders a `variable` command, dropping only the binders that reference an *excluded* exposed
declaration — one outside the target's closure, hence not emitted here, so a reference to it would be
an undefined name. `excludedNames` holds those declarations' full names.

An identifier is treated as such a reference only if some in-scope namespace prefix (`activePrefixes`,
the open/entered namespaces) turns it into an excluded name, *and* it does not already denote an
external (non-project) constant. The latter guard is essential: otherwise a Mathlib type or class that
merely shares its last name component with a project declaration (e.g. `IndexedPartition`) would be
mistaken for the project one and its binder wrongly dropped, taking the binders it scopes with it.

A reference can also be spelled as *generalized field notation* on another bound name, in which the
referenced declaration's own name never literally appears: `variable [𝓕.IsComplete P]` denotes
`MeasureTheory.Filtration.IsComplete` purely by virtue of `𝓕`'s type. `boundVarTypes` maps each
`variable`-bound name to the head symbol of its type (`𝓕 ↦ Filtration`) so such a binder can be
resolved and, when excluded, dropped. Going through the receiver's type keeps this as precise as the
direct case — matching the field's last component against excluded short names instead would
resurrect exactly the `IndexedPartition` confusion the guard above exists to prevent, since Mathlib
has its own top-level `IsComplete`.

Returns `none` if no binder survives. -/
def binderRefsExcluded (env : Environment) (rootPrefix : Name) (excludedNames : Std.HashSet Name)
    (activePrefixes : Array Name) (boundVars : Std.HashSet Name)
    (boundVarTypes : Std.HashMap Name Name) (id : String) : Bool :=
  let resolvesToExcluded (n : Name) : Bool :=
    activePrefixes.any fun pfx => excludedNames.contains (pfx ++ n)
  -- `x.f` with `x` a `variable`-bound name: resolve it as `T.f`, `T` being the head of `x`'s type.
  let fieldNotationExcluded (n : Name) : Bool :=
    match nameComponents n with
    | recv :: field@(_ :: _) =>
      match boundVarTypes.get? recv.toName with
      | some ty => resolvesToExcluded (field.foldl (fun acc c => Name.str acc c) ty)
      | none => false
    | _ => false
  let n := id.toName
  if boundVars.contains n then
    false   -- a locally-bound `variable` name, not a global reference
  else if env.contains n && !isProjectLocalConst env rootPrefix n then
    false   -- an external (e.g. Mathlib) constant, not a project reference
  else
    resolvesToExcluded n || fieldNotationExcluded n

/-- Whether an entry of a `variable`, `include` or `omit` command survives in a file. A binder
survives unless one of its identifiers names a declaration left out of the file
(`binderRefsExcluded`). A bare variable name, as `include` and `omit` take, survives only if a
binder of that name did (`bound`): `include hf` after the binder `(hf : P f)` was dropped would
name no variable. -/
def entryKept (env : Environment) (rootPrefix : Name) (excludedNames : Std.HashSet Name)
    (activePrefixes : Array Name) (boundVars : Std.HashSet Name)
    (boundVarTypes : Std.HashMap Name Name) (bound : Std.HashSet Name)
    (entry : String × Array String) : Bool :=
  let (src, idents) := entry
  if idents.size == 1 && src.trimAscii.toString == idents[0]! then
    bound.contains idents[0]!.toName
  else
    !idents.any (binderRefsExcluded env rootPrefix excludedNames activePrefixes boundVars
      boundVarTypes)

/-- Renders a `variable`, `include` or `omit` command with the entries that survive (`entryKept`),
or `none` when none does. A command that could not be decomposed is kept verbatim. -/
def pruneEntries (keep : String × Array String → Bool) (keyword : String) (e : CommandEntry) :
    Option String :=
  if e.binders.isEmpty then
    some e.src   -- couldn't decompose; keep verbatim
  else
    let kept := e.binders.filter keep
    if kept.isEmpty then none
    else some (keyword ++ " " ++ " ".intercalate (kept.map (·.1)).toList)

/-- Renders a declaration command, pruning any `omit … in` prefix in step with the `variable`
binders (`entryKept`): an `omit` still naming a binder that was dropped is an undefined reference.
The surviving entries are re-rendered, or the whole prefix is dropped when none survive. -/
def pruneOmit (keep : String × Array String → Bool) (e : CommandEntry) : String :=
  match e.srcNoOmit? with
  | none => e.src
  | some bare =>
    let kept := e.omitBinders.filter keep
    if kept.size == e.omitBinders.size then e.src
    else if kept.isEmpty then bare
    else "omit " ++ " ".intercalate (kept.map (·.1)).toList ++ " in\n" ++ bare

/-- Role of a pre-rendered output chunk for scope balancing in `stripEmptyScopes`. -/
inductive ScopeTag where
  /-- Opens a strippable scope: `section`. Dropped if it ends up holding nothing but `soft` chunks. -/
  | openSection
  /-- Opens a strippable scope: `namespace X`. Dropped on the same terms as `openSection`; the
  namespace stubs at the top of the file are what keep `X` existing for later references. -/
  | openNamespace
  /-- Closes a scope: `end` or `end X`. -/
  | close
  /-- A scoped context command — `variable`, `open`, `set_option`, `universe` — whose whole effect is
  on the enclosing scope's contents. It does *not*, on its own, justify keeping that scope: with
  nothing left inside for it to act on, it is dropped along with it. -/
  | soft
  /-- A declaration or any other context command: forces the enclosing scope to be kept. -/
  | hard
  deriving BEq, Inhabited

/-- A pre-rendered output chunk: its role for scope balancing, its text, and the project namespaces
the text needs to exist (the one a `namespace X` enters, the ones an `open` names).

Carrying the namespaces *per chunk* rather than collecting them from the source commands up front is
what lets the stub block at the top of the file be restricted to the chunks that actually survive
`stripEmptyScopes`. A target typically keeps a handful of declarations out of a module holding
hundreds, so almost every `namespace … end` block is dropped — and a stub for a namespace no
surviving line mentions is pure noise. -/
structure OutChunk where
  tag : ScopeTag
  text : String
  /-- Project namespaces this chunk references; stubbed iff the chunk survives. -/
  namespaces : Array Name := #[]
  /-- For a chunk opening or closing scopes, how many: one per component of the name, as Lean
  counts them (`namespace A.B` opens two, `end A.B` closes two, `section` and `end` one). -/
  scopes : Nat := 1
  /-- For a `set_option` chunk, the option it sets and the value it sets it to (see
  `dropRedundantOptions`). -/
  setOption? : Option (Name × String) := none
  deriving Inhabited

/-- Collapses runs of two or more consecutive blank lines into a single blank line. -/
def collapseBlankRuns (s : String) : String :=
  let isBlank (l : String) : Bool := l.all Char.isWhitespace
  let collapsed := s.splitOn "\n" |>.foldl (init := ([] : List String)) fun acc line =>
    match acc with
    | prev :: _ => if isBlank line && isBlank prev then acc else line :: acc
    | [] => [line]
  "\n".intercalate collapsed.reverse

/-- Whether `chunks` is a single scope: an opening chunk first, and the chunk closing it last. -/
def isOneScope (chunks : Array OutChunk) : Bool := Id.run do
  unless chunks[0]?.any (fun c => c.tag == .openSection || c.tag == .openNamespace) do return false
  let mut depth : Int := 0
  for i in [0:chunks.size] do
    match chunks[i]!.tag with
    | .openSection | .openNamespace => depth := depth + chunks[i]!.scopes
    | .close => depth := depth - chunks[i]!.scopes
    | _ => pure ()
    if depth == 0 then return i + 1 == chunks.size
  return false

/-- Drops `section` and `namespace` scopes that contain no declarations and no context beyond the
`soft` commands (`variable`/`open`/`set_option`/`universe`), which are scoped to the dropped block
and hence safe to remove with it. A scope is kept iff it (transitively) contains a `hard` chunk;
otherwise the whole `… end` block — `soft` lines included — is dropped. Because matching
opens/closes are tracked on a stack, nesting stays balanced regardless of how deep an empty block
is.

A plain `section … end` holding nothing but one scope is that scope, and is replaced by it: every
module is wrapped in a `section`, and a module whose commands sit in a scope of their own —
`noncomputable section`, the module system's `@[expose] public section` — would otherwise read as two
nested sections. -/
def stripEmptyScopes (items : Array OutChunk) : Array OutChunk := Id.run do
  -- Stack of open scopes: (open chunk, accumulated inner chunks, must be kept?).
  let mut stack : Array (OutChunk × Array OutChunk × Bool) := #[]
  let mut top : Array OutChunk := #[]   -- chunks already committed at the current outermost level
  for c in items do
    match c.tag with
    -- Namespaces are droppable too: an empty or `soft`-only `namespace … end` block later in the
    -- file is useless, since the namespace stubs at the top already declare it for `open`s.
    | .openSection | .openNamespace => stack := stack.push (c, #[], false)
    | .close =>
      if stack.isEmpty then
        top := top.push c   -- unbalanced (shouldn't happen): emit verbatim
      else
        -- The open chunks this closes: as many as hold the scopes it closes (`end A.B` closes a
        -- `namespace A.B`, or a `namespace A` and a `namespace B`).
        let mut need : Int := c.scopes
        let mut block : Array OutChunk := #[]
        let mut hasContent := false
        let mut opened := 0
        while need > 0 && !stack.isEmpty do
          let (o, inner, h) := stack.back!
          stack := stack.pop
          block := #[o] ++ inner ++ block
          hasContent := hasContent || h
          need := need - o.scopes
          opened := opened + 1
        if hasContent then
          let rendered :=
            if opened == 1 && block[0]!.tag == .openSection && block[0]!.text == "section\n"
                && isOneScope (block.extract 1 block.size)
            then block.extract 1 block.size
            else block.push c
          if stack.isEmpty then
            top := top ++ rendered
          else
            let (po, pl, _) := stack.back!
            stack := stack.set! (stack.size - 1) (po, pl ++ rendered, true)
        -- else: drop the scopes (open chunks, inner `soft` lines, and close chunk) entirely.
    | .soft =>
      if stack.isEmpty then
        top := top.push c
      else
        let (o, l, h) := stack.back!
        stack := stack.set! (stack.size - 1) (o, l.push c, h)
    | .hard =>
      if stack.isEmpty then
        top := top.push c
      else
        let (o, l, _) := stack.back!
        stack := stack.set! (stack.size - 1) (o, l.push c, true)
  -- Flush any unclosed scopes verbatim (shouldn't happen with well-formed sources).
  for (openChunk, inner, _) in stack do
    top := (top.push openChunk) ++ inner
  return top

/-- Drops every `set_option` line that re-sets an option to the value already in effect where it
stands, `inEffect` being what is in effect before the first chunk. The option state is tracked as a
stack that pops with each `end`, mirroring how Lean scopes the setting: a value restored by leaving a
scope is *not* still in effect afterwards. -/
def dropReSetOptions (chunks : Array OutChunk) (inEffect : Std.HashMap Name String := {}) :
    Array OutChunk := Id.run do
  let mut out : Array OutChunk := #[]
  let mut scopes : Array (Std.HashMap Name String) := #[inEffect]
  for c in chunks do
    match c.tag, c.setOption? with
    | .openSection, _ | .openNamespace, _ =>
      for _ in [0:c.scopes] do scopes := scopes.push {}
      out := out.push c
    | .close, _ =>
      for _ in [0:c.scopes] do
        if scopes.size > 1 then scopes := scopes.pop
      out := out.push c
    | _, some (name, value) =>
      -- The innermost scope that has set this option is the one in effect.
      let inEffect? := scopes.reverse.findSome? (·.get? name)
      unless inEffect? == some value do
        scopes := scopes.set! (scopes.size - 1) (scopes.back!.insert name value)
        out := out.push c
    | _, none => out := out.push c
  return out

/-- Drops every `set_option` line immediately followed by another setting of the same option: nothing
elaborates in between, so only the last setting of the run is ever in force. Adjacency is judged on
the chunks as they will be written, which is why this runs *after* `dropReSetOptions` — a run like
`autoImplicit`/`maxHeartbeats`/`autoImplicit`/`maxHeartbeats` only becomes a run of `maxHeartbeats`
settings once the repeated `autoImplicit` lines are gone. A setting followed by a *scope* rather than
by another setting is live, since what opens next inherits it. -/
def dropSupersededOptions (chunks : Array OutChunk) : Array OutChunk :=
  chunks.zipIdx.filterMap fun (c, i) =>
    match c.setOption? with
    | some (name, _) =>
      if (chunks[i + 1]?.bind (·.setOption?)).any (·.1 == name) then none else some c
    | none => some c

/-- Drops every `set_option` line with no observable effect: one that re-sets an option to the value
already in effect, and one immediately superseded by another setting of the same option.

Worth doing because these come in runs. A source file that sets `autoImplicit false` and a heartbeat
budget above each of its sections contributes one such pair per section, and once the sections
themselves are gone (`stripEmptyScopes`) what is left is a block of consecutive settings with nothing
between them for any of them but the last to apply to. -/
def dropRedundantOptions (chunks : Array OutChunk) (inEffect : Std.HashMap Name String := {}) :
    Array OutChunk :=
  dropSupersededOptions (dropReSetOptions chunks inEffect)

/-! ## The project's options

The options a project is built with — its lakefile's `leanOptions`, `autoImplicit false` above all —
are in no source file, so a file made of the source compiles under Lean's defaults unless they are
set again. Under `autoImplicit`, a binder lost from a `variable` command does not fail: its name is
bound anew, with a more general type, and the file states another theorem.

Lake records them per module, in the `.setup.json` it compiles the module with. They are set again
at the top of a file when every module in it shares them, and at the top of a module's block where
it differs. -/

/-- Options that change only what Lean reports, never what a file means or whether it compiles: not
set again. `warningAsError` among them, since every `sorry` warns. -/
def reportOnlyOptions : Array Name :=
  #[`pp, `format, `linter, `trace, `profiler, `diagnostics, `debug, `warn, `warning, `eval,
    `warningAsError, `maxErrors, `printMessageEndPos, `showPartialSyntaxErrors, `showTacticDiff,
    `showInferredTerminationBy, `stderrAsMessages, `maxTraceChildren]

/-- Whether an option the project is built with is set again: one of Lean's own (`builtin`, the
options registered before any module is imported), since only those are known in every file, and
not one of the `reportOnlyOptions`. -/
def isReplayedOption (builtin : Std.HashSet Name) (o : Name) : Bool :=
  builtin.contains o && !reportOnlyOptions.any (hasPrefixName o ·)

/-- An option's value as a `.setup.json` gives it, written as `set_option` takes it. -/
def renderOptionValue : Json → Option String
  | .bool b => some (toString b)
  | .num n => some (toString n)
  | .str s => some s.quote
  | _ => none

/-- The options Lake built `mod` with, as `(name, value)`: the `options` of the `.setup.json` Lake
writes beside the module's other build files, `<build>/ir/A/B.setup.json` for
`<build>/lib/lean/A/B.olean`. `none` when there is no such file. Needs the search path
(`initSearchPath`). -/
def moduleOptions? (mod : Name) : IO (Option (Array (Name × String))) := do
  let rel := String.intercalate "/" (nameComponents mod)
  let some olean ← (try some <$> findOLean mod catch _ => pure none) | return none
  let suffix := s!"lib/lean/{rel}.olean"
  let oleanPath := olean.toString
  unless oleanPath.endsWith suffix do return none
  let setup : System.FilePath := s!"{oleanPath.dropEnd suffix.length}ir/{rel}.setup.json"
  unless ← setup.pathExists do return none
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile setup))
  let some (.obj options) := (json.getObjVal? "options").toOption | return some #[]
  return some <| options.toArray.filterMap fun (k, v) => (renderOptionValue v).map (k.toName, ·)

/-- The settings all of `perModule` make, with the same value: set once, at the top of a file. -/
def commonOptions (perModule : Array (Array (Name × String))) : Array (Name × String) :=
  match perModule[0]? with
  | none => #[]
  | some first => first.filter fun o => perModule.all (·.contains o)

/-- The project namespaces `chunks` reference, in first-mention order and deduplicated: the stubs the
extracted file needs at its top. -/
def chunkNamespaces (chunks : Array OutChunk) : Array Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut acc : Array Name := #[]
  for c in chunks do
    for ns in c.namespaces do
      unless seen.contains ns do
        seen := seen.insert ns
        acc := acc.push ns
  return acc

/-- The project namespaces an `open` command's source text brings into scope.

`known` holds fully-qualified names, but an `open` token may be spelled *relative* to a namespace
already in scope — `open MeasureTheory … AEEqProcess` names `MeasureTheory.AEEqProcess`. Matching
the bare token alone therefore misses it, no stub is emitted, and the whole `open` fails with
`unknown namespace`, which in turn leaves the namespaces spelled correctly on the same line
(`MeasureTheory`, …) unopened too. So each token is resolved against `prefixes` — the namespaces
this file enters — plus the ones the same `open` command brings into scope ahead of it. -/
def openedNamespaces (known : Std.HashSet Name) (prefixes : Array Name)
    (src : String) : Array Name := Id.run do
  let toks := ((src.replace "\n" " ").splitOn " ").toArray.map (·.trimAscii.toString.toName)
  let mut acc : Array Name := #[]
  for tok in toks do
    if tok.isAnonymous then continue
    let resolved? :=
      if known.contains tok then some tok
      else (prefixes ++ toks).findSome? fun p =>
        let full := p ++ tok
        if known.contains full then some full else none
    if let some ns := resolved? then acc := acc.push ns
  return acc

/-- Assembles the standalone file for `target`. `cache` holds the processed entries per module;
`moduleOrder` lists the project modules in dependency-first order; `keep` is the target's transitive
closure (declarations to emit); `exposedNames` is every exposed declaration (to recognise references
to declarations *outside* `keep`). -/
def assembleTarget (env : Environment) (rootPrefix : Name) (cache : Std.HashMap Name (Array CommandEntry))
    (moduleOrder : Array Name) (exposedNames keep projectNamespaces : Std.HashSet Name)
    (moduleOptions : Std.HashMap Name (Array (Name × String))) (projectShortNames : Std.HashSet String)
    (target : Name) : String := Id.run do
  -- Modules contributing at least one kept declaration, in dependency order, with their filtered
  -- (and section-stripped) entries.
  let mut involved : Array (Name × Array CommandEntry) := #[]
  for modName in moduleOrder do
    if let some entries := cache.get? modName then
      -- Keep every context command (so `namespace`/`section`/`end` nesting stays balanced) and the
      -- declarations in the closure; other declarations become `skip`.
      let filtered := restrictToTarget env rootPrefix projectShortNames entries keep
      -- A module contributes either declarations, or — even with none in the closure — standalone
      -- `attribute` commands, whose registrations the rest of the file may depend on (see
      -- `isContextCmd`). Without the second case the module is skipped wholesale and the
      -- registration is lost.
      let hasAttribute := filtered.any fun e =>
        e.cls == .context && e.kind == ``Parser.Command.«attribute» && e.attrIsTranslation
      if filtered.any (·.cls == .decl) || hasAttribute then
        involved := involved.push (modName, filtered)
  -- Nothing after the target can be needed by it; drop it so the file ends where it is going.
  involved := truncateAfterTarget involved target
  -- Truncation can empty a module of declarations entirely; drop those so the file does not carry
  -- a bare `namespace …`/`end` shell (or an import) for a module that now contributes nothing.
  involved := involved.filter fun (_, entries) =>
    entries.any fun e =>
      e.cls == .decl || (e.cls == .context && e.kind == ``Parser.Command.«attribute» && e.attrIsTranslation)
  -- The options every module of this file is built with, set once at its top. A module whose
  -- options are unknown (no `.setup.json`) is left out of the comparison.
  let common := commonOptions (involved.filterMap fun (m, _) => moduleOptions.get? m)
  -- Exposed declarations *not* emitted in this file: a `variable` binder referencing one of these
  -- would reference an undefined name, so such binders are dropped (see `entryKept`).
  -- A private declaration is referred to by its name without the private prefix.
  let excludedNames : Std.HashSet Name := exposedNames.fold (init := {}) fun s n =>
    if keep.contains n then s else (s.insert n).insert (privateToUserName n)
  -- All names bound by `variable` commands in this file: these are local, so an identifier matching
  -- one is not a reference to a same-named global declaration (e.g. the project's top-level `Ω`).
  let boundVars : Std.HashSet Name := Id.run do
    let mut s : Std.HashSet Name := {}
    for (_, entries) in involved do
      for e in entries do
        if e.kind == ``Parser.Command.«variable» then
          for (bsrc, _) in e.binders do
            for nm in binderBoundNames bsrc do
              s := s.insert nm.toName
    return s
  -- The head symbol of each bound name's type (`𝓕 ↦ Filtration`), so that generalized field
  -- notation written on it (`𝓕.IsComplete`) can be resolved back to the declaration it names.
  -- See `entryKept`.
  let boundVarTypes : Std.HashMap Name Name := Id.run do
    let mut m : Std.HashMap Name Name := {}
    for (_, entries) in involved do
      for e in entries do
        if e.kind == ``Parser.Command.«variable» then
          for (bsrc, _) in e.binders do
            if let some ty := binderTypeHead? bsrc then
              for nm in binderBoundNames bsrc do
                m := m.insert nm.toName ty
    return m
  -- Namespaces entered by a `namespace` command anywhere in the involved modules. Deliberately
  -- taken over *all* entries, not just the ones this target keeps: an `open` token has to resolve
  -- to the same namespace it named in the source no matter what survives here.
  let nsPrefixes : Array Name := Id.run do
    let mut acc : Array Name := #[Name.anonymous]
    for (_, entries) in involved do
      for e in entries do
        if let some ns := e.qualifiedNsName? then
          acc := acc.push ns
    return acc
  -- What an `open` token may resolve to: every namespace holding an exposed declaration, plus the
  -- ones these modules enter. The second half matters because a namespace whose contents are all
  -- unexposed appears in no declaration name, so `projectNamespaces` misses it — and an `open` of
  -- it would then be left without the stub that makes it resolve.
  let stubbable : Std.HashSet Name := nsPrefixes.foldl (·.insert ·) projectNamespaces
  -- Build the per-module body as tagged chunks, then drop empty/`soft`-only scopes.
  let mut items : Array OutChunk := #[]
  -- Namespace prefixes in scope when resolving `variable` binder identifiers: the root plus every
  -- entered (`namespace`) or opened (`open`) namespace. Accumulated (never popped) as an
  -- over-approximation of scope; `entryKept` only matches exact excluded names against it.
  let mut activePrefixes : Array Name := #[Name.anonymous]
  -- The names bound by the `variable` binders kept so far, which `include` and `omit` may name.
  let mut bound : Std.HashSet Name := {}
  for (modName, entries) in involved do
    -- The module's path below the root (`Foo.Bar` under root `Foo` reads as `Bar`), except for the
    -- root module itself, whose path below the root is empty.
    let shortName :=
      if modName == rootPrefix then modName.toString
      else if hasPrefixName modName rootPrefix then
        (modName.toString.drop (rootPrefix.toString.length + 1)).toString
      else modName.toString
    items := items.push { tag := .hard, text := s!"\n-- ═══ {shortName} ═══\n" }
    -- Wraps each module's replayed content in its own `section … end`, so its `open` commands
    -- (which, unlike `notation`/`def`/etc., are scoped by `section`) don't leak into later
    -- modules. Without this, each contributing module's `open`s pile up across the whole
    -- assembled file instead of each being local to its own file as in the original project,
    -- and repeating the same `open Foo` several times can make an unqualified name reachable
    -- through several redundant open-paths to the same declaration, which Lean then reports as
    -- ambiguous even though every path resolves to the exact same constant.
    items := items.push { tag := .openSection, text := "section\n" }
    -- The options this module is built with that the file does not set at its top.
    for o in moduleOptions.getD modName #[] do
      unless common.contains o do
        items := items.push { tag := .soft, text := s!"set_option {o.1} {o.2}\n", setOption? := o }
    for e in entries do
      match e.cls with
      | .context =>
        let entryOk := entryKept env rootPrefix excludedNames activePrefixes boundVars boundVarTypes bound
        if e.kind == ``Parser.Command.«variable» then
          for (bsrc, idents) in e.binders do
            if entryOk (bsrc, idents) then
              bound := (binderBoundNames bsrc).foldl (·.insert ·.toName) bound
          if let some v := pruneEntries entryOk "variable" e then
            items := items.push { tag := .soft, text := v ++ "\n" }
        else if e.kind == ``Parser.Command.«include» || e.kind == ``Parser.Command.«omit» then
          -- Scoped like `variable`, and pruned in step with it.
          let keyword := if e.kind == ``Parser.Command.«include» then "include" else "omit"
          if let some v := pruneEntries entryOk keyword e then
            items := items.push { tag := .soft, text := v ++ "\n" }
        else if e.kind == ``Parser.Command.namespace then
          if let some ns := e.nsName? then
            activePrefixes := activePrefixes.push ns
          -- The namespace this enters needs a stub only if this block survives — hence carried on
          -- the chunk rather than collected from every `namespace` command in the module.
          items := items.push
            { tag := .openNamespace, text := e.src ++ "\n", scopes := e.scopes
              namespaces := e.qualifiedNsName?.toArray }
        else if e.kind == ``Parser.Command.«section» then
          -- Every form of `section`, the module system's `@[expose] public section` included, as
          -- `replayedSection` renders it. An empty one goes in `stripEmptyScopes`.
          items := items.push
            { tag := .openSection, text := e.sectionSrc?.getD e.src ++ "\n", scopes := e.scopes }
        else if e.kind == ``Parser.Command.«end» then
          items := items.push { tag := .close, text := e.src ++ "\n", scopes := e.scopes }
        else if e.kind == ``Parser.Command.«attribute» then
          -- Replayed only for translation attributes (see `translationAttributes`), and only when
          -- every name it targets actually exists here. The target test is stricter than
          -- `entryKept`'s: it rejects any project-local constant outside `keep`, not just an
          -- *exposed* one, since a non-exposed project declaration is never emitted either.
          -- `.hard`, not `.soft`: the registration is real content, and the enclosing
          -- `namespace`/`open` scope is what makes its target resolve.
          let targetMissing (id : String) : Bool :=
            let n := id.toName
            activePrefixes.any fun pfx =>
              let full := pfx ++ n
              env.contains full && isProjectLocalConst env rootPrefix full && !keep.contains full
          if e.attrIsTranslation && !e.attrTargets.any targetMissing then
            items := items.push { tag := .hard, text := e.src ++ "\n" }
        else if e.kind == ``Parser.Command.«set_option» then
          if (setOptionName? e.src).any isExcludedOption then
            pure ()   -- an option registered by a package this file does not import; see
                      -- `excludedOptions`. The `set_option … in <decl>` form is handled in `mkSrc`.
          else
            -- Like `variable`: the option is scoped to the enclosing `section`/`namespace`, so it
            -- affects only what is inside it. A block holding nothing but options no longer has
            -- anything to configure, and goes with them.
            items := items.push
              { tag := .soft, text := e.src ++ "\n", setOption? := setOptionSetting? e.src }
        else if e.kind == ``Parser.Command.«universe» then
          -- Scoped like `variable`, and just as pointless in a block with nothing left to quantify.
          items := items.push { tag := .soft, text := e.src ++ "\n" }
        else if e.kind == ``Parser.Command.«open» then
          -- Tokens after `open`/`scoped` name namespaces brought into scope.
          for tok in (e.src.replace "\n" " ").splitOn " " do
            let nm := tok.trimAscii.toString.toName
            unless nm.isAnonymous do activePrefixes := activePrefixes.push nm
          -- Like `variable`: emitted if its scope survives, but doesn't on its own keep an otherwise
          -- empty `section`/`namespace` alive.
          items := items.push
            { tag := .soft, text := e.src ++ "\n"
              namespaces := openedNamespaces stubbable nsPrefixes e.src }
        else
          items := items.push { tag := .hard, text := e.src ++ "\n" }
      | .decl =>
        let body := pruneOmit
          (entryKept env rootPrefix excludedNames activePrefixes boundVars boundVarTypes bound) e
        let mut s := "\n" ++ body ++ "\n"
        for extra in e.appended do
          s := s ++ extra ++ "\n"
        s := s ++ "\n"
        -- `open Foo in <decl>` (a `Command.in` node) carries its own `open`, which needs `Foo` to
        -- exist just as a standalone one does. Only the first line is scanned: that is where the
        -- prefix sits, and scanning the whole declaration would match every fully-qualified name
        -- in its statement.
        let inlineOpens :=
          if e.kind == ``Parser.Command.in then
            openedNamespaces stubbable nsPrefixes (body.splitOn "\n").head!
          else #[]
        items := items.push { tag := .hard, text := s, namespaces := inlineOpens }
      | .skip => pure ()
    items := items.push { tag := .close, text := "end\n" }
  -- What survives, and — read off it — the namespaces the surviving lines still refer to.
  let kept := dropRedundantOptions (stripEmptyScopes items)
    (common.foldl (fun m (o, v) => m.insert o v) {})
  let body := String.join (kept.toList.map (·.text))
  let nsStubs := chunkNamespaces kept
  let imports := externalImports env rootPrefix (involved.map (·.1))
  -- The extracted files are terminal and self-contained (nothing imports them), so the source's
  -- module-system scaffolding (`module` header, `public import`, `@[expose] public section`) is
  -- unnecessary: plain `import`s suffice, and the sections are replayed without it
  -- (`replayedSection`).
  let mut out := String.join (imports.toList.map (fun i => s!"import {i}\n"))
  out := out ++ s!"\n/-! # Standalone extraction for `{target}`\n"
    ++ "Definitions are copied verbatim; theorem proofs are replaced by `sorry`.\n"
    ++ "Auto-generated by ChallengeGen. -/\n"
  -- Replayed `notation`/`macro` commands may mention declarations that appear later in the file;
  -- defer identifier resolution in their right-hand sides to use sites.
  out := out ++ "\nset_option quotPrecheck false\n"
  unless common.isEmpty do
    out := out ++ "\n-- The options the project is built with.\n"
    for (o, v) in common do
      out := out ++ s!"set_option {o} {v}\n"
  -- Existence stubs for the namespaces the body still names, since an `open Foo` may precede the
  -- `namespace Foo` that (re)creates `Foo` here — and may even refer to a namespace no kept
  -- declaration re-enters.
  unless nsStubs.isEmpty do
    out := out ++ "\n-- Namespace stubs (so later `open`s resolve).\n"
    for ns in nsStubs do
      out := out ++ s!"namespace {ns}\nend {ns}\n"
  out := out ++ body
  return (collapseBlankRuns out).trimAscii.toString ++ "\n"

/-! ## Driver -/

/-- The declarations of `modDecls` by the byte index (in `source`) where their range starts. Several
can start at one position: a command declaring more than one constant may give them all its own
range, as Mathlib's `irreducible_def` does for `foo` and `foo_def`. -/
def declPositions (env : Environment) (source : String) (modDecls : Array Name) :
    IO (Std.HashMap Nat (Array Name)) := do
  let fileMap := FileMap.ofString source
  let mut m : Std.HashMap Nat (Array Name) := {}
  for name in modDecls do
    if let some ranges ← findRanges? env name then
      let pos := (fileMap.ofPosition ranges.range.pos).byteIdx
      m := m.insert pos ((m.getD pos #[]).push name)
  return m

/-- What the emitted text of each of `names` needs, from `MeaningGraph`, in the order of `names`.

A declaration whose value is replaced by `sorry` (`valueDropped`) needs what its statement mentions:
its `statement` edges, and every constant its type mentions, proofs included, looked through the
constants that are not declarations (`MeaningGraph.expandThrough`). The statement edges erase
proofs, but the statement's text needs them: an instance of a `Prop`-valued class is a proof, and
the file must declare it for instance search to find it. Any other is emitted whole and needs what its term mentions, the lemmas its
proofs call included: its `term` edges. Proofs inside a definition are mostly replaced by `sorry`
too, but not the tactic blocks that make up a whole value (`wholeValueTacticRanges`), and those
run in the extracted file. Both add the `source` dependencies, what the source needs and no term
mentions: coercion instances, and the constants a notation expands to. -/
def neededDeps (ctx : MeaningGraph.Context) (cache : MeaningGraph.Cache)
    (valueDropped : Name → Bool) (names : Array Name) :
    MetaM (Array (Name × Array Name) × MeaningGraph.Context × MeaningGraph.Cache) := do
  let (ofDropped, ctx) ← ctx.depsOf (names.filter valueDropped) (term := false)
  let (ofWhole, ctx) ← ctx.depsOf (names.filter (!valueDropped ·)) (term := true)
  let mut byName : Std.HashMap Name (Array Name) := {}
  for (n, d) in ofDropped do byName := byName.insert n d.statement
  for (n, d) in ofWhole do byName := byName.insert n d.term
  let mut cache := cache
  let mut out := #[]
  for n in names do
    let deps := byName.getD n #[]
    match ctx.env.find? n with
    | some info =>
      let (source, c) := ctx.sourceDeps cache n info
      cache := c
      let mut deps := deps ++ source
      if valueDropped n then
        let (ofType, c) := MeaningGraph.expandThrough ctx.env (!ctx.isNode ·) cache
          (MeaningGraph.usedConstantsOf ctx.env n info (includeValue := false))
        cache := c
        deps := deps ++ ofType
      out := out.push (n, deps)
    | none => out := out.push (n, deps)
  return (out, ctx, cache)

/-- The project's declarations, in environment order: `MeaningGraph`'s, under the rule
`ltb-meaning/1`. -/
def projectDeclarations (ctx : MeaningGraph.Context) : Array Name :=
  ctx.constants.filterMap fun (n, _, _) => if ctx.exposed.contains n then some n else none

/-- Writes a standalone `<anchorIdOf target>.lean` file into `dir` for each of `targets`, the
declarations of the project `ctx` was made for (`MeaningGraph.Context.of env rootPrefix`), whose
source files are under `projectDir`. Targets that are not declarations of the project are skipped.
Returns the number of files written.

`builtinOptions` are Lean's own options, those registered before any module was imported
(`getOptionDecls` at the start of the process): the options the project is built with are set
again in the files when they are among these (`isReplayedOption`). Empty, none is.

Each project source file is parsed once. A file then holds its target and, transitively, what each
declaration in it needs: what `neededDeps` says, the notations its source uses, and the other
declarations its source command defines. -/
def writeChallenges (ctx : MeaningGraph.Context) (projectDir dir : System.FilePath)
    (targets : Array Name) (builtinOptions : Std.HashSet Name := {}) : IO Nat := do
  let env := ctx.env
  let rootPrefix := ctx.rootPrefix
  let exposedNames := ctx.exposed
  -- Exposed notation parsers, by syntax kind; a declaration's source uses one iff its parsed syntax
  -- contains a node of that kind. The kind is the parser's name, both read without the prefix of a
  -- private name: a `local notation` declares a private parser, and its nodes, parsed again here,
  -- carry another private prefix than the declaration's.
  let notationKinds : Std.HashMap Name Name := exposedNames.fold (init := {}) fun m n =>
    if isNotationKind env n then m.insert (privateToUserName n) n else m
  -- Every project namespace, taken as the proper-prefix ancestors of the exposed declaration names
  -- (a private name read as its author wrote it).
  let projectNamespaces : Std.HashSet Name := exposedNames.fold (init := {}) fun s n =>
    (namespaceAncestors (privateToUserName n).getPrefix).foldl (·.insert ·) s
  -- Group exposed declarations by module.
  let declsByModule : Std.HashMap Name (Array Name) :=
    ctx.constants.foldl (init := {}) fun m (n, mod, _) =>
      if exposedNames.contains n then m.insert mod ((m.getD mod #[]).push n) else m
  -- Project modules in dependency-first order (the order of `env.header.moduleNames`), restricted to
  -- those that contain an exposed declaration.
  let moduleOrder : Array Name := env.header.moduleNames.filter declsByModule.contains
  -- The options each module is built with (see "The project's options").
  let mut moduleOptions : Std.HashMap Name (Array (Name × String)) := {}
  let mut unknownOptions : Array Name := #[]
  for modName in moduleOrder do
    match ← moduleOptions? modName with
    | some opts =>
      moduleOptions := moduleOptions.insert modName (opts.filter (isReplayedOption builtinOptions ·.1))
    | none => unknownOptions := unknownOptions.push modName
  unless unknownOptions.isEmpty do
    IO.eprintln s!"challenge-gen: no build options found for {unknownOptions.size} modules \
      (no .setup.json for {unknownOptions[0]!}, …): their files use Lean's defaults"
  -- Phase 1: process each contributing source file once.
  let mut cache : Std.HashMap Name (Array CommandEntry) := {}
  let mut reparsed : Array Name := #[]
  for modName in moduleOrder do
    let modDecls := declsByModule.getD modName #[]
    let path := moduleSourcePath projectDir modName
    let some source ← (do try pure (some (← IO.FS.readFile path)) catch _ => pure none)
      | continue
    let declPos ← declPositions env source modDecls
    -- The source is parsed against the whole project, which holds syntax the module did not
    -- import: a `scoped` notation `ℙ` that the module's `open ProbabilityTheory` activates turns its
    -- binder `(ℙ : Measure Ω)` into a parse error. The project builds, so a command that does not
    -- parse here can only be that; the module is parsed again against its own imports.
    let mut commands ← parseCommands env source path.toString
    if commands.any (·.hasMissing) then
      if let some idx := env.getModuleIdx? modName then
        if h : idx.toNat < env.header.moduleData.size then
          -- Without running initializers again: the first import ran them, so every extension is
          -- registered and gets its entries, the syntax among them (Lean refuses a second
          -- `loadExts := true` import, `withImporting` having reset the flag).
          let own ← importModules env.header.moduleData[idx.toNat].imports {} (loadExts := false)
          commands ← parseCommands own source path.toString
          reparsed := reparsed.push modName
    let entries ← processFile env source commands declPos notationKinds
    cache := cache.insert modName entries
  unless reparsed.isEmpty do
    IO.eprintln s!"challenge-gen: {reparsed.size} modules parsed against their own imports \
      ({reparsed[0]!}, …): the project's syntax did not parse them"
  -- Map each declaration to the notation parsers its source uses (gathered syntactically above).
  let mut declUsedNotations : Std.HashMap Name (Array Name) := {}
  -- Map each declaration to every exposed declaration its own source command also defines.
  --
  -- One command routinely declares several constants: `@[to_additive]` produces a multiplicative
  -- and an additive version, `@[simps]` adds projection lemmas. Extraction emits whole *commands*
  -- (`restrictToTarget` keeps a command when any one of its declarations is in `keep`), so keeping
  -- one sibling emits the others too — and they must then elaborate. Concretely: a target needing
  -- only `toGermAddMonoidHom` emits the `@[to_additive] def toGermMonoidHom` command it comes from,
  -- whose *multiplicative* spelling needs `Monoid`-side instances that the additive one never
  -- mentions.
  let mut commandSiblings : Std.HashMap Name (Array Name) := {}
  -- The declarations whose value is replaced by `sorry`.
  let mut valueDropped : Std.HashSet Name := {}
  for (_, entries) in cache.toList do
    for e in entries do
      if e.cls == .decl then
        if !e.usedNotations.isEmpty then
          for nm in e.declNames do
            declUsedNotations := declUsedNotations.insert nm e.usedNotations
        if e.declNames.size > 1 then
          for nm in e.declNames do
            commandSiblings := commandSiblings.insert nm e.declNames
        if e.valueDropped then
          valueDropped := e.declNames.foldl (·.insert ·) valueDropped
  -- Phase 2: the graph the files are closed under, for what the targets reach. A declaration's
  -- edges are what its text needs (`neededDeps`), the notations its source uses, and its command's
  -- siblings, each of which arrives with needs of its own.
  let targets := targets.filter exposedNames.contains
  let edges ← runMetaIO env do
    let mut ctx := ctx
    let mut sourceCache : MeaningGraph.Cache := {}
    let mut edges : Std.HashMap Name (Array Name) := {}
    let mut seen : Std.HashSet Name := {}
    let mut frontier : Array Name := #[]
    for t in targets do
      unless seen.contains t do
        seen := seen.insert t
        frontier := frontier.push t
    while !frontier.isEmpty do
      let (needed, c, sc) ← neededDeps ctx sourceCache valueDropped.contains frontier
      ctx := c
      sourceCache := sc
      let mut next : Array Name := #[]
      for (n, deps) in needed do
        let out := (deps ++ declUsedNotations.getD n #[] ++ commandSiblings.getD n #[]).filter
          fun m => m != n && exposedNames.contains m
        edges := edges.insert n out
        for m in out do
          unless seen.contains m do
            seen := seen.insert m
            next := next.push m
      frontier := next
    return edges
  -- The last components of the project's declaration names (`restrictToTarget`).
  let projectShortNames : Std.HashSet String := exposedNames.fold (init := {}) fun s n =>
    s.insert (shortName n)
  -- Phase 3: assemble and write one file per target.
  IO.FS.createDirAll dir
  for target in targets do
    let mut keep : Std.HashSet Name := ({} : Std.HashSet Name).insert target
    let mut todo : Array Name := #[target]
    while !todo.isEmpty do
      let n := todo.back!
      todo := todo.pop
      for m in edges.getD n #[] do
        unless keep.contains m do
          keep := keep.insert m
          todo := todo.push m
    let content := assembleTarget env rootPrefix cache moduleOrder exposedNames keep
      projectNamespaces moduleOptions projectShortNames target
    IO.FS.writeFile (dir / s!"{anchorIdOf target}.lean") content
  return targets.size

end ChallengeGen
