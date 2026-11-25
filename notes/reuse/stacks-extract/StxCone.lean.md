# `StxCone.lean`

This page holds the Lean tool `StxCone.lean` as it is, in the code block below. To use it, save the content of the block under that name.

```lean
import Lean
import Lean.Meta.Tactic.NormCast

/-!
# The declaration cone of a list of roots in the Stacks copy

Run as

    env LEAN_PATH=<compiled copy and packages> lean --run tools/StxCone.lean ROOTS EXTRAS OUTDIR

`ROOTS` and `EXTRAS` are tab-separated files with lines `name<TAB>module<TAB>reason` (lines
starting with `#` and empty lines are skipped). The tool imports the named modules of the
compiled copy, and computes the *cone*: the constants of the copy (modules below `StacksCore`
and `StacksFrontier`) reachable from the roots and extras through types, values and proofs.

Constants are grouped into *commands* by their declaration ranges
(`Lean.findDeclarationRanges?`). A constant without a range of its own (auxiliary proofs,
matchers, equation lemmas, recursors, ...) belongs to the nearest prefix of its name that has a
range. A command is the outermost range of a module: the ranges of a structure's fields and
constructor lie inside the structure's range. When a constant is reached, its whole command is
kept and every constant the command produced is walked as well, so that what the kept text
generates again on elaboration rests only on kept text. The constants *named in the text* of a
kept command are walked too: the `.ilean` of the module records every identifier the
elaborator resolved, also those that the final terms do not contain (an unused `simp` lemma, a
name only used while elaborating). Finally, declarations that elaboration uses without a trace
in the terms are added when everything of the copy they mention is kept, until nothing changes:
the `rfl` lemmas of the simp sets (`simp`, `push_cast`, `norm_cast`) and coercion instances.

Output, in `OUTDIR`:

* `imports.tsv`: `module, isCopy, import, isExported, importAll, isMeta` for every module of
  the environment (modules without imports have one line with an empty import);
* `commands.tsv`: for every command of every copy module of the import closure:
  `module, startLine, startCol, endLine, endCol, kept, constants` (lines 1-based, columns in
  codepoints, 0-based; constants separated by spaces, the kept ones marked with `*`);
* `cone.tsv`: every constant of the cone: `name, sourceModule, kind, owner, reachedFrom`;
* `namespaces.tsv`: the namespaces of the environment (prefixes of names of constants that are
  not internal), with `1` if only constants of the copy have it;
* `selections.tsv`: the selection range (the declared name) of every constant of a kept command
  that has a range of its own: `name, module, startLine, startCol, endLine, endCol`;
* `termmods.tsv`: for every source module of the cone, the modules outside the copy whose
  constants its kept constants use in their types and values: `module, used module, a constant
  used, the kept constant that uses it, number of uses` (a constant counts for the module of its
  owner);
* `unowned.tsv`: copy constants that neither have a range nor a prefix with one;
* `summary.txt`: counts.
-/

open Lean

structure Entry where
  name : Name
  module : Name
  reason : String

def parseList (path : System.FilePath) : IO (Array Entry) := do
  let mut out := #[]
  for line in ← IO.FS.lines path do
    if line.isEmpty || line.startsWith "#" then continue
    let parts := line.splitOn "\t"
    if parts.length < 2 then throw <| IO.userError s!"bad line in {path}: {line}"
    out := out.push { name := parts[0]!.toName, module := parts[1]!.toName,
                      reason := (parts.drop 2).foldl (· ++ ·) "" }
  return out

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

def usedBy (info : ConstantInfo) : Array Name :=
  let fromValue : Array Name :=
    match info with
    | .defnInfo d => d.value.getUsedConstants
    | .thmInfo d => d.value.getUsedConstants
    | .opaqueInfo d => d.value.getUsedConstants
    | .inductInfo d => d.ctors.toArray ++ d.all.toArray
    | .ctorInfo d => #[d.induct]
    | .recInfo d => d.all.toArray
    | _ => #[]
  info.type.getUsedConstants ++ fromValue

/-- The ranges recorded for a declaration, as `Lean.findDeclarationRanges?` finds them. -/
def rangesOf (env : Environment) (n : Name) : Option DeclarationRanges :=
  let core (n : Name) :=
    declRangeExt.find? (level := .exported) env n <|> declRangeExt.find? (level := .server) env n
  if isAuxRecursor env n || isNoConfusion env n || isRecCore env n then core n.getPrefix
  else core n

/-- Positions as pairs (line, column) compared lexicographically. -/
def posKey (p : Position) : Nat × Nat := (p.line, p.column)

def lexLe (a b : Nat × Nat) : Bool := a.1 < b.1 || (a.1 == b.1 && a.2 ≤ b.2)

def isCopyModule (m : Name) : Bool := m.getRoot == `StacksCore || m.getRoot == `StacksFrontier

/-- The constants named in the text of a module, as Lean recorded them in its `.ilean` when the
copy was compiled: (line, column, constant), lines 1-based, columns in UTF-16 units. -/
def ileanRefs (mod : Name) : IO (Array (Nat × Nat × Name)) := do
  let olean ← findOLean mod
  let path := olean.withExtension "ilean"
  unless ← path.pathExists do return #[]
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let .obj refs ← IO.ofExcept (j.getObjVal? "references") | return #[]
  let mut out := #[]
  for (k, v) in refs.toList do
    let some kj := (Json.parse k).toOption | continue
    let some c := (kj.getObjVal? "c").toOption | continue
    let some n := (c.getObjVal? "n" >>= Json.getStr?).toOption | continue
    let name := n.toName
    let some us := (v.getObjVal? "usages" >>= Json.getArr?).toOption | continue
    for u in us do
      let some a := u.getArr?.toOption | continue
      let some l := (a[0]? >>= (·.getNat?.toOption)) | continue
      let some col := (a[1]? >>= (·.getNat?.toOption)) | continue
      out := out.push (l + 1, col, name)
  return out

def main (args : List String) : IO UInt32 := do
  let [rootsPath, extrasPath, outDir] := args
    | IO.eprintln "usage: StxCone ROOTS EXTRAS OUTDIR"; return 1
  initSearchPath (← findSysroot)
  let roots ← parseList rootsPath
  let extras ← parseList extrasPath
  let mut importMods : Array Name := #[]
  for e in roots ++ extras do
    unless importMods.contains e.module do importMods := importMods.push e.module
  let env ← importModules (importMods.map fun m => { module := m }) {} (loadExts := false)
  let mods := env.header.moduleNames
  let data := env.header.moduleData
  IO.FS.createDirAll outDir
  -- Imports of every module.
  let hImp ← IO.FS.Handle.mk (outDir ++ "/imports.tsv") .write
  for i in [0:mods.size] do
    let m := mods[i]!
    let copy := if isCopyModule m then "1" else "0"
    if data[i]!.imports.isEmpty then hImp.putStrLn s!"{m}\t{copy}\t\t\t\t"
    for imp in data[i]!.imports do
      hImp.putStrLn s!"{m}\t{copy}\t{imp.module}\t{imp.isExported}\t{imp.importAll}\t{imp.isMeta}"
  hImp.flush
  -- The source module and owner of every constant of a copy module.
  let modOf (n : Name) : Option Name := (env.getModuleIdxFor? n).map (mods[·.toNat]!)
  let mut owner : Std.HashMap Name Name := {}
  let mut srcMod : Std.HashMap Name Name := {}
  let mut unowned : Array Name := #[]
  -- ranges per source module: (start, end, constant)
  let mut ranged : Std.HashMap Name (Array ((Nat × Nat) × (Nat × Nat) × Name)) := {}
  let mut selection : Std.HashMap Name ((Nat × Nat) × (Nat × Nat)) := {}
  for i in [0:mods.size] do
    let m := mods[i]!
    unless isCopyModule m do continue
    for n in data[i]!.constNames do
      let mut p := n
      let mut found : Option (Name × DeclarationRanges) := none
      while true do
        match rangesOf env p with
        | some r => found := some (p, r); break
        | none =>
          -- An auxiliary constant of a public declaration made in the private scope of a
          -- module (`_private.M.0.foo._proof_1`) belongs to the public `foo`.
          if let some q := privateToUserName? p then
            if q != p && env.contains q then
              if let some r := rangesOf env q then
                found := some (q, r); break
          if p.isAnonymous then break
          p := p.getPrefix
      match found with
      | some (o, r) =>
        let sm := (modOf o).getD m
        owner := owner.insert n o
        srcMod := srcMod.insert n sm
        if o == n then
          selection := selection.insert n
            (posKey r.selectionRange.pos, posKey r.selectionRange.endPos)
          ranged := ranged.alter sm fun
            | some a => some (a.push (posKey r.range.pos, posKey r.range.endPos, n))
            | none => some #[(posKey r.range.pos, posKey r.range.endPos, n)]
      | none =>
        unowned := unowned.push n
        srcMod := srcMod.insert n m
  -- Commands: outermost ranges per module.
  -- cmdOf: constant with a range ↦ (module, command index)
  let mut cmdRanges : Std.HashMap Name (Array ((Nat × Nat) × (Nat × Nat))) := {}
  let mut cmdOfRanged : Std.HashMap Name (Name × Nat) := {}
  let mut overlaps : Array String := #[]
  for (m, arr) in ranged.toArray do
    let sorted := arr.qsort fun a b =>
      if a.1 == b.1 then lexLe b.2.1 a.2.1 && a.2.1 != b.2.1 || (a.2.1 == b.2.1 && a.2.2.lt b.2.2)
      else lexLe a.1 b.1
    let mut cmds : Array ((Nat × Nat) × (Nat × Nat)) := #[]
    for (s, e, n) in sorted do
      match cmds.back? with
      | some (cs, ce) =>
        if lexLe cs s && lexLe e ce then
          cmdOfRanged := cmdOfRanged.insert n (m, cmds.size - 1)
        else
          if lexLe s ce && s != ce then
            overlaps := overlaps.push s!"{m}\t{n}\t{s}\t{e}\t{cs}\t{ce}"
          cmds := cmds.push (s, e)
          cmdOfRanged := cmdOfRanged.insert n (m, cmds.size - 1)
      | none =>
        cmds := cmds.push (s, e)
        cmdOfRanged := cmdOfRanged.insert n (m, cmds.size - 1)
    cmdRanges := cmdRanges.insert m cmds
  -- Every constant ↦ command, and command ↦ constants.
  let mut cmdOf : Std.HashMap Name (Name × Nat) := {}
  let mut cmdConsts : Std.HashMap (Name × Nat) (Array Name) := {}
  for (n, o) in owner.toArray do
    if let some k := cmdOfRanged[o]? then
      cmdOf := cmdOf.insert n k
      cmdConsts := cmdConsts.alter k fun
        | some a => some (a.push n)
        | none => some #[n]
  -- Declarations that elaboration uses without leaving a trace in the terms: `rfl` lemmas of
  -- the simp sets (`simp`, `push_cast`, `norm_cast`), which `simp` and `dsimp` apply by
  -- unfolding, and coercion instances, which the elaborator unfolds. They are kept when their
  -- type names a constant of the copy and every constant of the copy it names is kept.
  let simpExts : List Lean.Meta.SimpExtension :=
    [Lean.Meta.simpExtension, Lean.Meta.NormCast.pushCastExt, Lean.Meta.NormCast.normCastExt.up,
     Lean.Meta.NormCast.normCastExt.down, Lean.Meta.NormCast.normCastExt.squash]
  let mut traceless : Array (Name × String) := #[]
  let mut tracelessSeen : Std.HashSet Name := {}
  for i in [0:mods.size] do
    unless isCopyModule mods[i]! do continue
    for ext in simpExts do
      for lvl in [OLeanLevel.exported, OLeanLevel.server] do
        for e in ext.ext.getModuleEntries env i (level := lvl) do
          let se := match e with
            | .global se => se
            | .scoped _ se => se
          if let .thm t := se then
            if t.rfl || t.backwardRfl then
              if let .decl n .. := t.origin then
                unless tracelessSeen.contains n do
                  tracelessSeen := tracelessSeen.insert n
                  traceless := traceless.push (n, "rfl simp lemma")
    for n in data[i]!.constNames do
      if let some (.defnInfo d) := env.find? n then
        let mut ty := d.type
        while ty.isForall do ty := ty.bindingBody!
        let hd := ty.getAppFn
        if hd.isConst && (hd.constName!.toString.startsWith "Coe") then
          unless tracelessSeen.contains n do
            tracelessSeen := tracelessSeen.insert n
            traceless := traceless.push (n, "coercion instance")
  -- The walk.
  let isCopy (n : Name) : Bool := match srcMod[n]? with
    | some m => isCopyModule m
    | none => false
  let mut seen : Std.HashMap Name String := {}   -- constant ↦ how it was reached
  let mut keptCmds : Std.HashSet (Name × Nat) := {}
  let mut todo : Array (Name × String) := #[]
  -- the constants named in the text of each command, from the module's `.ilean`
  let mut cmdRefs : Std.HashMap (Name × Nat) (Array Name) := {}
  let mut refsLoaded : Std.HashSet Name := {}
  for e in roots do todo := todo.push (e.name, "root")
  for e in extras do todo := todo.push (e.name, "extra")
  for e in roots ++ extras do
    unless env.contains e.name do
      IO.eprintln s!"not found: {e.name}"; return 2
  let mut round := 0
  while true do
    while !todo.isEmpty do
      let (n, src) := todo.back!
      todo := todo.pop
      if seen.contains n then continue
      if !isCopy n then continue
      seen := seen.insert n src
      if let some k := cmdOf[n]? then
        unless keptCmds.contains k do
          keptCmds := keptCmds.insert k
          for c in cmdConsts[k]?.getD #[] do
            unless seen.contains c do todo := todo.push (c, s!"command of {n}")
          let m := k.1
          unless refsLoaded.contains m do
            refsLoaded := refsLoaded.insert m
            let cmds := cmdRanges[m]?.getD #[]
            for (l, c, r) in ← ileanRefs m do
              -- the command containing position (l, c), by binary search on the starts
              let mut lo := 0
              let mut hi := cmds.size
              while lo < hi do
                let mid := (lo + hi) / 2
                if lexLe cmds[mid]!.1 (l, c) then lo := mid + 1 else hi := mid
              if lo == 0 then continue
              let j := lo - 1
              if lexLe (l, c) cmds[j]!.2 then
                cmdRefs := cmdRefs.alter (m, j) fun
                  | some a => some (a.push r)
                  | none => some #[r]
          for r in cmdRefs[k]?.getD #[] do
            unless seen.contains r do todo := todo.push (r, s!"named in the text of {n}")
      if let some info := env.find? n then
        for u in usedBy info do
          unless seen.contains u do todo := todo.push (u, s!"used by {n}")
    -- traceless declarations about kept constants
    round := round + 1
    for (n, why) in traceless do
      if seen.contains n || !isCopy n then continue
      let some info := env.find? n | continue
      let copyConsts := info.type.getUsedConstants.filter isCopy
      if !copyConsts.isEmpty && copyConsts.all seen.contains then
        todo := todo.push (n, s!"{why} about kept declarations")
    if todo.isEmpty then break
  -- Output.
  let hCone ← IO.FS.Handle.mk (outDir ++ "/cone.tsv") .write
  let mut coneMods : Std.HashSet Name := {}
  let mut named := 0
  let mut theorems := 0
  for (n, src) in seen.toArray.qsort (fun a b => a.1.lt b.1) do
    let sm := srcMod[n]?.getD .anonymous
    coneMods := coneMods.insert sm
    let kind := (env.find? n).map kindOf |>.getD "?"
    if !n.isInternal then
      named := named + 1
      if kind == "theorem" then theorems := theorems + 1
    hCone.putStrLn s!"{n}\t{sm}\t{kind}\t{owner[n]?.getD .anonymous}\t{src}"
  hCone.flush
  let hCmd ← IO.FS.Handle.mk (outDir ++ "/commands.tsv") .write
  let mut nKept := 0
  let mut nCmds := 0
  for (m, cmds) in cmdRanges.toArray.qsort (fun a b => a.1.lt b.1) do
    for j in [0:cmds.size] do
      let (s, e) := cmds[j]!
      let k := (m, j)
      let kept := keptCmds.contains k
      nCmds := nCmds + 1
      if kept then nKept := nKept + 1
      let cs := (cmdConsts[k]?.getD #[]).qsort Name.lt |>.toList.map fun c =>
        if seen.contains c then s!"*{c}" else toString c
      hCmd.putStrLn s!"{m}\t{s.1}\t{s.2}\t{e.1}\t{e.2}\t{if kept then 1 else 0}\t{" ".intercalate cs}"
  hCmd.flush
  -- The modules outside the copy that the kept constants use in their types and values, per
  -- source module of the copy. A constant belongs to the module of its owner (the nearest
  -- prefix of its name with a declaration range), so that an equation lemma counts for the module
  -- of its definition, not for the module where it was realized.
  let ownerModule (u : Name) : Name := Id.run do
    let mut p := u
    while !p.isAnonymous do
      if (rangesOf env p).isSome then
        return (modOf p).getD .anonymous
      if let some q := privateToUserName? p then
        if q != p && env.contains q && (rangesOf env q).isSome then
          return (modOf q).getD .anonymous
      p := p.getPrefix
    return (modOf u).getD .anonymous
  let mut termMods : Std.HashMap (Name × Name) (Name × Name × Nat) := {}
  for (n, _) in seen.toArray.qsort (fun a b => a.1.lt b.1) do
    let some info := env.find? n | continue
    let sm := srcMod[n]?.getD .anonymous
    for u in usedBy info do
      if isCopy u then continue
      let om := ownerModule u
      termMods := termMods.alter (sm, om) fun
        | some (ex, by_, k) => some (ex, by_, k + 1)
        | none => some (u, n, 1)
  let hTm ← IO.FS.Handle.mk (outDir ++ "/termmods.tsv") .write
  for ((sm, om), (ex, by_, k)) in termMods.toArray.qsort (fun a b => a.1.1.lt b.1.1 || (a.1.1 == b.1.1 && a.1.2.lt b.1.2)) do
    hTm.putStrLn s!"{sm}\t{om}\t{ex}\t{by_}\t{k}"
  hTm.flush
  -- The selection ranges (the declared name) of the constants of kept commands.
  let hSel ← IO.FS.Handle.mk (outDir ++ "/selections.tsv") .write
  for k in keptCmds do
    for c in cmdConsts[k]?.getD #[] do
      if let some ((sl, sc), (el, ec)) := selection[c]? then
        hSel.putStrLn s!"{c}\t{k.1}\t{sl}\t{sc}\t{el}\t{ec}"
  hSel.flush
  let hUn ← IO.FS.Handle.mk (outDir ++ "/unowned.tsv") .write
  for n in unowned do hUn.putStrLn s!"{n}\t{srcMod[n]?.getD .anonymous}"
  hUn.flush
  -- Namespaces, as Lean registers them when a declaration is added: the prefixes of the names
  -- of the constants that are not internal. Flag `1`: only constants of the copy have it.
  let mut outsidePrefixes : Std.HashSet Name := {}
  let mut copyPrefixes : Std.HashSet Name := {}
  for i in [0:mods.size] do
    let inCopy := isCopyModule mods[i]!
    for n in data[i]!.constNames do
      if n.isInternal then continue
      let mut p := n.getPrefix
      while !p.isAnonymous do
        if inCopy then
          if copyPrefixes.contains p then break
          copyPrefixes := copyPrefixes.insert p
        else
          if outsidePrefixes.contains p then break
          outsidePrefixes := outsidePrefixes.insert p
        p := p.getPrefix
  let hNs ← IO.FS.Handle.mk (outDir ++ "/namespaces.tsv") .write
  for ns in outsidePrefixes do hNs.putStrLn s!"{ns}\t0"
  for ns in copyPrefixes do
    unless outsidePrefixes.contains ns do hNs.putStrLn s!"{ns}\t1"
  hNs.flush
  let copyMods := mods.filter isCopyModule
  let frontier := coneMods.toList.filter (·.getRoot == `StacksFrontier) |>.length
  let summary :=
    s!"copy modules loaded\t{copyMods.size}\nall modules loaded\t{mods.size}\n" ++
    s!"cone constants\t{seen.size}\nof them named\t{named}\nof those theorems\t{theorems}\n" ++
    s!"cone modules\t{coneMods.size}\nof them in StacksFrontier\t{frontier}\n" ++
    s!"commands in copy modules loaded\t{nCmds}\nkept commands\t{nKept}\n" ++
    s!"unowned copy constants\t{unowned.size}\noverlapping ranges\t{overlaps.size}\n" ++
    s!"traceless candidates (rfl simp lemmas, coercion instances)\t{traceless.size}\nrounds\t{round}\n"
  IO.FS.writeFile (outDir ++ "/summary.txt") summary
  IO.FS.writeFile (outDir ++ "/overlaps.tsv") ("\n".intercalate overlaps.toList)
  IO.print summary
  return 0
```
