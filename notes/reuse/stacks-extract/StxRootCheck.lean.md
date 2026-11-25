# `StxRootCheck.lean`

This page holds the Lean tool `StxRootCheck.lean` as it is, in the code block below. To use it, save the content of the block under that name.

```lean
import Lean

/-!
# The types and axioms of the root declarations

    lean --run tools/StxRootCheck.lean SIDE OUT ROOTS RENAMES

`SIDE` is `full` (the whole copy: the root names and every constant in the types are mapped by
the renames) or `extract` (the extract: the root names are mapped, the types are read as they
are). For every root of `ROOTS` (`tools/roots.tsv`) the tool writes to `OUT` one line

    name <TAB> universe parameters <TAB> axioms <TAB> type

where the type is a complete serialization of the `Expr` (constants by name, universe levels,
binder names and kinds, literals; metadata is skipped), so that two lines are equal exactly when
the two types are the same term up to the renames. `RENAMES` is `tools/renames-applied.tsv`
(old and new full names of every renamed constant).
-/

open Lean

def binderTag : BinderInfo → String
  | .default => "d"
  | .implicit => "i"
  | .strictImplicit => "s"
  | .instImplicit => "c"

partial def ser (rn : Name → Name) : Expr → String
  | .bvar i => s!"#{i}"
  | .fvar f => s!"F({f.name})"
  | .mvar m => s!"M({m.name})"
  | .sort l => s!"S({l})"
  | .const n ls => s!"C({rn n};{ls})"
  | .app f a => s!"A({ser rn f},{ser rn a})"
  | .lam n t b bi => s!"L({n};{binderTag bi};{ser rn t};{ser rn b})"
  | .forallE n t b bi => s!"P({n};{binderTag bi};{ser rn t};{ser rn b})"
  | .letE n t v b nd => s!"E({n};{nd};{ser rn t};{ser rn v};{ser rn b})"
  | .lit (.natVal k) => s!"N({k})"
  | .lit (.strVal s) => s!"T({repr s})"
  | .mdata _ e => ser rn e
  | .proj s i e => s!"J({rn s};{i};{ser rn e})"

def main (args : List String) : IO UInt32 := do
  let [side, out, rootsPath, renamesPath] := args
    | IO.eprintln "usage: StxRootCheck SIDE OUT ROOTS RENAMES"; return 1
  initSearchPath (← findSysroot)
  let mut renames : Std.HashMap Name Name := {}
  for line in ← IO.FS.lines renamesPath do
    if line.isEmpty || line.startsWith "#" || line.startsWith "old full name" then continue
    match line.splitOn "\t" with
    | o :: n :: _ => renames := renames.insert o.toName n.toName
    | _ => pure ()
  let rn (n : Name) : Name := renames[n]?.getD n
  let mut roots : Array (Name × Name) := #[]
  for line in ← IO.FS.lines rootsPath do
    if line.isEmpty || line.startsWith "#" then continue
    match line.splitOn "\t" with
    | n :: m :: _ =>
      let n := n.toName
      let m := m.toName
      roots := roots.push (if side == "full" then (n, m) else (rn n, m))
    | _ => pure ()
  let mut mods : Array Name := #[]
  for (_, m) in roots do
    unless mods.contains m do mods := mods.push m
  let env ← importModules (mods.map fun m => { module := m }) {} (loadExts := false)
  let h ← IO.FS.Handle.mk out .write
  for (n, _) in roots do
    let some info := env.find? n
      | IO.eprintln s!"not found: {n}"; return 2
    let ctx : Core.Context := { fileName := "<root check>", fileMap := default }
    let st : Core.State := { env }
    let (axs, _) ← (collectAxioms n : CoreM (Array Name)).toIO ctx st
    let mapType := if side == "full" then rn else id
    h.putStrLn s!"{rn n}\t{info.levelParams}\t{axs.qsort Name.lt}\t{ser mapType info.type}"
  h.flush
  return 0
```
