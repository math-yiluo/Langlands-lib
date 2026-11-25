# `StxNames.lean`

This page holds the Lean tool `StxNames.lean` as it is, in the code block below. To use it, save the content of the block under that name.

```lean
import Lean

/-!
# Names of the constants of an environment

    lean --run tools/StxNames.lean OUT MODULES ROOTS

Imports the modules listed in the file `MODULES` (one per line) and writes to `OUT` one line
`name<TAB>module<TAB>kind<TAB>private` for every constant of a module whose first name component
is in the comma-separated list `ROOTS` (`*` for all modules). Generated constants (auxiliary
proofs, equation lemmas, recursors, instance names) are included; `private` is `1` for private
names.
-/

open Lean

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

def main (args : List String) : IO UInt32 := do
  let [out, modsFile, rootsArg] := args
    | IO.eprintln "usage: StxNames OUT MODULES ROOTS"; return 1
  initSearchPath (← findSysroot)
  let mods := (← IO.FS.lines modsFile).filter (!·.isEmpty) |>.map String.toName
  let roots := (rootsArg.splitOn ",").map String.toName
  let env ← importModules (mods.map fun m => { module := m }) {} (loadExts := false)
  let h ← IO.FS.Handle.mk out .write
  let names := env.header.moduleNames
  for i in [0:names.size] do
    let m := names[i]!
    unless rootsArg == "*" || roots.contains m.getRoot do continue
    for n in env.header.moduleData[i]!.constNames do
      let kind := (env.find? n).map kindOf |>.getD "?"
      h.putStrLn s!"{n}\t{m}\t{kind}\t{if isPrivateName n then 1 else 0}"
  h.flush
  return 0
```
