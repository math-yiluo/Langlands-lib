# Tools of the Stacks extract

The directories `StacksCore/` and `StacksFrontier/` are an extract of the Lean formalization of
the Stacks project by AxiomMath (commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, Apache-2.0),
compiled at `/srv/ll-stx/full`. They are produced only by `tools/stx-extract.py`; nothing in
them is written by hand. Run every command from the workspace root.

In this repository each tool and each table is a Markdown file of its name with `.md` added, holding the
file in a code block. To run the tools, save the blocks under their names: the scripts, the Lean tools and
their tables under `tools/`, the two licence tables at the workspace root.

## Making the extract

    python3 tools/stx-extract.py            # about 25 s, plus the cone tool's 15-40 s

Inputs (all kept here):

- `tools/roots.tsv`: the root declarations (`name, module, why`);
- `tools/extra-decls.tsv`: declarations kept although the cone does not reach them, each with
  the reason (`name, module, why`);
- `STX-RENAMES.tsv`: the renames (`old full name, new full name, module, clashed with`) and, in
  its header, the rule by which new names are chosen;
- `tools/forbidden-imports.tsv`: Mathlib modules that no module of the extract may have in its
  import closure (`module, why`): the three that declare names weil-conjectures also declares;
- `tools/extra-imports.tsv`: imports a file needs beyond the modules that its kept terms and text
  name, found by compiling (`module of the extract, imported module, why`); empty at present;
- the compiled copy at `/srv/ll-stx/full` (`--source`): its Lean files, `.olean` and `.ilean`.

What it does:

1. `tools/StxCone.lean` (run by the driver as `lean --run` on the compiled copy) computes the
   cone: the constants of the copy reachable from the roots and extras through types, values
   and proofs, by whole commands (a command is the outermost declaration range of a module; a
   reached constant keeps its command and all the constants it generates); the constants named
   in the text of kept commands (from the source `.ilean`); and, until nothing changes, the
   `rfl` lemmas of the simp sets and the coercion instances whose copy constants are all kept. It
   also records, for every module, the modules outside the copy whose constants the kept
   constants use (`termmods.tsv`). Work data goes to `.tmp/stx-work/` (`cone.tsv`,
   `commands.tsv`, `imports.tsv`, `termmods.tsv`, ...).
2. Every module with a kept command is cut: its non-declaration commands (less `example`s, `attribute`/`export` commands naming a left-out
   declaration, and the namespaces of `open` commands that exist only through left-out
   declarations) and its kept declarations, character for character apart from the renames. The
   renames are applied at the positions Lean recorded in the source `.ilean` (every reference
   and definition of a renamed constant) and in `namespace`/`end` commands.
3. The headers are made in import order. A file keeps its source imports of kept copy modules
   and of modules outside the copy; an import of a left-out copy module is replaced by the modules
   it makes visible (the level rules of the module system, `Lean.importModulesCore`); `import
   Mathlib` and the forbidden modules are never written, directly or in a replacement; and every
   module outside the copy that the kept text needs and that the other imports do not make
   visible is imported (`public import`). A module is needed when its constants occur in the
   terms of the kept constants, are named in the kept text (`.ilean`), or `extra-imports.tsv`
   lists it. The tool stops with an error naming the declaration if a needed module is
   forbidden, and stops if the import closure of any file contains a forbidden module.

Outputs: the files of `StacksCore/` and `StacksFrontier/` (others there are removed),
`STX-MANIFEST.tsv` (for every file: its source, and every declaration kept or left out, with
its name in the extract and in the source), `tools/extract-stats.txt`,
`tools/extract-commands.tsv` (every non-declaration command left out or changed, with the
reason), `tools/extract-imports.tsv` (every `import Mathlib` not written and every import
added, with the constant that needs it), `tools/renames-applied.tsv`,
`tools/extract-warnings.txt`. Running the tool again
reproduces all of them byte for byte.

## Checks

- `taskset -c 0-11 lake build StacksCore StacksFrontier` builds the extract.
- `python3 tools/stx-clash.py` (after a build): names of the extract shared with
  weil-conjectures (`/srv/ll-stx/ref/weil-names.txt`), with the environment of `import Mathlib`,
  with the compiled Library modules, and with a scan of the declaration heads of
  `/srv/ll-stx/ref/head/Langlands`; output `tools/clashes.tsv`.
- `python3 tools/stx-checks.py --repro`: the root declarations' types in the extract against the
  whole copy up to the renames, and their axioms (`tools/StxRootCheck.lean`); the words `sorry`,
  `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern` in the extract and in its
  sources; the counts; two more runs of the tool and `git status`. Output `tools/checks.txt`.
- `python3 tools/stx-coimport.py` (after the extract and the bridge modules are built): Lean,
  without Lake, on a file importing all modules of the extract and `WeilConjectures` (compiled at
  `/srv/ll-stx/weil`), which must be accepted; on a file importing all modules of the extract,
  which must not load `Mathlib` or a forbidden module; and on files importing the bridge modules
  and `WeilConjectures`, with the Library modules in their closure that import `Mathlib` or a
  forbidden module by name; and on a file importing all modules of the extract, `Mathlib` and the
  five Library roots, which must be accepted. Output `tools/coimport.txt`.
- `taskset -c 0-11 python3 tools/stx-timebuild.py`: the time of a full build of the extract from
  nothing, compiled into `.tmp/fullbuild` without touching `.lake/`. With `--src DIR --out DIR2`
  it builds another tree (for instance an earlier extract exported with `git archive`).

`tools/StxNames.lean` dumps the constants of a set of modules (used by the two checks).
