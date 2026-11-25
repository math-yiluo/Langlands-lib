STATUS: complete

# Report: the Brauer induction block ported into `Langlands/Representation/Finite/`

The seven modules of the block left `Langlands/AnthropicFLT/` and became five files of
`Langlands/Representation/Finite/`, each with its page. The four users were moved to them, and the old
modules and their pages were removed. The whole workspace builds, and both completeness tests pass
for every end theorem. Work log: `BRAUER-NOTES.md`; commits `7fd4631` … `c58435f` on branch `work`
(this report is the last commit).

## New files

| File | Lines (Lean / page) | What it holds | From |
| --- | ---: | --- | --- |
| `ClassFunctionInduction` | 246 / 104 | `Langlands.FiniteRep.inducedClassFunction` (normalized induction of functions `G → K`) and its calculus: `_apply`, `_congr`, `_conj`, linearity, projection formula, `⊤`, induction in stages | `Def_ClassFunction_Induced` |
| `SolomonInduction` | 743 / 145 | Solomon's theorem `Solomon.exists_one_eq_sum_zsmul_inducedClassFunction_one` (ℚ) and `…_one_complex` (ℂ); permutation characters, the ring of their span, the hyperelementary ideal, the maximal-ideal argument | `Thm_/S_ClassFunction_exists_one_eq_sum_zsmul_induced_one_of_hyperelementary`, and `BrauerProof.solomon_complex` of `S_BrauerInduction…` |
| `WeightSpaces` | 364 / 117 | weight spaces `wt σ A χ` of a commuting subgroup, the internal direct sum, weights as characters, the conjugation action of `K` on weights (scoped instance), `stabRep`, `trace_eq_sum_fixed` | sections `Rep` and `Trace` of `S_ClassFunction_exists_trace_eq_sum_induced_linearCharacter…` |
| `MonomialTrace` | 624 / 132 | the monomial case `MonomialTrace.exists_trace_eq_sum_inducedClassFunction_linearCharacter`; bookkeeping (`Entry`, `lsum`, `lift`), the group lemma, `Monomial`, `engine`, `repOfGL` | the rest of that module and its `Thm_` |
| `BrauerTrace` | 203 / 111 | Brauer's theorem in trace form `BrauerTrace.exists_trace_eq_sum_zsmul_induced_linearCharacter` and its proof | `Thm_/S_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter` |

Together these are 2,180 Lean lines (the seven old modules had 2,054). The layout is flat, because
`Representation/Finite/` and its Brauer files are flat. The 880-line monomial module is split by
subject into `WeightSpaces` and `MonomialTrace`. Statement and proof sit in one file. The
`P2MW.…` name spaces and the `Thm_`/`S_`/`Def_` scheme are gone. Imports are minimal module imports;
each file was checked to compile with exactly them (`tools/prune_imports.sh`). The closure of
`BrauerTrace` has 5,392 modules; it contains no `Mathlib`, `Langlands.MathlibBase` or forbidden
module, and no Library module besides the five. Each file has the Apache-2.0 header naming its FLT
source files and commit. Each page has the sections Statements, Proof(s), Declarations, "Source and
licence" (with a table of FLT files and their SHA-256 and the list of changes) and Literature.

## Names (`BRAUER-NAMES.tsv`)

The table has 104 rows, one for each non-private declaration of the block (the private ones are
`BrauerProof.ext` and `MonomialProof.val`; both stay private). There are 99 distinct new names: the
FLT `main`/`solution` pairs are merged into the end theorems (Solomon and monomial: `main` and
`solution`; Brauer: `solution`).

- `ClassFunction.induced(_X)` → `Langlands.FiniteRep.inducedClassFunction(_X)`, and
  `induced_induced` → `inducedClassFunction_inducedClassFunction`. The new name was chosen to
  differ from the old text: inside `Langlands.FiniteRep.*` the text `ClassFunction.induced` would
  otherwise read as the new name too.
- The three end theorems: `Solomon.exists_one_eq_sum_zsmul_inducedClassFunction_one`,
  `MonomialTrace.exists_trace_eq_sum_inducedClassFunction_linearCharacter` and
  `BrauerTrace.exists_trace_eq_sum_zsmul_induced_linearCharacter`, all under `Langlands.FiniteRep`.
- Solomon helpers go to `Langlands.FiniteRep.Solomon`, with the cryptic names renamed: `IsHyper` →
  `IsHyperelementary`, `pc` → `permCharacter`, `P` → `permLattice`, `I` → `hyperelementaryLattice`,
  `Psub` → `permSubring`, and the lemmas on them to match. `solomon_complex` becomes
  `Solomon.exists_one_eq_sum_zsmul_inducedClassFunction_one_complex`.
- Monomial helpers keep their short names, in `Langlands.FiniteRep.WeightSpaces` (31) or
  `Langlands.FiniteRep.MonomialTrace`. The one exception is `induced_lsum_eq` →
  `inducedClassFunction_lsum_eq`.
- Brauer helpers: `chi` → `matrixCharacter`, `chi_conj` → `matrixCharacter_conj`,
  `induced_ext_apply` → `inducedClassFunction_ext_apply`, `induced_chi_hyper` →
  `exists_inducedClassFunction_matrixCharacter_eq_sum`, `main` → `exists_matrixCharacter_eq_sum_zsmul`.
- No new name existed before:
  - `tools/check_new_names.py` found 0 declarations or name spaces in the original workspace
    (`git archive 51785f3`, 565 files) and 0 in `ref/tree` (39,796 files);
  - `tools/MathlibAbsent.lean` (`import Mathlib`, `env.contains`) found 0 of the 99 in Mathlib.

## Universes of the end theorems

| Theorem | Before | After |
| --- | --- | --- |
| Solomon (ℚ and ℂ forms) | `{G : Type}` | `{G : Type u}` |
| Monomial case | `{G : Type}`; `engine` over `K : Type`, `W : Type`; group lemma `Γ : Type` | `{G : Type u}`; `engine` over `K : Type u`, `W : Type v`; `Γ : Type*` |
| Brauer, trace form | `{G : Type}` | `{G : Type u}` |
| `inducedClassFunction` | `G : Type*`, `K : Type*` | unchanged |
| `WeightSpaces` | `K W : Type`; index types `ι : Type` | `K : Type u`, `W : Type v`; `ι : Type*` |

Every proof generalized without change of argument, so no statement had to stay in `Type`.
`tools/StmtCompare.lean`, run while the old modules still existed, renamed `ClassFunction.induced`
in each old type and set `u := 0` in the new one. For all four statements (the three end theorems
and the complex Solomon form) the two elaborated types were syntactically equal (`==`). It also
proved `@ClassFunction.induced = @inducedClassFunction` by `rfl`.

## Statements whose text changed otherwise than by names and universes

- **The end theorems: none.** They are syntactically equal, as just described.
- **Merges.** The FLT `main` and `solution` of Solomon and of the monomial case, and Brauer's
  `solution`, state exactly the end theorem and are merged into it. Solomon's `main` used
  `IsHyper (H i)`, which is the unfolded condition by definition.
- **Unused instance arguments omitted.** With the linters on (the extract silenced them file-wide),
  the following helpers no longer take an argument their proof does not use (`omit … in`). The types
  become more general; nothing else changes.
  - Solomon: `[Fintype G]` from `conj_pow'`, `IsHyperelementary.of_le_conj`,
    `permCharacter_apply`, `card_mul_permCharacter`, `permCharacter_top`,
    `conj_mem_of_mem_stabilizer`, `hyperelementaryLattice_le_permLattice`,
    `permCharacter_mem_permLattice`, `one_mem_permLattice`, `mul_mem_span_of_gen`,
    `orderOf_conj'`; `[Fintype G]` and `[Fact q.Prime]` from `mem_of_orderOf_coprime`.
  - WeightSpaces: `[FiniteDimensional ℂ W]` from 21 lemmas and `[Fintype K]` from 5, four of them
    the same lemmas (listed on its page). As a consequence the definitions `weightHom`, `wtEquiv` and `stabRep` no longer take
    `[FiniteDimensional ℂ W]`.
  - MonomialTrace: `[Fintype K]` from `lift_snd_apply` and `extChar_lift`; `[Fintype G]` from
    `repOfGL_apply` and `trace_repOfGL`.
  - BrauerTrace: `[Fintype G]` from `matrixCharacter_conj`.
- **Users.** No statement changed (see the edits below).

## Raised limits and options

None. No ported file sets any option, and every proof checks under Lean's defaults:
`maxHeartbeats 200000`, `synthInstance.maxHeartbeats 20000`, no `backward.isDefEq.respectTransparency.types`
and no `autoImplicit` setting. The extract had set `maxHeartbeats 4000000`,
`synthInstance.maxHeartbeats 400000` and `backward.…types false` in every file, plus linters off.
Without the `backward` option, one proof (`inducedClassFunction_conj`) needs a closing `rfl`; this is
the audit's compatibility edit 1. Since no limit had to be raised, the 671- and 880-line proofs were
not split into lemmas; the 880-line module was split into two files by subject.

## Edits outside the block (`BRAUER-LIBRARY-EDITS.tsv`)

Eight files changed: the four users and their pages, nothing else.

- **Imports.** The users now import `BrauerTrace`, `ClassFunctionInduction`, `MonomialTrace` and
  `SolomonInduction` respectively, instead of the old modules.
- **Names.** `ClassFunction.induced…` becomes `inducedClassFunction…`. The
  `open P2MW…MonomialProof` lines become `open Langlands.FiniteRep.WeightSpaces
  Langlands.FiniteRep.MonomialTrace` (or `MonomialTrace` alone). `…BrauerProof.solomon_complex`
  becomes `Solomon.exists_one_eq_sum_zsmul_inducedClassFunction_one_complex`, and `induced_lsum_eq`
  becomes `inducedClassFunction_lsum_eq`.
- **Decision 2: `BrauerLatticeProof`.** Its universe transport is removed:
  `character_mem_inducedCharacterLattice` now applies Brauer's theorem to `matrixModel V.ρ` on `G`
  itself, using the existing `inducedCharacter_pullbackDatum` with `MulEquiv.refl G`. No public
  statement changed; `card_comap`, `pullbackDatum` and `inducedCharacter_pullbackDatum` are kept.
- **Decision 2: `DegreeZeroBrauerProof`.** Its transport stays. Removing it would change the public
  statements `augment_native`, `augment_of_normal`, `augment_of_hyper` and `augment_monomial_mem`,
  and `DegreeZeroMonomial.engine` is stated for `Type`.
- **Pages.** The user pages now name the new modules and theorems. `BrauerLatticeProof.md` describes
  the proof without the transport. `DegreeZeroMonomial.md` says the imported engine allows any
  universe while its own statements stay in `Type 0`.
- **Unchanged.** The users' own file-wide options (`DegreeZeroBrauerProof`,
  `DegreeZeroBrauerSupport`) and `DegreeZeroMonomial`'s six linter warnings are not part of the port
  and were left as they were; the warnings are identical before and after.
- **Nothing else needed editing.** No other file of the workspace or of `ref/tree` uses a name of
  the block; grep hits in `LocalFactor/` and `Global/` are false positives. No file under
  `LocalFactor/` was edited.
- **Removal.** The seven old modules and their seven pages were removed (`git rm`), together with
  their 49 build outputs in `.lake/build`. Before the removal, nothing outside the block imported
  them except the users.
- **Workspace records.** `BRAUER-LIBRARY-ROOTS.txt` (the seven old roots replaced by the five new
  modules) and `BRAUER-LIBRARY-FILES.tsv` (563 modules) were updated.
- **Licences.** `licenses/Anthropic-FLT/` (in `ref/head`; there is no `licenses/` in the workspace)
  lists none of the old modules (searched for `ClassFunction`, `AnthropicFLT`, `BrauerInduction`,
  `hyperelementary`), so no note was added, as decision 8 provides.

## The script and its report on the whole tree

`tools/apply_brauer_port.py <tree> [--apply]` holds the edits as exact text hunks: 19 in the four
Lean files and 7 in the four pages. Applied to a fresh `git archive 51785f3` it reproduces the
workspace's users and pages byte for byte. Its report searches every `.lean` and `.md` under
`Langlands/` for:

- old module names (dotted and as paths), and imports of them;
- old declaration names as whole tokens;
- the `P2MW.S_…` name spaces and partial references such as `MonomialProof.x`.

It lists the old block's files and the port's new files apart, because the new files' provenance
text names FLT declarations.

On `ref/tree` (dry run, `BRAUER-TREE-REPORT.txt`), all 19 Lean hunks apply. The tree has no pages,
so the 7 page hunks are skipped. After the edits, the only files that mention an old name or import
an old module are the seven old block modules themselves, which the port removes. Other files: 0.

## Tests

- **Build.** `lake build $(tr '\n' ' ' < BRAUER-LIBRARY-ROOTS.txt)` succeeds (9,605 jobs,
  `BRAUER-TESTS-BUILD.txt`, after deleting the five new modules' outputs). `lake build` of the whole
  workspace succeeds (9,606 jobs). No warning comes from a ported file; Lake's notes about plain
  Mathlib imports ("designed for use with the module system") concern every Library file alike.
- **Completeness** (`tools/run_completeness.py`, outputs `BRAUER-TESTS-COMPLETENESS.txt` and
  `BRAUER-TESTS-CONTROL.txt`). Both tests were run on:
  - the ported end theorems (Solomon ℚ and ℂ, monomial, Brauer, `inducedClassFunction_inducedClassFunction`,
    `trace_eq_sum_fixed`, `MonomialTrace.engine`);
  - all 99 new names in one walk;
  - `finiteDegreeZeroBrauer` and the other end theorems of the four users (`characterLattice`,
    `character_mem_inducedCharacterLattice`, `augment_character_mem`, `augment_native`,
    `span_le_degreeZero`, `degreeZero_le_span`, `ind_mem`, `pullback_mem`, `ind_comap`, `ind_ind`,
    `virtualCharacter_induce`, `DegreeZeroMonomial.engine`);
  - `Langlands.Ramification.Padic.finiteGaloisConductorIntegrality` and `exists_int_artinConductor`
    from `FiniteIntegralityProof.lean`.

  Results:
  - `#print axioms`: `[propext, Classical.choice, Quot.sound]` for each.
  - Term walk (`tools/SorryWalk.lean`): it follows the types and the values
    (`ConstantInfo.value? (allowOpaque := true)`, `Expr.getUsedConstants`, plus constructors and
    inductives), transitively. Each walk visited 8k–71k constants, reached the same three axioms,
    found 0 constants mentioning `sorryAx` and none missing.
  - Control: a module compiled with `theorem ctlBad : (1 : Nat) = 2 := sorry` and `ctlAbove`
    using it, imported by a file proving `ctlTop`. For `ctlTop` and `ctlAbove` the walk lists
    `ctlBad` (and `#print axioms` shows `sorryAx`); for `Nat.add_comm` it lists nothing.
- **Static** (`BRAUER-TESTS-STATIC.txt`).
  - No `set_option`, `sorry`, `admit`, `axiom`, `native_decide` or `unsafe` in the ported files.
  - No forbidden import, directly or in the closure.
  - No module under `Langlands/` imports a removed module. Outside `Langlands/`,
    `tools/StmtCompare.lean` imports them: it is a check that ran before the removal (output
    recorded in the notes) and is not a Lake module.

## Literature

Cited in the pages, read on the page images of Serre, *Linear Representations of Finite Groups*
(GTM 42, 1977), in `/srv/central-library`. PDF page = printed page + 8, checked on the pages cited.

- §7.1: Proposition 19 and remark (3), p.55.
- §7.2: the definition of `Ind_H^G(f)`, p.55; Proposition 20, p.56; Remark (3) and Exercise 7.2,
  p.57.
- §8.1: Proposition 24, p.61.
- §8.5: Lemma 4 and Theorem 16, pp.66–67. The monomial proof follows this pattern.
- Ch. 10: §10.1 p.74; Theorems 18 and 18′ p.75; Lemma 8 p.77; §10.4 p.78; Theorems 19 and 20,
  pp.78–79 (Brauer's theorem and its proof through elementary subgroups).
- §11.4: pp.86–87 and Exercise 11.7, p.89. The maximal-ideal step of the Solomon proof follows this.
- §12.6: Theorems 27 and 28 with Proposition 36, pp.97–98.
- §12.7: Lemma 17, p.100. The construction of the hyperelementary subgroup follows this.

Looked for and not found:

- **Solomon's theorem.** The library holds no source stating it (Solomon's 1961 paper or a
  textbook); the full text has no hit for "hyperelementary" or "Solomon's theorem". The Solomon page
  says so and cites nothing for the theorem itself.
- **The Anthropic FLT source at `6e837e75`.** It is not on this server. The SHA-256 values on the
  pages are those of the Library's audit evidence (`notes/reuse/anthropic-brauer-audit.md`) and were
  not recomputed.

## Build times

| What | Time |
| --- | --- |
| `ClassFunctionInduction` | 1.3 s |
| `WeightSpaces` | 3.3 s |
| `SolomonInduction` | 2.8 s |
| `MonomialTrace` | 2.8 s |
| `BrauerTrace` | 1.6 s |
| Roots build after deleting the new modules' outputs | 9.6 s wall |
| Users, rebuilt after the edits | 2.1–3.2 s each |
| The six importers, rebuilt | 11 s wall |
| Completeness tests | 34 s |
| Report on `ref/tree` | 40 s |

All builds ran with `taskset -c 16-23`.

## What was not done, and remarks

- **Pruning failure.** One pruning run hit the one-hour command limit: without its import,
  `Representation` became an auto-bound implicit and elaboration ran away. The script now gives each
  compile 300 s (F1 in the notes). No process was left running.
- **Long proofs not split.** The long proofs were not split into lemmas, because no limit had to be
  raised.
- **Transport kept.** The transport in `DegreeZeroBrauerProof` is kept (decision 2 allows removal
  only without changing public statements).
- **Commit command.** The brief's command (`git add -A -- Langlands licenses tools …`) fails while
  `licenses/` does not exist, and its `'*.md'` would add the harness file `.claude/loop.md`. Commits
  used `git add -A -- Langlands tools '*.md' '*.tsv' '*.txt' ':(exclude).claude'` (D1 in the notes).
- **Files copied from `ref/tree`:** none.
- **Old modules elsewhere in the extract.** No file of `Langlands/AnthropicFLT/` other than the
  seven was touched.
