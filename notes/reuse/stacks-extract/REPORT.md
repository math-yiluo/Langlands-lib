STATUS: complete

# Report: the extract of the Stacks copy, its imports, and the bridges to the reduced fibre theorem

The extract of the Stacks copy is in `StacksCore/` and `StacksFrontier/`: 609 modules, made only
by `tools/stx-extract.py`.

- **It builds, and it is reproducible.** The tool reproduces it byte for byte, and its roots have
  the copy's types up to the renames, with the three standard axioms.
- **The bridges.** Four bridge modules in `Langlands/` prove `SchemeReducedFibreStatement`,
  `CompleteLocalNormalizationFinitenessStatement`, `DvrAffineReducedFibreStatement` and
  `DvrStableNormalizationStatement`, each depending only on `propext`, `Classical.choice` and
  `Quot.sound`.

This report replaces the first one, which is kept as `STX-REPORT-1.md`. Since then the work
of operator note 1 was done:

- **The imports are cut by need.** No module of the extract imports `Mathlib` whole any more, and
  none has `Mathlib.CategoryTheory.GuitartExact.Prod`, `Mathlib.RingTheory.Depth.Basic` or
  `Mathlib.RepresentationTheory.Stabilizer` in its import closure.
- **The co-import with weil-conjectures was run here.** A file importing all modules of the extract
  and `WeilConjectures` is accepted (section 7).
- **The bridges and weil-conjectures.** Of the bridge modules, the two that rest only on the
  extract can be imported with `WeilConjectures`. The other two cannot, as things are, because 112
  Library modules in their closure have `import Mathlib` (section 7, appendix).

The working notes are in `STX-NOTES.md`; `tools/README.md` describes the tools.

## 1. How to run the tool

From the workspace root:

    python3 tools/stx-extract.py                          # the extract, ~1 min
    taskset -c 0-11 lake build StacksCore StacksFrontier  # build it
    python3 tools/stx-clash.py                            # names against the other libraries
    python3 tools/stx-checks.py --repro                   # roots, hole words, counts, reproducibility
    python3 tools/stx-coimport.py                         # co-import with weil-conjectures
    taskset -c 0-11 python3 tools/stx-timebuild.py        # time a full build from nothing

`stx-extract.py` runs `tools/StxCone.lean` (with `lean --run`, on the compiled copy at
`/srv/ll-stx/full`) to compute the cone, then cuts every module of the cone and makes its header.

- **Inputs:**
  - `tools/roots.tsv`, `tools/extra-decls.tsv` and `STX-RENAMES.tsv`;
  - `tools/forbidden-imports.tsv`: the three Mathlib modules, each with its reason;
  - `tools/extra-imports.tsv`: imports found by compiling, each with its reason; empty, as nothing
    was needed;
  - the copy.
- **Outputs:**
  - the two directories and `STX-MANIFEST.tsv`;
  - `tools/extract-stats.txt` and `tools/extract-commands.tsv`;
  - `tools/extract-imports.tsv`: every `import Mathlib` not written and every import added, with
    the constant that needs it;
  - `tools/renames-applied.tsv` and `tools/extract-warnings.txt`.
- **Work data:** `.tmp/stx-work/`, which is not kept.

### The cone

The cone is the set of constants of the copy reachable from the roots and extras through types,
values and proofs. It is computed by commands:

- **Source declarations.** Every constant belongs to a source declaration through its range
  (`Lean.findDeclarationRanges?`). An auxiliary constant belongs to the nearest prefix of its name
  that has a range, and for `_private.M.0.foo._proof_1` that is the public `foo`. A command is the
  outermost range in a module, and a constant reached keeps its whole command and everything that
  command generates.
- **Names written in kept text.** The cone also follows the constants named in the text of kept
  commands, as recorded in the copy's `.ilean`; these include, for example, unused `simp`
  arguments.
- **Traceless helpers.** Until nothing changes, it adds the `rfl` lemmas of the `simp`,
  `push_cast` and `norm_cast` sets and the coercion instances whose type names copy constants that
  are all kept. Elaboration uses these without leaving a trace in the terms.
- **Outside modules used.** For every module it records the modules outside the copy whose
  constants the kept constants use, counting a constant for the module of the source declaration it belongs to
  (`termmods.tsv`). The headers need this (below).

### The cut

- **Non-declaration commands** are all kept, except:
  - `example`s;
  - `attribute` and `export` commands that name a left-out declaration;
  - prefixes (`open … in`, `set_option … in`, `omit … in`) of left-out declarations;
  - namespaces opened by `open` that exist in the whole copy but not in the extract; these are
    removed from the command, and an `open` left empty is dropped.

  Every such change is listed in `tools/extract-commands.tsv`: 3 examples, 11 attribute or export
  commands, 2 `open`s dropped and 1 rewritten, and 187 prefixes.
- **Declarations** are kept character for character, apart from the renames.
- **Comments and blank lines.** Comments directly attached to a left-out declaration go with it,
  and runs of blank lines between commands are collapsed.

### The headers

The headers are made in import order, one rule for every file. Section 7 gives the results.

1. **What stays.** The source's imports of kept copy modules and of modules outside the copy stay.
2. **Left-out copy modules.** An import of a left-out copy module is replaced by what that module
   makes visible, repeatedly, by the level rules of the module system
   (`Lean.importModulesCore`): only its `public` imports, or all of them for `import all`. The
   replacements are reduced by public reachability.
3. **What is never written.** `import Mathlib` and the modules of `tools/forbidden-imports.tsv` are
   never written, neither directly nor in a replacement.
4. **What is added.** A module outside the copy is *needed* by a file if one of three holds:
   - its constants occur in the terms of the kept constants;
   - they are named in the kept text (`.ilean`);
   - `tools/extra-imports.tsv` lists it.

   A needed module that the file's imports do not make visible is imported with
   `public import`, at the place of a cut `import Mathlib` or after the last import. Of several
   such modules, those imported by another are left out.
5. **Stops.** The tool stops with an error if a needed module is forbidden, naming the declaration
   that needs it. It also stops if the import closure of any file contains a forbidden module.
   Both stops were tested by adding a module to the list for one run. With
   `Mathlib.RingTheory.Coalgebra.IsFrobenius`, the error names
   `IsDiscreteValuationRing.residueTensorMap_surjective`. With `Mathlib.Tactic.CrossRefAttribute`,
   all 609 modules are reported. In neither case was anything written.

## 2. The root list

`tools/roots.tsv`:

| Root | Module | Tag |
| --- | --- | --- |
| `AlgebraicGeometry.exists_finiteExtension_smoothAt_genericPoints_fiber_normalization_pullback` | `StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreTheorem` | 09IL |
| `IsNagataRing.of_isPrecomplete_maximalIdeal` (in the extract `StacksIsNagataRing.of_isPrecomplete_maximalIdeal`) | `StacksFrontier.RingTheory.Nagata.CompleteLocalRing` | 032W |
| `isNagataRing_tfae` | `StacksFrontier.RingTheory.Nagata.FiniteType` | 0334 |

The bridges needed nothing else. The cones of 032W and 0334 lie inside that of 09IL: the cone of
the three roots equals the cone of 09IL alone.

## 3. Size

| | Modules | Lines | Declaration commands | Constants (declared names) |
| --- | --- | --- | --- | --- |
| Whole copy | 4,763 files | 1,485,927 | — | 116,947 (69,272) |
| Import closure of the roots | 4,343 | — | 57,897 | — |
| Cone (final, with extras and traceless declarations) | 609 (597 StacksFrontier) | — | 5,516 | 9,728 (3,681 by `!isInternal`, 2,902 theorems) |
| The 609 source files of the cone | 609 | 243,521 | 8,223 | — |
| **Extract** | **609** | **187,775** | **5,516 kept, 2,707 left out** | **9,775 (5,829)** |

- The extract is 12.8% of the copy's files and 12.6% of its lines.
- The manifest lists 5,718 declarations kept (2,370 of them private) and 2,831 left out.
- 237 of the 609 files lost no declaration.
- **Since the first report:** 28 more lines (the headers) and 3 more constants (equation lemmas
  that Lean now realizes inside the extract, section 6).
- **What it loads.** A file importing every module of the extract loads 7,442 modules (section 7),
  not all of Mathlib. `lake build StacksCore StacksFrontier` has 5,799 jobs instead of 9,657.
- **What came back.** No file of algebraic spaces (`AlgebraicGeometry/Spaces`), algebraic
  stacks, `CategoryTheory`, sites, `Topologies`, `Groupoids` or the cotangent complex
  (`StacksFrontier/Cotangent`) is in the extract. The largest parts are
  `RingTheory/DiscreteValuationRing` (112 files) and `AlgebraicGeometry/Morphisms` (79).

**The cone of 09IL alone** was measured before the extras and the traceless declarations were
added: 608 modules (596 of `StacksFrontier`), 9,683 constants and 3,645 named. The 19 November
measurement gave 611 modules, 9,071 constants and 3,348 named. The differences come from three
places:

- **Closure, 4,343 against 4,345:** the two attribute modules `StacksCore.Tactic.*` of the source
  layout.
- **Modules, 608 against 611:** the old script counts the module a constant is stored in, mine the
  module of its source declaration. Three modules of the old cone hold only equation lemmas
  realized there for declarations of other modules:
  - `CohenMacaulay.RegularSequence.LocalRingMap`: `IsCohenMacaulayModule.eq_1`;
  - `CohenMacaulay.Module.RegularSequenceExtension`: `Module.IsMaximalCohenMacaulay.eq_1`;
  - `CompleteIntersection.AtPrime.LocalCriterion`: `IsLocalization.AtPrime.eq_1`, an equation
    lemma of a Mathlib definition.
- **Constants:** whole commands are kept, with all the constants they generate, so the count is
  larger.

## 4. Files kept whole

None. Every file was cut by declaration, and the tool gives no warnings about splitting.

## 5. Extra declarations

`tools/extra-decls.tsv` has two declarations, both found by compiling:

- `OXModule.sectionModule` and `OXModule.sectionPresheafModule`
  (`StacksFrontier.Topology.Sheaves.Cohomology.KFlat.FlatModuleSheavesAndStalks.Basic`). They are
  named, together with the needed `OXModule.stalkModule`, in
  `attribute [local instance] sectionModule sectionPresheafModule stalkModule`
  (`…/TorOneAndSkyscraper.lean:87`). An attribute command that names a left-out declaration is
  left out, and without it `sheafify_skyscraperPOM_stalkIso_skyscraper` cannot find its module
  instance. Keeping the two definitions keeps the command.

`tools/extract-warnings.txt` has one warning, about a command that was left out although it also
names kept declarations: `export _root_.ReducedTensorTower (…)` in
`StacksFrontier/RingTheory/DiscreteValuationRing/ReducedTensorTower.lean:170`. It only makes
aliases in the namespace `IsDiscreteValuationRing.ReducedTensorTower`, and the extract builds
without them, so no extra was added for it.

Three rules of the tool replace what would otherwise be a long list of extras:

- **Text references** are how 72 constants of the cone are first reached. The first build failed
  on `smulMap_tmul`, an unused `simp` argument.
- **`rfl` simp lemmas** add 28, for example `localizationProdMap_apply` and
  `Algebra.FiniteTypeSystem.ringMap_tmul`.
- **Coercion instances** add none.

`tools/extra-imports.tsv`, the corresponding list for imports, is empty.

## 6. Renames and the rule

The rule is stated in the header of `STX-RENAMES.tsv`:

> A declaration of the extract whose full name is also declared by weil-conjectures, Mathlib or
> the Library keeps its namespace, and its last name component `c` gets the prefix `stacks` in
> Lean's case convention: `Stacks` + c when c is UpperCamelCase (types, classes, predicates),
> `stacks_` + c for theorems, and `stacks` + c with its first letter capitalised for other
> definitions. A row renames the declaration and every declaration of the extract in its
> namespace (fields, constructors, equation lemmas, theorems `X.foo`), which keep their own last
> components.

**Why this rule.** The namespace stays, and with it the namespace of a renamed type, because the
kept text uses dot notation on these names: `f.fiberMap`, `X.normalization hX`,
`hDNagata.exists_pow_eq_iff_exists_pow_eq_adicCompletion` on an `IsNagataRing` hypothesis, and
`hR.1`. Moving the declarations under a namespace `Stacks` would break those uses.

**How it is applied.** The tool rewrites every reference and definition of a renamed constant at
the position Lean recorded in the source `.ilean`. It writes the corresponding suffix of the new
name, whether the source writes the name in full, relative to a namespace, or as the field of a
dot notation. It also rewrites the declared names and the `namespace`/`end` commands. 55
constants of the extract are renamed (`tools/renames-applied.tsv`).

| Old name | New name | Clashed with |
| --- | --- | --- |
| `AdicCompletion.factorPow_evalₐ` | `AdicCompletion.stacks_factorPow_evalₐ` | weil-conjectures |
| `AdicCompletion.isNoetherianRing` | `AdicCompletion.stacks_isNoetherianRing` | weil-conjectures |
| `Algebra.IsSeparableExtension` | `Algebra.StacksIsSeparableExtension` | weil-conjectures |
| `Algebra.isSeparableExtension_of_perfectField` | `Algebra.stacks_isSeparableExtension_of_perfectField` | weil-conjectures |
| `AlgebraicGeometry.Scheme.Hom.apply_fiberι` | `AlgebraicGeometry.Scheme.Hom.stacks_apply_fiberι` | weil-conjectures |
| `AlgebraicGeometry.Scheme.Hom.fiberMap` | `AlgebraicGeometry.Scheme.Hom.stacksFiberMap` | weil-conjectures |
| `AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal` | `….stacks_isReduced_subscheme_vanishingIdeal` | weil-conjectures |
| `AlgebraicGeometry.Scheme.normalization` | `AlgebraicGeometry.Scheme.stacksNormalization` | weil-conjectures |
| `IsAnalyticallyUnramified` | `StacksIsAnalyticallyUnramified` | weil-conjectures |
| `IsCohenRing` | `StacksIsCohenRing` | weil-conjectures |
| `IsN1` | `StacksIsN1` | weil-conjectures |
| `IsNagataRing` (with `IsNagataRing.isNoetherianRing`) | `StacksIsNagataRing` | weil-conjectures |
| `IsRegularLocalRing.isDomain` | `IsRegularLocalRing.stacks_isDomain` | weil-conjectures; Library (`Langlands.AnthropicFLT.Theorems.Thm_IsRegularLocalRing_isDomain`) |
| `Module.Flat.tensorProduct_of_flat` | `Module.Flat.stacks_tensorProduct_of_flat` | weil-conjectures |
| `Module.depth` | `Module.stacksDepth` | Library, by scan (`Langlands/AnthropicFLT/Definitions/Def_Patching_SystemTypes.lean`) |
| `Module.depth_le_ringKrullDim_quotient_of_mem_associatedPrimes` | `Module.stacks_depth_le_ringKrullDim_quotient_of_mem_associatedPrimes` | Library, by scan |
| `ringKrullDim_ne_top_of_finiteType` | `stacks_ringKrullDim_ne_top_of_finiteType` | weil-conjectures |
| `topologicalKrullDimAt` (with `topologicalKrullDimAt.eq_1`) | `stacksTopologicalKrullDimAt` | weil-conjectures |

The co-import (section 7) reported no clash of the extract's own. No rename was added.

**After the renames.** `tools/stx-clash.py` (output `tools/clashes.tsv`, run on the current build)
compares the 5,050 non-private constants of the extract with four sets of names:

- the 163,507 names of weil-conjectures;
- the 798,311 constants of the environment of `import Mathlib`;
- the 10,169 constants of the compiled Library modules;
- 347,249 names from a scan of the declaration heads of `ref/head/Langlands`.

**26 names are still shared, none to rename.** Each is an equation or congruence lemma
(`X.eq_1`, `X.congr_simp`) of a **Mathlib** definition `X`, which Lean realized inside a module of
the extract while elaborating a kept proof. For example `AdjoinRoot.powerBasis.congr_simp` and
`PrimeSpectrum.basicOpen.eq_1`.

- **Why they cannot be renamed.** Lean fixes such a name from `X`; only an edit of the proofs could
  avoid it.
- **Why they do not clash.** `Lean.Environment`'s import (`subsumesInfo`) accepts the same theorem
  from several modules: same name, type and universe parameters.
- **This is now tested,** not only argued. The 20 shared with weil-conjectures pass the co-import
  of section 7 (test 1), and the operator's measurement found the same: `WeilConjectures` with all
  of Mathlib except the three modules is accepted. The 10 shared with Mathlib and the 2 shared with
  the Library pass test 4 of section 7: the extract with `import Mathlib` and the five Library
  roots. Some names are shared with more than one of these.
- **The new name.** One name is new since the first report:
  `Algebra.TensorProduct.includeRight.eq_1`, now realized in
  `…/EliminateRamificationSolution/FiniteStageDescent.lean`. Before, the module that already holds
  it, `Mathlib.Algebra.Algebra.Subalgebra.Centralizer`, was in the closure through `import Mathlib`.

Read literally, rule 4.5 also covers generated names, so these 26 meet it in spirit rather than
letter.

## 7. The imports, and the co-import with weil-conjectures

### What the co-import showed

The operator ran a file importing the extract, the bridges and `WeilConjectures`, and Lean refused
it:

```
import WeilConjectures.FromJoel.CategoryTheory.GuitartExact.Basic failed, environment already
contains 'CategoryTheory.TwoSquare.GuitartExact.prod' from Mathlib.CategoryTheory.GuitartExact.Prod
```

Five files of the extract had kept the copy's line `import Mathlib`. Through it the extract
loaded three Mathlib modules (`tools/forbidden-imports.tsv`), each declaring names that
weil-conjectures declares too:

- `Mathlib.CategoryTheory.GuitartExact.Prod`: `CategoryTheory.TwoSquare.GuitartExact.prod`;
- `Mathlib.RingTheory.Depth.Basic`: `Ideal.depth` and `IsLocalRing.depth`;
- `Mathlib.RepresentationTheory.Stabilizer`: `Representation.stabilizer`.

No Mathlib module imports them. The first report's own test, a co-import of the extract with
`import Mathlib` and the Library, could not show this, because that file imported all of Mathlib
anyway.

### What a kept declaration needs from the three

**Nothing.** No kept constant uses a constant of the three modules in its terms (`termmods.tsv`
of the cone), and no kept text names one (the `.ilean` of all 609 kept modules has no reference
into them). So the stop condition of the note does not arise.

### What the tool now writes

The header rule is in section 1; the changes are in `tools/extract-imports.tsv`. **Five lines
`import Mathlib` are no longer written:**

- `StacksFrontier/RingTheory/DiscreteValuationRing/Abhyankar/ResidueFieldTensor.lean`
- `…/DiscreteValuationRing/SolutionTower.lean`
- `…/DiscreteValuationRing/EliminateRamificationSolution/AlgClosedResidueExtension.lean`
- `…/DiscreteValuationRing/EppSolution.lean`
- `StacksFrontier/AlgebraicGeometry/Morphisms/CohenMacaulay/FibrewiseDenseRelativeDimension.lean`

**Ten imports are added, in seven files.** In each case the kept terms use the module, and nothing
else the file imports makes it visible:

| File (under `StacksFrontier/`) | Added | Needed by |
| --- | --- | --- |
| `…/CohenMacaulay/FibrewiseDenseRelativeDimension.lean` | `Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale` | `AlgebraicGeometry.WeaklyEtale.flat` |
| `…/Abhyankar/ResidueFieldTensor.lean` | `Mathlib.RingTheory.Coalgebra.IsFrobenius`, `Mathlib.RingTheory.HopfAlgebra.Basic` | `Coalgebra.IsFrobenius.instFinite`, `HopfAlgebraStruct.toBialgebra` (instances found while all of Mathlib was imported) |
| `…/Abhyankar/AdjoinRootExtensions.lean` | `Mathlib.RingTheory.Smooth.IntegralClosure` | `TensorProduct.toIntegralClosure` |
| `…/EppSolution.lean` | `Mathlib.RingTheory.Flat.Domain` | `TensorProduct.map_injective_of_flat_flat_of_isDomain` |
| `…/EppAlgClosedResidue/CompleteIntegralClosure.lean` | `Mathlib.Algebra.Azumaya.Basic`, `Mathlib.Algebra.Order.Star.Rat` | `IsAzumaya.id`, `Rat.instStarOrderedRing` |
| `…/EppAlgClosedResidue/SolvableInertia.lean` | `Mathlib.GroupTheory.Nilpotent` | `Group.IsNilpotent` |
| `…/EliminateRamificationSolution/FiniteIntegralClosure.lean` | `Mathlib.RingTheory.Finiteness.Descent`, `Mathlib.RingTheory.LocalProperties.Semilocal` | `Module.Finite.of_finite_tensorProduct_of_faithfullyFlat`, `Module.Finite.of_isLocalized_maximal` |

**These sets are minimal in one sense.** They hold the modules that the kept terms and text need
and that the file does not otherwise see. Compiling confirmed that nothing more is needed:
`tools/extra-imports.tsv` stayed empty. It is not minimal in another: the source's other import
lines, and the replacements of left-out copy modules, are kept as before, and I did not try to
remove those of them that are not needed. A fixed list of all Mathlib modules was not used.

**The other imports the tool writes were checked the same way.** This covers the replacements of
left-out copy modules, the 104 Mathlib imports replacing `import StacksCore` in
`StacksFrontier/Algebra/Homology/ProjectiveDimension.lean` among them. The tool's closure check
runs over every header, and test 2 below loads the whole extract. None of the three modules, and
not `Mathlib` itself, is reached. Once `Mathlib` no longer covered everything, the replacements of
`FibrewiseDenseRelativeDimension` are written out (21 Mathlib modules visible through left-out
copy modules, `Mathlib.Tactic` among them).

### The tests

`tools/stx-coimport.py`, output `tools/coimport.txt`. It runs Lean without Lake, with the compiled
outputs of the workspace, of weil-conjectures (`/srv/ll-stx/weil`) and of the packages on
`LEAN_PATH`. Both projects pin the same Mathlib (`56a0058`) and the same packages.

1. **All 609 modules of the extract and `WeilConjectures`: accepted.** The file loads 35,051
   modules: 26,795 of weil-conjectures, all of it, and 609 of the extract. The extract's
   `StacksIsNagataRing` and weil-conjectures' `IsNagataRing` coexist. No clash of the extract's
   own was reported, so no rename was needed.
2. **All 609 modules of the extract alone** load 7,442 modules, and neither
   `Mathlib.CategoryTheory.GuitartExact.Prod`, `Mathlib.RingTheory.Depth.Basic`,
   `Mathlib.RepresentationTheory.Stabilizer` nor `Mathlib` is among them.
3. **The bridge modules with `WeilConjectures`, as things are:**

   | Imported with `WeilConjectures` | Result | Library and `Nyll` modules in its import closure | of them with `import Mathlib` |
   | --- | --- | --- | --- |
   | `…DvrAffineReducedFibre.SchemeReducedFibreProof` | **accepted** | 2 | 0 |
   | `…CommutativeAlgebra.CompleteLocalNormalizationFinitenessProof` | **accepted** | 2 | 0 |
   | `…AlgebraicGeometry.DvrAffineReducedFibreProof` | refused | 483 | 109 |
   | `…AlgebraicGeometry.DvrStableNormalizationProof` | refused | 506 | 112 |
   | the four bridge modules together | **refused** | 506 | 112 |

   The refusals all start with the same error, `CategoryTheory.TwoSquare.GuitartExact.prod` from
   `Mathlib.CategoryTheory.GuitartExact.Prod`, which comes in through Library files with
   `import Mathlib`.
   - **The cause.** The last two bridges import the Library's `ConditionalReduction` and
     `DvrStableNormalization.Reduction`, whose closures reach 112 Library modules (no `Nyll`
     module) that have `import Mathlib`. None imports one of the three modules by name. They are
     listed by name in the appendix and in `tools/coimport.txt`: 6 in
     `Langlands/AlgebraicGeometry`, 2 in `Langlands/CommutativeAlgebra`, and 104 in
     `Langlands/AnthropicFLT` (19 `Definitions`, 42 `Theorems`, 43 `P2M/Sol`). I did not edit
     them.
   - **A further obstacle.** The Library modules in the closure of the four bridges also declare
     21 constants that weil-conjectures declares, all in `Langlands/AnthropicFLT`: 15 declarations,
     and 6 constants generated for them (recursors, constructor and matchers). Among them are
     definitions (`SheafOfModules.monoidalCategory`, `symmetricCategory`, `monoidalClosed`,
     `AlgebraicGeometry.Scheme.Modules.tensorPow`, `…tensorPowSection`, `…dual`,
     `…Scheme.Modules.IsInvertible`) and theorems (`IsRegularLocalRing.isDomain`,
     `AlgebraicGeometry.Smooth.isRegularLocalRing_stalk`, …). So once `import Mathlib` is gone
     from those files, these names must still be renamed on the Library's side before the last two
     bridges can be imported with weil-conjectures, as the design note's section 4.2 foresaw.
4. **All 609 modules of the extract, `import Mathlib` and the five Library roots: accepted.**

## 8. Checks

All recorded in `tools/checks.txt`, made on the committed tree after the import cut.

- **Rule 4.4 (roots).** `tools/StxRootCheck.lean` serializes each root's type completely:
  constants, universe levels, binder names and kinds, and literals. It reads the whole copy with
  the renames applied and the extract as it is. For all three roots the serializations are
  **identical**:
  - 09IL: 1,164,505 characters;
  - 032W: 992 characters;
  - 0334: 1,140 characters.

  The universe parameters are equal (`[u, v]`, `[u]`, `[u]`), and the axioms are
  `[propext, Classical.choice, Quot.sound]` on both sides.
- **Rule 4.3 (holes).** Occurrences in the extract and in its 609 source files, counted in the
  whole text and in code (comments and strings left out):

  | Word | Extract: text | Extract: code | Sources: text | Sources: code |
  | --- | --- | --- | --- | --- |
  | `sorry` | 0 | 0 | 0 | 0 |
  | `admit` | 9 | 0 | 12 | 0 |
  | `axiom` | 0 | 0 | 0 | 0 |
  | `native_decide` | 0 | 0 | 0 | 0 |
  | `unsafe` | 0 | 0 | 0 | 0 |
  | `implemented_by` | 0 | 0 | 0 | 0 |
  | `extern` | 0 | 0 | 0 | 0 |

  The `admit`s are the English word in comments. The four bridge modules contain none of the words
  and set no options.
- **Reproducibility.** Two further runs of the tool give the same hashes as the committed state for
  all 615 files it writes, the import log included, and `git status` then shows no change.
- **Imports.** No file of the extract has `import Mathlib`. The tool's closure check passes, and so
  do tests 1 and 2 of section 7.
- **Clash table:** section 6. **Counts:** section 3.
- **Statements unchanged.** `git diff --name-status 896c3e3 HEAD -- Langlands Nyll` shows only the
  eight added files of section 9. No file of the Library or of `Nyll` was edited.

## 9. The final theorems

The four modules, each with a page beside it, unchanged by the second piece of work and rebuilt
against the new extract:

- `Langlands/AlgebraicGeometry/DvrAffineReducedFibre/SchemeReducedFibreProof.lean`
- `Langlands/CommutativeAlgebra/CompleteLocalNormalizationFinitenessProof.lean`
- `Langlands/AlgebraicGeometry/DvrAffineReducedFibreProof.lean`
- `Langlands/AlgebraicGeometry/DvrStableNormalizationProof.lean`

```lean
theorem Langlands.AlgebraicGeometry.DvrAffineReducedFibre.schemeReducedFibre :
    SchemeReducedFibreStatement.{u, v}
theorem Langlands.CommutativeAlgebra.completeLocalNormalizationFiniteness :
    CompleteLocalNormalizationFinitenessStatement.{u}
theorem Langlands.AlgebraicGeometry.dvrAffineReducedFibre : DvrAffineReducedFibreStatement.{u}
theorem Langlands.AlgebraicGeometry.dvrStableNormalization : DvrStableNormalizationStatement.{u}
```

The statements, in full:

```lean
def SchemeReducedFibreStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDedekindDomain A] (K : Type v) [Field K]
    [Algebra A K] [IsFractionRing A K],
    (IsNoetherianRing A ∧ ∀ (p : Ideal A) [p.IsPrime]
      (L : Type u) [Field L] [Algebra (FractionRing (A ⧸ p)) L] [Algebra (A ⧸ p) L]
      [IsScalarTower (A ⧸ p) (FractionRing (A ⧸ p)) L]
      [FiniteDimensional (FractionRing (A ⧸ p)) L],
      Module.Finite (A ⧸ p) (integralClosure (A ⧸ p) L)) →
    ∀ {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [Flat f] [LocallyOfFiniteType f] [QuasiCompact f],
      ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
        (_ : Algebra A L) (_ : IsScalarTower A K L),
      let g := Spec.algebraMap A (integralClosure A L)
      let W := pullback f g
      ∃ hW : ∀ U : W.Opens, IsCompact (U : Set W) → (irreducibleComponents U).Finite,
        let h := schemeNormalizationHom W hW ≫ pullback.snd f g
        ∀ (b : Spec (.of ↥(integralClosure A L))) (y : h.fiber b),
          y ∈ genericPoints (h.fiber b) →
          ∃ U : (schemeNormalization W hW).Opens, h.fiberι b y ∈ U ∧
            Smooth (h.resLE ⊤ U le_top)

def CompleteLocalNormalizationFinitenessStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (S : Type u) [CommRing S] [IsDomain S] [Algebra R S] [Algebra.FiniteType R S]
    (L : Type u) [Field L] [Algebra (FractionRing S) L] [Algebra S L]
    [IsScalarTower S (FractionRing S) L] [FiniteDimensional (FractionRing S) L],
    Module.Finite S (integralClosure S L)

def DvrAffineReducedFibreStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (A : Type u) [CommRing A] [Algebra R A],
    Module.Flat R A → Algebra.FiniteType R A →
    Algebra.Smooth (FractionRing R) (FractionRing R ⊗[R] A) →
    ∃ (R' : Type u) (cR' : CommRing R'),
      letI := cR'
      ∃ (_ : IsDomain R') (_ : IsDiscreteValuationRing R') (aR' : Algebra R R'),
        letI := aR'
        Module.FaithfullyFlat R R' ∧
        Module.Finite (R' ⊗[R] A)
          (integralClosure (R' ⊗[R] A) ((R' ⊗[R] A) ⊗[R'] FractionRing R')) ∧
        ∀ (F : Type u) [Field F] [Algebra R' F],
          IsReduced (F ⊗[R']
            integralClosure (R' ⊗[R] A) ((R' ⊗[R] A) ⊗[R'] FractionRing R'))

def DvrStableNormalizationStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (X : Over (Spec (CommRingCat.of R))),
    Flat X.hom → LocallyOfFiniteType X.hom → QuasiCompact X.hom →
    IsSeparated X.hom →
    Smooth ((Over.pullback (Spec.algebraMap R (FractionRing R))).obj X).hom →
    ∃ (R' : Type u) (cR' : CommRing R'),
      letI := cR'
      ∃ (dR' : IsDomain R'),
        letI := dR'
        ∃ (_ : IsDiscreteValuationRing R')
          (b : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)),
          Flat b ∧ Surjective b ∧
            Nonempty (DvrStableNormalization.Model ((Over.pullback b).obj X))
```

### The proofs

- **`schemeReducedFibre`** applies the copy's 09IL theorem to the hypotheses, with
  `StacksIsNagataRing A` built by anonymous constructors from the two components of the Nagata
  conjunction. The conclusion is handed over unchanged: the match with the copy's statement,
  including the generic-point morphism (`Spec (.of (X.residueField η.1))` against
  `Spec (X.residueField x.1)`), the normalization and `SmoothAt`, is **definitional**. No transport
  along an isomorphism was needed.
- **`completeLocalNormalizationFiniteness`** uses 032W (`StacksIsNagataRing.of_isPrecomplete_maximalIdeal`),
  then `(isNagataRing_tfae.out 1 3).mp` (0334) for `IsUniversallyJapaneseRing R`, then
  `(hU.1.japanese S).finite L`.
- **`dvrAffineReducedFibre`** is `dvrAffineReducedFibreConditional`, applied to the two proofs
  above at `SchemeReducedFibreStatement.{u, u}`.
- **`dvrStableNormalization`** is `dvrStableNormalization_of_affineReducedFibre dvrAffineReducedFibre`.

With `pp.universes`, `schemeReducedFibre.{u_1, u_2}` has type
`SchemeReducedFibreStatement.{u_1, u_2}`; the other three are polymorphic in one universe.

### `#print axioms` (on the final tree)

```
'Langlands.AlgebraicGeometry.DvrAffineReducedFibre.schemeReducedFibre' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Langlands.CommutativeAlgebra.completeLocalNormalizationFiniteness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Langlands.AlgebraicGeometry.dvrAffineReducedFibre' depends on axioms: [propext, Classical.choice, Quot.sound]
'Langlands.AlgebraicGeometry.dvrStableNormalization' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 10. Build times

All with `taskset -c 0-11`, on a machine shared with other users: the load average was 20 to 28 on
its 32 cores during the measurements of 22 November afternoon.

| Build | Time | Notes |
| --- | --- | --- |
| **Full build of the current extract from nothing** (`tools/stx-timebuild.py`, 12 jobs, into `.tmp/fullbuild`) | **883 s wall; again 918 s** | 609 modules; sum of module times 3,518 s and 3,597 s; load about 20 |
| Full build of the extract before the import cut (commit `6f7d146`, exported with `git archive`, `--src`) | 1,210 s wall | sum 5,023 s; same afternoon, load 24 to 28 |
| Full build of the extract before the import cut, first report | 2,234 s wall | sum 9,134 s; morning, load not recorded |
| Rebuild after the import cut: the 9 changed files | 174 s | |
| Rebuild after the import cut: `lake build StacksCore StacksFrontier` | 474 s | 49 modules recompiled; 66 modules lie above the five files |
| Incremental after the renames / after the traceless rule (first report) | 1,491 s / 1,688 s | 325 / 203 modules |
| Closing, from the committed tree, up to date | extract 3 s; Library roots 4 s; bridges 4 s | first build of the four bridges: 40 s |

- **Why from `.tmp`.** `.lake/` may not be cleaned, so full builds are measured by compiling every
  module with `lean --root=<tree> -o -i -c` into `.tmp`, in import order, as Lake does.
- **`--root`.** Without it, Lean takes the module name from the path relative to the current
  directory, and an exported tree would get wrong private names. The timing tool sets it now.
  Earlier measurements were made in the workspace itself and were not affected.
- **Comparison.** The current extract builds faster than the one before the cut. But modules that
  the cut did not touch were also 1.5 to 2.5 times slower in the earlier runs, so the effect of
  the import change itself is within the variation from load.
- **Critical path.** One module, `…/EliminateRamificationSolution/Assembly.lean`, takes 471–481 s
  (1,054 s in the first measurement). The next is `…/Abhyankar/AbhyankarLemma.lean` at 76–91 s.
- **Tools.** The cone tool takes 15–45 s, the whole extractor about a minute, and the co-import
  tests about a minute.

## 11. Deviations from the design note

1. **Roots.** Only 09IL comes from the copy, with 032W and 0334 for the
   second premise. The norm (0BD0, 0BD4) and the ampleness roots (01VT, 0892) are left out. The
   extract therefore has 609 modules, not the note's 554 to 775.
2. **Renames.** There are 18 rows for 19 clashing declarations, against the note's estimate of
   11 to 18, and 55 constants are renamed with their namespaces. The note did not anticipate the
   26 realized lemmas of Mathlib declarations (section 6). The new names follow a stated rule
   rather than a move under `Stacks`, because of dot notation.
3. **The 09IL bridge is definitional.** The note feared a transport of a few hundred lines.
4. **Names in the extract.** The note's sketches name the copy's `IsNagataRing` and
   `IsNagataRing.of_isPrecomplete_maximalIdeal`. In the extract they are `StacksIsNagataRing` and
   `StacksIsNagataRing.of_isPrecomplete_maximalIdeal`, and `Scheme.normalization` is
   `Scheme.stacksNormalization`.
5. **Universes.** The note proposed `schemeReducedFibre : SchemeReducedFibreStatement.{u, v}`; it
   is that, and `dvrAffineReducedFibre` uses it at `.{u, u}`. `dvrStableNormalization` is added in
   its own module (`DvrStableNormalizationProof.lean`); the note proved stable normal models for smooth-generic DVR schemes "in the same
   stroke" without naming a module.
6. **The root module `StacksCore.lean`** is not in the extract: it has no declarations. Its one
   import, in `StacksFrontier/Algebra/Homology/ProjectiveDimension.lean`, is replaced by the
   modules it makes visible, which is 104 Mathlib imports after reduction.
7. **The cut needed more than the measured cone.** The note expected repairs by hand-listed
   helpers. Besides the two extras, the tool follows text references, adds traceless `rfl` simp
   lemmas, filters `open` commands, and computes the imports a file needs. No file had to be kept
   whole.
8. **The co-import test** (the note's step 5) was run with `WeilConjectures` itself. The note
   expected generated-name clashes; the real obstacle was the five lines `import Mathlib` in the
   extract (section 7). For the bridges, the obstacle is now the Library's own `import Mathlib`
   lines and the 15 shared declarations of `Langlands/AnthropicFLT`, which the note's section 4.2
   foresaw.
9. **Not done here:** the note's step 6 (pages of the extract), and its items in 5.2, 5.5 and 5.6
   (licence notice, `external-copies.md`, the extension of `PORT-MANIFEST.tsv`, the tag index,
   the import allow-list). See section 13.

## 12. Suggestions for the Library

- **None was needed for the proofs.** No private or missing Library declaration was required.
- **To import `DvrAffineReducedFibreProof` and `DvrStableNormalizationProof` with
  weil-conjectures,** two things are needed:
  - replace `import Mathlib` in the 112 Library modules of the appendix by specific imports, as is
    under way in the Library;
  - rename the 15 declarations of `Langlands/AnthropicFLT` that weil-conjectures also declares
    (section 7).

  `tools/stx-coimport.py` repeats the test.
- The page of `SchemeReducedFibreStatement` could link to its proof `schemeReducedFibre` and say
  that the match with the copy's theorem is definitional. In the extract the copy's names are
  `StacksIsNagataRing` and `Scheme.stacksNormalization`.
- The rules of the design note's 5.6 remain to be adopted by the Library: only bridge modules
  import `StacksCore.*` and `StacksFrontier.*`, checked at validation; and the page
  `notes/library/external-copies.md`. A check that no file imports `Mathlib` whole would have
  caught the problem of section 7 earlier.

## 13. What was not done

- **The bridges with weil-conjectures.** A file importing the four bridge modules and
  `WeilConjectures` is refused, as things are, for the Library reasons of section 7. Within the
  rules (no edits of Library files) nothing in this workspace can change that. The two bridges
  that rest only on the extract are accepted.
- **The Library check is exact only for the compiled modules.** It is exact for the 485 Library
  and 17 `Nyll` modules compiled here. For the rest of `ref/head/Langlands` it is a scan of
  declaration heads, which does not see generated names, so it is a lower bound.
- **The source imports were not minimized.** Import lines of the source files other than
  `import Mathlib` and the three modules are kept as in the source, and so are the replacements of
  left-out copy modules. I only checked that they do not reach the three modules.
- **The pages of the extract are not written,** as the brief says. `STX-MANIFEST.tsv` gives, for
  each file, the source file and every declaration kept or left out, with its name in the extract
  and in the source.
- **The licence notice, the tag indexes and the extension of `PORT-MANIFEST.tsv`** (design note
  5.2, 5.5) are not part of this brief and were not made.
- **`.tmp/` was not emptied this time.** It is ignored by Git and holds 1.1 GB of scratch data
  that the tools make again: the tool's work data, the timing builds of the current and the earlier
  extract, the exported earlier tree, and the test files. The command that empties it
  (`rm -rf .tmp/*`) was refused by this session's permissions. The committed tree is clean
  (`git status` shows nothing), and the directory can be emptied with that command at any time.

## Appendix: the Library modules that bring the three Mathlib modules into the bridges' closure

These are the 112 modules in the import closure of the four bridge modules that have
`import Mathlib`; none imports one of the three modules by name, and no `Nyll` module is among
them. 109 of them are already in the closure of `DvrAffineReducedFibreProof`.

- `Langlands.AlgebraicGeometry.`: `DvrStableNormalization.AffineGeomReduced`,
  `DvrStableNormalization.GenericFibre`, `NoetherianValuativeCriterion`,
  `PotentialGeometricReduction`, `SmoothProperConnectedGlobalFunctionsProof`, `SmoothReducedProof`.
- `Langlands.CommutativeAlgebra.`: `FlatDvrNormality`, `IntegralClosureTransfer`.
- `Langlands.AnthropicFLT.Definitions.` (19): `Def_AlgebraicGeometry_ModulesSectionsTensor`,
  `Def_AlgebraicGeometry_ModulesTensorPow`, `Def_AlgebraicGeometry_ModulesTensorPowV2`,
  `Def_AlgebraicGeometry_NeronModelEndomorphismExtension`,
  `Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier`,
  `Def_AlgebraicGeometry_NeronSpecialFibreRestriction`,
  `Def_AlgebraicGeometry_RegularLocalRingQuotientNonZeroDivisorAscent`,
  `Def_AlgebraicGeometry_RegularLocalRingRegularSequenceAscent`,
  `Def_AlgebraicGeometry_RelativePicardFunctor`, `Def_AlgebraicGeometry_SubalgebraStages`,
  `Def_Mathlib_Algebra_IsDirectLimit`, `Def_Mathlib_RingTheory_KmfloorsFiberPolynomialRegularAscent`,
  `Def_Mathlib_RingTheory_RegularLocalRingFlatLocalAscent`,
  `Def_Mathlib_RingTheory_RegularLocalRingQuotientRegular`,
  `Def_Mathlib_RingTheory_SmoothAlgebraOverFieldRegularStalks`,
  `Def_Mathlib_RingTheory_SmoothFieldFiberRegularStalksStandardSmoothReduction`,
  `Def_PresheafOfModules_InternalHom`, `Def_SheafOfModules_Monoidal`, `Def_SheafOfModules_MonoidalV2`.
- `Langlands.AnthropicFLT.Theorems.` (42) and `Langlands.AnthropicFLT.P2M.Sol.` (43): for each of
  the following names `X`, the module `Thm_X` in `Theorems` and the module `S_X` in `P2M.Sol`:
  `Algebra_IsStandardSmooth_exists_isStandardSmoothOfRelativeDimension_of_field`,
  `Algebra_exists_finitePresentation_tensorProduct_algEquiv_of_isDirectLimit`,
  `AlgebraicGeometry_Flat_exists_fg_subalgebra_of_flat_pullback_snd`,
  `AlgebraicGeometry_GeometricallyConnected_descendsAlong_surjective`,
  `AlgebraicGeometry_GeometricallyIrreducible_geometricallyConnected`,
  `AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal_and_le_ker`,
  `AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit`,
  `AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit`,
  `AlgebraicGeometry_Scheme_exists_mem_preimage_le_of_directed_subalgebra`,
  `AlgebraicGeometry_Smooth_isRegularLocalRing_stalk`,
  `AlgebraicGeometry_SubalgebraStages_nonempty_isLimit_cone`,
  `AlgebraicGeometry_exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation`,
  `AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_iSup_eq_top_of_locallyOfFinitePresentation`,
  `AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_isAffine_of_locallyOfFinitePresentation`,
  `AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation`,
  `AlgebraicGeometry_exists_fg_subalgebra_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation`,
  `AlgebraicGeometry_exists_fg_subalgebra_opens_preimage_eq_of_isCompact`,
  `AlgebraicGeometry_exists_fg_subalgebra_pullback_fst_comp_eq_of_locallyOfFiniteType`,
  `AlgebraicGeometry_exists_isPullback_glue_of_isPullback_of_isOpenImmersion`,
  `AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed`,
  `AlgebraicGeometry_isClosedMap_pullback_snd_of_directed_subalgebra`,
  `AlgebraicGeometry_universallyClosed_of_forall_finite_isClosedMap_pullback_snd_mvPolynomial`,
  `GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem`,
  `GoodReductionJacobian_RelativeGroupLaw_exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent`,
  `GoodReductionJacobian_RelativeGroupLaw_exists_isOpenImmersion_irreducibleSpace_range_eq_connectedComponent_finiteIndex`,
  `IsAdicComplete_of_finite_of_isNoetherianRing`,
  `IsLocalRing_exists_isPrime_not_mem_ringKrullDim_quotient_eq_one`,
  `IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates`,
  `IsNoetherianRing_of_ringKrullDim_le_one_of_finiteDimensional_subalgebra`,
  `IsRegularLocalRing_isDomain`,
  `Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct`,
  `Module_Flat_exists_fg_subalgebra_flat_tensorProduct`,
  `Module_Flat_exists_ne_zero_flat_localization_tensorProduct`,
  `Module_Flat_isOpen_setOf_flat_localization_atPrime`,
  `Module_flat_of_comap_maximalIdeal_rTensor_injective`,
  `PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf`, `PresheafOfModules_isSheaf_ihomObj`,
  `Subalgebra_fg_restrictScalars_and_le_of_fg`,
  `Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite`,
  `ValuationSubring_exists_isDiscreteValuationRing_dominates_of_finiteDimensional`,
  `isRegularLocalRing_localization_atPrime_mvPolynomial`,
  `isRegularLocalRing_localization_atPrime_of_etale_of_comap`; and only in `P2M.Sol`,
  `S_isRegularLocalRing_localization_atPrime_of_isStandardSmooth`.
