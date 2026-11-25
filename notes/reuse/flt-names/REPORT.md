STATUS: blocked

**The obstacle, precisely.** Both parts are done and tests (b) and (c) of the brief's 4.6 pass. Test (a)
does not: **1,828 of the 1,831 roots build; 3 do not**, because two modules outside both bodies fail to
compile in the workspace as given, before any edit of mine, with the same errors after it:

- `Langlands.AlgebraicGeometry.Picard.FiniteBasisPicardTangentLifting`, line 51: `failed to synthesize
  instance Epi (StructuredArrow.hom D)` (then `rcases` fails at line 50);
- `Langlands.GroupScheme.Reductive.TorusFibreMaximality`, line 103: typeclass timeout (`ZeroHomClass
  …`, maximum of 20,000 heartbeats) and unsolved goals at line 98.

The roots `Langlands.AbelianScheme.FieldH1LowerBound`, `Langlands.GroupScheme.FiniteFreeAlgebraUnipotentUnits`
and `Langlands.GroupScheme.FiniteFreeAlgebraUnits` import them (13 modules in all depend on the two).
Neither module mentions a renamed name or a restricted product, and the brief allows Library files to be
edited only for the renames and moves, so I did not touch them. Of the three roots, the last two use
`GeometricallyIrreducible.geometricallyConnected` and were edited for the rename (one line each,
`…geometricallyConnectedFLT`); those two edits are the only ones the compiler could not check.

Everything below is committed on branch `work` (commits `8f86562`, `577a514`, `79e5f68`, `68f23c3` after
the base `c51a009`). The working notes are in `FLT-NOTES.md`.

## 1. Part A: the names that clash with weil-conjectures

### The rule

A renamed declaration keeps its name space, and the marker `FLT` is attached to the last component of its
name: at its end (`IsInvertible` → `IsInvertibleFLT`, `isDomain` → `isDomainFLT`, `IsInvertible.pullback`
→ `IsInvertible.pullbackFLT`), except when the last component is a lemma about another renamed declaration
of the same name space, i.e. begins with that declaration's last component and `_` (`tensorPow_zero`,
`tensorPowSection_succ`); then the marker goes right after that part (`tensorPowFLT_zero`,
`tensorPowSectionFLT_succ`). None of the 21 new names exists in `ref/flt-names.tsv`,
`ref/weil-names.txt`, Mathlib, `ref/tree` or the weil-conjectures sources (not even their last component as
a word), so no name had to be chosen otherwise. Generated companions follow their parent
(`IsInvertibleFLT.mk`, `.rec`, `.casesOn`, `.recOn`, the field `IsInvertibleFLT.exists_trivialization`,
`tensorPowFLT.match_1`, `tensorPowSectionFLT.match_1`). The other declarations of the extract built on a
renamed one (`IsInvertible.tensor_monoidalV2`, `tensorPowOneIso`, …) are left alone.

`IsInvertible.pullback` became `IsInvertible.pullbackFLT`, not `IsInvertibleFLT.pullback`: the rule keeps
the name space, and `…Modules.IsInvertible` keeps all the other lemmas of the extract about the structure.

### The table (`FLT-RENAMES.tsv` has the full names, declaring modules and weil-conjectures' modules)

| old full name | new last component | kind | weil-conjectures' declaration of the old name is the same kind of thing |
|---|---|---|---|
| `AdicCompletion.ker_evalₐ_eq_map_pow` | `ker_evalₐ_eq_map_powFLT` | theorem | yes |
| `AlgebraicGeometry.GeometricallyIrreducible.geometricallyConnected` | `geometricallyConnectedFLT` | theorem | yes |
| `AlgebraicGeometry.Scheme.IdealSheafData.comap_ofIdealTop` | `comap_ofIdealTopFLT` | theorem | yes |
| `AlgebraicGeometry.Scheme.Modules.IsInvertible` | `IsInvertibleFLT` | structure (Prop) | no: a structure here, a class there |
| `AlgebraicGeometry.Scheme.Modules.IsInvertible.pullback` | `pullbackFLT` | theorem | no: a theorem here, an instance there (about weil's class) |
| `AlgebraicGeometry.Scheme.Modules.dual` | `dualFLT` | definition (abbrev) | yes (both definitions; each on its own monoidal closed structure) |
| `AlgebraicGeometry.Scheme.Modules.pullback_hom_ext` | `pullback_hom_extFLT` | theorem | yes |
| `AlgebraicGeometry.Scheme.Modules.tensorPow` | `tensorPowFLT` | definition | yes (both definitions; here L^(n+1) = L^n ⊗ L, there M ⊗ M^n) |
| `AlgebraicGeometry.Scheme.Modules.tensorPowSection` | `tensorPowSectionFLT` | definition | yes |
| `AlgebraicGeometry.Scheme.Modules.tensorPowSection_succ` | `tensorPowSectionFLT_succ` | theorem | yes |
| `AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero` | `tensorPowSectionFLT_zero` | theorem | yes |
| `AlgebraicGeometry.Scheme.Modules.tensorPow_succ` | `tensorPowFLT_succ` | theorem | yes |
| `AlgebraicGeometry.Scheme.Modules.tensorPow_zero` | `tensorPowFLT_zero` | theorem | yes |
| `AlgebraicGeometry.Smooth.isRegularLocalRing_stalk` | `isRegularLocalRing_stalkFLT` | theorem | yes |
| `FixedPoints.isLocalRing_subring` | `isLocalRing_subringFLT` | instance | no: an instance here, a theorem there |
| `FixedPoints.isUnit_subring_iff` | `isUnit_subring_iffFLT` | theorem | yes |
| `FixedPoints.mem_maximalIdeal_subring_iff` | `mem_maximalIdeal_subring_iffFLT` | theorem | yes |
| `IsRegularLocalRing.isDomain` | `isDomainFLT` | theorem | no: a theorem here, an instance there |
| `SheafOfModules.monoidalCategory` | `monoidalCategoryFLT` | instance | no: an instance here, a definition there |
| `SheafOfModules.monoidalClosed` | `monoidalClosedFLT` | instance | no: an instance here, a definition there |
| `SheafOfModules.symmetricCategory` | `symmetricCategoryFLT` | instance | no: an instance here, a definition there |

The 33 names of `ref/flt-weil-shared-names.txt` are these 21, four structure companions (`IsInvertible.mk`,
`.rec`, `.casesOn`, `.recOn`), the two `match_1` of `tensorPow` and `tensorPowSection`, and six names that
Lean realizes on demand (`….congr_simp`, `….eq_1`); the brief's "8 on demand" counts the two `match_1`
with them.

**The four theorems that weil-conjectures also has** (statements read in `/srv/ll-flt/weil/WeilConjectures/`,
and checked by Lean with both libraries loaded: each statement proved from the other declaration, both
ways). No use was switched.

| theorem | weil-conjectures | same statement? |
|---|---|---|
| `IsRegularLocalRing.isDomain` | `WeilConjectures/Mathlib/RingTheory/RegularLocalRing/Defs.lean` 218, an `instance` | yes, the identical type |
| `AlgebraicGeometry.Smooth.isRegularLocalRing_stalk` | `…/Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean` 639 | yes; `f` is explicit there, implicit in the extract |
| `AlgebraicGeometry.GeometricallyIrreducible.geometricallyConnected` | `…/Mathlib/AlgebraicGeometry/Geometrically/Integral.lean` 44 | yes (definitionally equal types, same signature) |
| `AlgebraicGeometry.Scheme.IdealSheafData.comap_ofIdealTop` | `…/Mathlib/AlgebraicGeometry/IdealSheaf/Affine.lean` 130 | yes, the same equation; the explicit arguments come in the other order (there `f K`, in the extract `I f`) |

### How the uses were found and changed

The baseline build refreshed the `.ilean` files, which record every syntactic reference with its range and
the module of the referenced constant; `tools/scan_ilean.py` lists them, `tools/gen_flt_edits.py` turned
them into edits (in the range, only the last component is replaced, so the Library's
`Langlands.Scheme.Modules.tensorPow` and every other declaration of the same short name are untouched).
Forms that the `.ilean` files do not record were handled by text: the declaration sites, the items of
`export`/`open … (…)` commands (40 lines: the `P2M/Sol` files mirror root name spaces into `P2MW.…` with
`export`), and the expected `#guard_msgs` texts of `#print axioms`. Result: 892 lines in 195 Lean files
(623 lines in 133 files of the extract, 269 lines in 62 Library files).

Edits forced by the rename beyond the identifiers (recorded on each page):

- **Dot notation on proofs of `IsInvertibleFLT L`** no longer finds lemmas of the name space
  `IsInvertible` (Lean looks in `IsInvertibleFLT`). 79 such applications were written out:
  `h.pullback f` → `Scheme.Modules.IsInvertible.pullbackFLT (hL := h) f` (the morphism is the first
  explicit argument), `h.tensor_monoidalV2 h'` → `Scheme.Modules.IsInvertible.tensor_monoidalV2 h h'`,
  parenthesised where the term is an argument. Each stays on its line; 36 Library lines (and 41 of the extract) now go over 100
  characters, which the Library tolerates elsewhere.
- **Two `export` lines** exported the field `exists_trivialization` and the constructor `mk` from a
  mirrored `namespace IsInvertible`; they now export them from a mirrored `namespace IsInvertibleFLT`.
- **`#guard_msgs`** expected texts (`'FixedPoints.isUnit_subring_iff' depends on axioms …`) follow the names.

No auto-generated instance name depends on a renamed declaration, so no `attribute [-instance]` line broke.

### Pages

Every page of a rename-edited file names the declarations as they now are (171 pages: 135 of the extract,
36 of the Library; `tools/update_pages_partA.py` plus checked manual edits). The pages of the extract say
that the names and proofs are FLT's; those sentences now point to a new final section "Names changed by the
Library (22 November 2026)", which lists for the file what it declares under a new name, the uses renamed,
the dot-notation applications written out, the `export` and `#guard_msgs` changes. Pages that speak of the
upstream source text (`NoetherianLineBundleSeesawStatement.md`: "that source's
`Scheme.Modules.IsInvertible`") were left as they are; three pages of unchanged or import-only files that
named a renamed declaration of the Library's extract were updated.

## 2. Operator note 1: Mathlib's own clashes, `Langlands.MathlibBase`

- `tools/make_mathlib_base.py` makes `Langlands/MathlibBase.lean`: the 8,626 imports of
  `.lake/packages/mathlib/Mathlib.lean` in their order, less `Mathlib.CategoryTheory.GuitartExact.Prod`,
  `Mathlib.RingTheory.Depth.Basic` and `Mathlib.RepresentationTheory.Stabilizer` (8,623 plain `import`
  lines: `Std`, `Batteries`, 8,621 Mathlib modules); no declaration; module docstring and page
  `Langlands/MathlibBase.md` as required. The script stops if one of the three leaves `Mathlib.lean` and warns
  if a Mathlib module starts importing one (none does now).
- Checks: `import Langlands.MathlibBase` + `import WeilConjectures` is accepted; `import Mathlib` +
  `import WeilConjectures` is rejected (`environment already contains
  'CategoryTheory.TwoSquare.GuitartExact.prod'`); the modules loaded by `import Langlands.MathlibBase` are
  those of `import Mathlib` less `Mathlib` and the three (797,155 constants against 797,294).
- `tools/replace_mathlib_import.py . --apply` changed **1,275 workspace files**: in the extract 1,241
  (`Definitions` 61, `OverBase` 5, `P2M` 600, `Theorems` 575), outside it 34 (`Algebra` 2,
  `AlgebraicGeometry` 19, `Cohomology` 4, `CommutativeAlgebra` 7, `GroupScheme` 2). Only that line changed.
- **Point 3 (files that need a declaration of the three modules):** none in the workspace. No workspace
  `.ilean` refers to a constant of the three modules and the full build passed without such a failure,
  so no explicit import was added and no module of the extract lies above such a file.
- **Report of `tools/replace_mathlib_import.py` on `ref/tree`:** it would change 1,375 of 39,685 files:
  `AnthropicFLT/Definitions` 61, `AnthropicFLT/OverBase` 5, `AnthropicFLT/P2M` 600, `AnthropicFLT/Theorems`
  575, `Algebra` 5, `AlgebraicGeometry` 39, `Analysis` 9, `BushnellKutzko` 4, `Cohomology` 4,
  `Combinatorics` 1, `CommutativeAlgebra` 59, `Global` 2, `GroupScheme` 3, `LinearAlgebra` 3,
  `Representation` 5 (134 outside the extract; the note says 137, every pattern I tried finds 134). Files
  importing one of the three modules directly: 3, all `Mathlib.RepresentationTheory.Stabilizer`:
  `Automorphic/BlockShapeLeviIdeleOrbit.lean` (uses `Representation.mem_stabilizer`),
  `Automorphic/GroupSchemeLocallyConstantFiniteLevel.lean` (`Representation.stabilizer`),
  `Representation/Smooth/Transfer/StabilizerStatement.lean` (`ρ.stabilizer`). These three and the 271
  modules of `ref/tree` above them cannot be loaded together with
  `WeilConjectures.RepresentationTheory.GeometricConstituents`; none is in the extract or the workspace.

## 3. The tests of 4.6

| test | result |
|---|---|
| (a) the 1,831 roots | 1,828 build; 3 fail only through the 2 modules that failed before any edit (above). After the renames, the import replacement and part B, `lake build --no-build` on the roots lists exactly those 2 modules as not built. |
| (b) the 101 modules of `Langlands/AnthropicFLT/Definitions/` + `WeilConjectures` | accepted: `lean` exit 0, no message (5-7 s) |
| (c) the 1,506 modules of the extract + `WeilConjectures` | accepted: exit 0, no message (6 s); 39,297 modules loaded; also with `WeilConjectures` imported first. With both loaded, the old names resolve to weil-conjectures' declarations and the new ones to the extract's. |

The six names that Lean realizes on demand (`Algebra.tensorH1CotangentOfFlat.congr_simp`,
`Scheme.Modules.pullbackCongr.eq_1`, `GradedRingHom.mk.congr_simp`, `Ideal.ofList.eq_1`,
`IsPreconnected.eq_1`, `PresheafOfModules.freeObj.eq_1`) are present in both compiled environments and do
not stop the import: the one of the module loaded first is kept, in either order. Lean reported no
further clash, so nothing beyond the 21 was renamed.

## 4. The script for the whole Library

The script and its two tables are not kept with this report; the edits it made are listed in
`FLT-LIBRARY-EDITS.tsv` and the renames in `FLT-RENAMES.tsv`.

`tools/rename_flt_clashes.py <tree> [--apply]` performs on a tree exactly the edits of part A
(`tools/rename_flt_clashes.table.json`, built by `tools/build_rename_table.py` from the commits `c51a009`
→ `577a514`, import lines excluded): 892 Lean lines by line (old text at the line, or at the one line of
the file that has it), 171 pages by whole text when the page is the old page; everything else is reported
and left alone. Checked: applied to a tree of the base versions of all these files, then with
`tools/replace_mathlib_import.py`, the result equals the workspace byte for byte; a second run changes
nothing. On `ref/tree` (dry run): all 195 files and 892 lines apply, no problem; pages are absent there.

Its report lists the files of the tree that it does not edit, that have the module declaring a renamed
short name in their import closure, and that mention that name in a form that could resolve to it
(distinctive names anywhere; `dual`, `pullback`, `isDomain`, … only qualified, in dot notation, or bare in a
file that opens the name space; dot notation `.lemma` of the `IsInvertible` lemmas; `.pullback` on a term
that is visibly an invertibility proof).

**Hidden uses found by it, and fixed.** Four Library files that are not in the workspace use renamed
declarations by dot notation, a form the original search for name forms did not catch:
`AlgebraicGeometry/ProjectiveSpace/EvaluationBracketAtlas.lean` (lines 124, 241) and
`EvaluationBracketFibres.lean` (164, 216, 325) write `(Q r).tensorPow n` with `Q r : X.Modules`;
`AbelianScheme/PolarizedFiniteLevel/TorsionBracketMapReduction.lean` (115) writes `(…).tensorPow n`;
`AlgebraicGeometry/NoetherianApproximation/LineBundleQuotientDescent.lean` (92, 109) writes `h.pullback u` on
invertibility proofs. I compiled copies of them, together with the modules they need that the workspace
lacks, against the renamed workspace (`tools/compile_outside.py`, own olean directory under `.tmp/`): the
unchanged copies fail (`Invalid field tensorPow`, `Invalid field pullback`), the copies with the 8 edited
lines compile. These 8 edits are part of the script's table (section `lean_outside`,
`tools/rename_flt_clashes.outside.json`), so the script applies them to the whole Library; they are not in
the workspace's commits, since the files are not in the workspace.

**The 81 files of the report on `ref/tree`, with my judgement of each.** None is a use of a renamed
declaration. 37 are in the workspace and were compiled after the rename; 20 were compiled as copies
(110 modules in all, 153 s); 24 were judged by reading, with the receiving types checked in the Library's
definitions.

| # | file | mentions († = only in comments) | how judged | judgement |
|---|---|---|---|---|
| 1 | `Langlands/AbelianScheme/AffineSectionAmple.lean` | `tensorPow` | copy compiled against the renamed workspace, with the modules it needs that the workspace lacks | compiles unchanged: no use of a renamed declaration |
| 2 | `Langlands/AbelianScheme/AlgClosedFieldAmpleCubeSeparationReduction.lean` | `tensorPow`†, `tensorPow` | copy compiled against the renamed workspace, with the modules it needs that the workspace lacks | compiles unchanged: no use of a renamed declaration |
| 3 | `Langlands/AbelianScheme/AmpleNonvanishingSection.lean` | `tensorPow` | copy compiled against the renamed workspace, with the modules it needs that the workspace lacks | compiles unchanged: no use of a renamed declaration |
| 4 | `Langlands/AbelianScheme/AmpleSectionIsogenyDegree.lean` | `tensorPow` | copy compiled against the renamed workspace, with the modules it needs that the workspace lacks | compiles unchanged: no use of a renamed declaration |
| 5 | `Langlands/AbelianScheme/EndomorphismEulerDegree.lean` | `tensorPow` | copy compiled against the renamed workspace, with the modules it needs that the workspace lacks | compiles unchanged: no use of a renamed declaration |
| 6 | `Langlands/AbelianScheme/PolarizedFiniteLevel/CubicBundlePolarizationDeterminationProof.lean` | `.dual`, `dual (bare)`† | copy compiled against the renamed workspace, with the modules it needs that the workspace lacks | compiles unchanged: no use of a renamed declaration |
| 7 | `Langlands/AbelianScheme/PolarizedFiniteLevel/CubicEmbeddingTorsionEquations.lean` | `tensorPow` | compiled in the workspace after the rename | no use of a renamed declaration (its `.ilean` has none): the names are other declarations |
| 8 | `Langlands/AbelianScheme/PolarizedFiniteLevel/CubicPowerFibreCohomology.lean` | `tensorPow`, `.dual` | compiled in the workspace after the rename | no use of a renamed declaration (its `.ilean` has none): the names are other declarations |
| 9 | `Langlands/AbelianScheme/PolarizedFiniteLevel/CubicTorsionHyperplaneBoundAssembly.lean` | `tensorPow` | compiled in the workspace after the rename | no use of a renamed declaration (its `.ilean` has none): the names are other declarations |
| 10 | `Langlands/AbelianScheme/PolarizedFiniteLevel/FrameEmbeddingReduction.lean` | `.dual`, `dual (bare)`† | compiled in the workspace after the rename | no use of a renamed declaration (its `.ilean` has none): the names are other declarations |
| 11 | `Langlands/AbelianScheme/PolarizedFiniteLevel/FrameHilbertClassifying.lean` | `hψ.pullback`, `hbar.pullback` | read | `hψ` and `hbar` are a Library embedding property and a `Realizes` proof, not invertibility proofs: their `.pullback` are other lemmas |
| 12 | `Langlands/AbelianScheme/PolarizedFiniteLevel/TorsionEvaluationLinePowers.lean` | `tensorPow`, `dual (bare)`† | copy compiled against the renamed workspace, with the modules it needs that the workspace lacks | compiles unchanged: no use of a renamed declaration |
| 13 | `Langlands/AbelianScheme/PolarizedFiniteLevel/ZariskiGluingPolarization.lean` | `.dual`, `.dual`† | read | `WB.dual P`, `Wb.dual P`, `(gluedDualWitness …).dual P` with dual witnesses: the Library's dual abelian scheme, not `Scheme.Modules.dual` |
| 14 | `Langlands/AlgebraicGeometry/Modules/FibreNeighbourhoodSectionBridge.lean` | `tensorPow` | compiled in the workspace after the rename | no use of a renamed declaration (its `.ilean` has none): the names are other declarations |
| 15 | `Langlands/AlgebraicGeometry/Modules/IdealAdicFibreSerre.lean` | `tensorPow` | compiled in the workspace after the rename | no use of a renamed declaration (its `.ilean` has none): the names are other declarations |
| 16 | `Langlands/AlgebraicGeometry/Modules/ProperFibrePowerSectionLiftingLocalCase.lean` | `tensorPow` | compiled in the workspace after the rename | no use of a renamed declaration (its `.ilean` has none): the names are other declarations |
| 17 | `Langlands/AlgebraicGeometry/Modules/ProperFibrePowerSectionLiftingLocalReduction.lean` | `tensorPow` | compiled in the workspace after the rename | no use of a renamed declaration (its `.ilean` has none): the names are other declarations |
| 18 | `Langlands/AlgebraicGeometry/Modules/SmoothProperLineBundleFiniteCohomologyProof.lean` | `.tensorPow` | compiled in the workspace after the rename | no use of a renamed declaration (its `.ilean` has none): the names are other declarations |
| 19 | `Langlands/AlgebraicGeometry/Picard/AffineBaseAmpleLocality.lean` | `tensorPow` | compiled in the workspace after the rename | no use of a renamed declaration (its `.ilean` has none): the names are other declarations |
| 20 | `Langlands/AlgebraicGeometry/Picard/AlgClosedFieldAmpleEulerInverseScalingAssembly.lean` | `tensorPow` | compiled in the workspace after the rename | no use of a renamed declaration (its `.ilean` has none): the names are other declarations |
| 21 | `Langlands/AlgebraicGeometry/Picard/AlgClosedFieldAmpleMumfordEulerSquareProof.lean` | `dual (bare)`†, `dual (bare)` | compiled in the workspace after the rename | no use of a renamed declaration (its `.ilean` has none): the names are other declarations |
| 22 | `Langlands/AlgebraicGeometry/Picard/AlgClosedFieldEulerInverseSymmetryProof.lean` | `tensorPow` | compiled in the workspace after the rename | no use of a renamed declaration (its `.ilean` has none): the names are other declarations |
| 23 | `Langlands/AlgebraicGeometry/Picard/AlgClosedFieldMumfordDualEulerProof.lean` | `dual (bare)`† | compiled in the workspace after the rename | no use of a renamed declaration (its `.ilean` has none): the names are other declarations |
| 24 | `Langlands/AlgebraicGeometry/Picard/AlgClosedFieldPoincareTangentSectionsProof.lean` | `dual (bare)`† | compiled in the workspace after the rename | no use of a renamed declaration (its `.ilean` has none): the names are other declarations |
| 25 | `Langlands/AlgebraicGeometry/Picard/AmpleMumfordMapIsogeny.lean` | `.dual`, `dual (bare)`† | copy compiled against the renamed workspace, with the modules it needs that the workspace lacks | compiles unchanged: no use of a renamed declaration |
| 26 | `Langlands/AlgebraicGeometry/Picard/CocycleLineBundlePower.lean` | `tensorPow` | copy compiled against the renamed workspace, with the modules it needs that the workspace lacks | compiles unchanged: no use of a renamed declaration |
| 27 | `Langlands/AlgebraicGeometry/Picard/DeterminantDualFrames.lean` | `.dual`, `dual (bare)`†, `dual (bare)` | copy compiled against the renamed workspace, with the modules it needs that the workspace lacks | compiles unchanged: no use of a renamed declaration |
| 28 | `Langlands/AlgebraicGeometry/Picard/DualNumberCocycleBundles.lean` | `dual (bare)`† | compiled in the workspace after the rename | no use of a renamed declaration (its `.ilean` has none): the names are other declarations |
| 29 | `Langlands/AlgebraicGeometry/Picard/DualNumberDeformationScaling.lean` | `dual (bare)`† | compiled in the workspace after the rename | no use of a renamed declaration (its `.ilean` has none): the names are other declarations |
| 30 | `Langlands/AlgebraicGeometry/Picard/DualNumberPointedDeformations.lean` | `dual (bare)`† | compiled in the workspace after the rename | no use of a renamed declaration (its `.ilean` has none): the names are other declarations |
| 31 | `Langlands/AlgebraicGeometry/Picard/DualNumberSectionTrivialization.lean` | `dual (bare)`† | compiled in the workspace after the rename | no use of a renamed declaration (its `.ilean` has none): the names are other declarations |
| 32 | `Langlands/AlgebraicGeometry/Picard/DualOriginMumfordClassifier.lean` | `dual (bare)`† | compiled in the workspace after the rename | no use of a renamed declaration (its `.ilean` has none): the names are other declarations |
| 33 | `Langlands/AlgebraicGeometry/Picard/DualSchemeQuotientFactorization.lean` | `dual (bare)`† | copy compiled against the renamed workspace, with the modules it needs that the workspace lacks | compiles unchanged: no use of a renamed declaration |
| 34 | `Langlands/AlgebraicGeometry/Picard/DualSchemeSubalgebraFactorization.lean` | `dual (bare)`† | compiled in the workspace after the rename | no use of a renamed declaration (its `.ilean` has none): the names are other declarations |
| 35 | `Langlands/AlgebraicGeometry/Picard/DualSchemeTangentH1.lean` | `dual (bare)`† | compiled in the workspace after the rename | no use of a renamed declaration (its `.ilean` has none): the names are other declarations |
| 36 | `Langlands/AlgebraicGeometry/Picard/DvrAbelianAffineSection.lean` | `tensorPow` | compiled in the workspace after the rename | no use of a renamed declaration (its `.ilean` has none): the names are other declarations |
| 37 | `Langlands/AlgebraicGeometry/Picard/DvrAbelianGeometry.lean` | `tensorPow` | compiled in the workspace after the rename | no use of a renamed declaration (its `.ilean` has none): the names are other declarations |
| 38 | `Langlands/AlgebraicGeometry/Picard/FieldDualSchemeSurjectionProof.lean` | `dual (bare)`† | copy compiled against the renamed workspace, with the modules it needs that the workspace lacks | compiles unchanged: no use of a renamed declaration |
| 39 | `Langlands/AlgebraicGeometry/Picard/FieldFiniteMumfordMapSurjectiveProof.lean` | `dual (bare)`† | compiled in the workspace after the rename | no use of a renamed declaration (its `.ilean` has none): the names are other declarations |
| 40 | `Langlands/AlgebraicGeometry/Picard/MumfordMapPicardClass.lean` | `.dual`, `dual (bare)`† | copy compiled against the renamed workspace, with the modules it needs that the workspace lacks | compiles unchanged: no use of a renamed declaration |
| 41 | `Langlands/AlgebraicGeometry/Picard/MumfordRosatiEulerDegreeAssembly.lean` | `tensorPow`†, `.dual` | copy compiled against the renamed workspace, with the modules it needs that the workspace lacks | compiles unchanged: no use of a renamed declaration |
| 42 | `Langlands/AlgebraicGeometry/Picard/MumfordRosatiMixedEulerTraceCharZeroReduction.lean` | `.dual` | read | `W.dual P` with `W : DualWitness …`/`DualData …`: the Library's dual abelian scheme, not `Scheme.Modules.dual` |
| 43 | `Langlands/AlgebraicGeometry/Picard/MumfordRosatiMixedEulerTraceReduction.lean` | `.dual` | read | `W.dual P` with `W : DualWitness …`/`DualData …`: the Library's dual abelian scheme, not `Scheme.Modules.dual` |
| 44 | `Langlands/AlgebraicGeometry/Picard/PoincareDirectImageSupport.lean` | `dual (bare)`† | compiled in the workspace after the rename | no use of a renamed declaration (its `.ilean` has none): the names are other declarations |
| 45 | `Langlands/AlgebraicGeometry/Picard/ProperFibreAmpleFromSectionLifting.lean` | `tensorPow` | compiled in the workspace after the rename | no use of a renamed declaration (its `.ilean` has none): the names are other declarations |
| 46 | `Langlands/AlgebraicGeometry/Picard/RelativeMumfordFibreImage.lean` | `dual (bare)`† | copy compiled against the renamed workspace, with the modules it needs that the workspace lacks | compiles unchanged: no use of a renamed declaration |
| 47 | `Langlands/AlgebraicGeometry/Picard/RigidifiedDeformationClasses.lean` | `dual (bare)`† | compiled in the workspace after the rename | no use of a renamed declaration (its `.ilean` has none): the names are other declarations |
| 48 | `Langlands/AlgebraicGeometry/Picard/RosatiAlgebraLawsProof.lean` | `.dual` | read | `W.dual P` with `W : DualWitness …`/`DualData …`: the Library's dual abelian scheme, not `Scheme.Modules.dual` |
| 49 | `Langlands/AlgebraicGeometry/Picard/RosatiTraceSymmetry.lean` | `.dual` | read | `W.dual P` with `W : DualWitness …`/`DualData …`: the Library's dual abelian scheme, not `Scheme.Modules.dual` |
| 50 | `Langlands/AlgebraicGeometry/Picard/SectionZeroIdealDual.lean` | `.dual`, `dual (bare)`†, `dual (bare)` | compiled in the workspace after the rename | no use of a renamed declaration (its `.ilean` has none): the names are other declarations |
| 51 | `Langlands/AlgebraicGeometry/Picard/UniversalRigidifiedTangentScaling.lean` | `dual (bare)`† | compiled in the workspace after the rename | no use of a renamed declaration (its `.ilean` has none): the names are other declarations |
| 52 | `Langlands/AlgebraicGeometry/ProjectiveBundle/EvaluationMorphism.lean` | `.dual` | compiled in the workspace after the rename | no use of a renamed declaration (its `.ilean` has none): the names are other declarations |
| 53 | `Langlands/AlgebraicGeometry/ProjectiveBundle/EvaluationTwist.lean` | `.dual` | compiled in the workspace after the rename | no use of a renamed declaration (its `.ilean` has none): the names are other declarations |
| 54 | `Langlands/AlgebraicGeometry/ProjectiveBundle/FrameAtlasTwist.lean` | `.dual`, `dual (bare)`† | compiled in the workspace after the rename | no use of a renamed declaration (its `.ilean` has none): the names are other declarations |
| 55 | `Langlands/AlgebraicGeometry/ProjectiveBundle/FrameAtlasTwistChart.lean` | `dual (bare)`† | copy compiled against the renamed workspace, with the modules it needs that the workspace lacks | compiles unchanged: no use of a renamed declaration |
| 56 | `Langlands/AlgebraicGeometry/ProjectiveBundle/FrameChoiceTwist.lean` | `.dual`, `dual (bare)`† | compiled in the workspace after the rename | no use of a renamed declaration (its `.ilean` has none): the names are other declarations |
| 57 | `Langlands/AlgebraicGeometry/ProjectiveBundle/FrameChoiceTwistChart.lean` | `dual (bare)`† | copy compiled against the renamed workspace, with the modules it needs that the workspace lacks | compiles unchanged: no use of a renamed declaration |
| 58 | `Langlands/AlgebraicGeometry/ProjectiveBundle/TensorFrameOverlap.lean` | `.dual` | compiled in the workspace after the rename | no use of a renamed declaration (its `.ilean` has none): the names are other declarations |
| 59 | `Langlands/AlgebraicGeometry/ProjectiveBundle/TensorTwistTransition.lean` | `.dual`, `dual (bare)`† | compiled in the workspace after the rename | no use of a renamed declaration (its `.ilean` has none): the names are other declarations |
| 60 | `Langlands/AlgebraicGeometry/ProjectiveSpace/TwistTensorPowers.lean` | `tensorPow` | compiled in the workspace after the rename | no use of a renamed declaration (its `.ilean` has none): the names are other declarations |
| 61 | `Langlands/GroupScheme/IdentityJetAmpleTransfer.lean` | `.dual`, `dual (bare)`† | read | `.dual` of a `LineBundle` (`smoothLieDeterminant`, `lieDeterminant`, `finiteLocallyFreeDeterminant` return `LineBundle`) or `PresheafLineBundle`: the Library's `LineBundle.dual`, not `Scheme.Modules.dual` |
| 62 | `Langlands/GroupScheme/IdentityJetDeterminantLine.lean` | `tensorPow` | copy compiled against the renamed workspace, with the modules it needs that the workspace lacks | compiles unchanged: no use of a renamed declaration |
| 63 | `Langlands/GroupScheme/IdentityJetGrassmannianAmple.lean` | `.dual`, `dual (bare)`† | read | `.dual` of a `LineBundle` (`smoothLieDeterminant`, `lieDeterminant`, `finiteLocallyFreeDeterminant` return `LineBundle`) or `PresheafLineBundle`: the Library's `LineBundle.dual`, not `Scheme.Modules.dual` |
| 64 | `Langlands/GroupScheme/IdentityJetLieDeterminant.lean` | `tensorPow`, `.dual`, `dual (bare)`† | copy compiled against the renamed workspace, with the modules it needs that the workspace lacks | compiles unchanged: no use of a renamed declaration |
| 65 | `Langlands/GroupScheme/IdentityJetRankReduction.lean` | `.dual`, `dual (bare)`† | read | `.dual` of a `LineBundle` (`smoothLieDeterminant`, `lieDeterminant`, `finiteLocallyFreeDeterminant` return `LineBundle`) or `PresheafLineBundle`: the Library's `LineBundle.dual`, not `Scheme.Modules.dual` |
| 66 | `Langlands/GroupScheme/RelativeLevi/ParabolicDeterminantComponents.lean` | `.dual` | read | `.dual` of a `LineBundle` (`smoothLieDeterminant`, `lieDeterminant`, `finiteLocallyFreeDeterminant` return `LineBundle`) or `PresheafLineBundle`: the Library's `LineBundle.dual`, not `Scheme.Modules.dual` |
| 67 | `Langlands/GroupScheme/RelativeLevi/ParabolicDeterminantDualAmpleStatement.lean` | `.dual` | read | `.dual` of a `LineBundle` (`smoothLieDeterminant`, `lieDeterminant`, `finiteLocallyFreeDeterminant` return `LineBundle`) or `PresheafLineBundle`: the Library's `LineBundle.dual`, not `Scheme.Modules.dual` |
| 68 | `Langlands/GroupScheme/RelativeLevi/ParabolicDeterminantPolarization.lean` | `.dual` | read | `.dual` of a `LineBundle` (`smoothLieDeterminant`, `lieDeterminant`, `finiteLocallyFreeDeterminant` return `LineBundle`) or `PresheafLineBundle`: the Library's `LineBundle.dual`, not `Scheme.Modules.dual` |
| 69 | `Langlands/GroupScheme/RelativeLevi/ParabolicDeterminantPresheaf.lean` | `.dual` | read | `.dual` of a `LineBundle` (`smoothLieDeterminant`, `lieDeterminant`, `finiteLocallyFreeDeterminant` return `LineBundle`) or `PresheafLineBundle`: the Library's `LineBundle.dual`, not `Scheme.Modules.dual` |
| 70 | `Langlands/GroupScheme/RelativeLevi/ParabolicQuotientJetPositivity.lean` | `.dual`, `dual (bare)`† | read | `.dual` of a `LineBundle` (`smoothLieDeterminant`, `lieDeterminant`, `finiteLocallyFreeDeterminant` return `LineBundle`) or `PresheafLineBundle`: the Library's `LineBundle.dual`, not `Scheme.Modules.dual` |
| 71 | `Langlands/Shimura/PEL/HarrisIntegralCMClosedActionLocus.lean` | `.dual` | read | `W.dual P` with `W : DualWitness …`/`DualData …`: the Library's dual abelian scheme, not `Scheme.Modules.dual` |
| 72 | `Langlands/Shimura/PEL/HarrisIntegralCMRosatiReflection.lean` | `.dual` | read | `W.dual P` with `W : DualWitness …`/`DualData …`: the Library's dual abelian scheme, not `Scheme.Modules.dual` |
| 73 | `Langlands/Shimura/PEL/HarrisIntegralRosatiClosedLocus.lean` | `dual (bare)`† | read | mentions in comments only (the English word “dual”) |
| 74 | `Langlands/Shimura/PEL/HarrisProjectiveCMActionScheme.lean` | `.dual`, `dual (bare)`† | read | `W.dual P` with `W : DualWitness …`/`DualData …`: the Library's dual abelian scheme, not `Scheme.Modules.dual` |
| 75 | `Langlands/Shimura/PEL/HarrisTaylorCMDivisionGeometricReduction.lean` | `dual (bare)`† | read | mentions in comments only (the English word “dual”) |
| 76 | `Langlands/Shimura/PEL/HarrisTaylorCMDvrPolarization.lean` | `.dual` | read | `W.dual P` with `W : DualWitness …`/`DualData …`: the Library's dual abelian scheme, not `Scheme.Modules.dual` |
| 77 | `Langlands/Shimura/PEL/HarrisTaylorCMDvrPolarizationBundle.lean` | `.dual` | copy compiled against the renamed workspace, with the modules it needs that the workspace lacks | compiles unchanged: no use of a renamed declaration |
| 78 | `Langlands/Shimura/PEL/HarrisTaylorCMDvrPolarizedAction.lean` | `.dual` | read | `W.dual P` with `W : DualWitness …`/`DualData …`: the Library's dual abelian scheme, not `Scheme.Modules.dual` |
| 79 | `Langlands/Shimura/PEL/HarrisTaylorCMGeometricFiniteOrderReduction.lean` | `.dual` | read | `W.dual P` with `W : DualWitness …`/`DualData …`: the Library's dual abelian scheme, not `Scheme.Modules.dual` |
| 80 | `Langlands/Shimura/PEL/HarrisTaylorCMOriginalActionLift.lean` | `dual (bare)`† | read | mentions in comments only (the English word “dual”) |
| 81 | `Langlands/Shimura/PEL/HarrisTaylorCMPolarizedPowerModel.lean` | `.dual`, `dual (bare)`† | read | `W.dual P` with `W : DualWitness …`/`DualData …`: the Library's dual abelian scheme, not `Scheme.Modules.dual` |

## 5. Part B: the nine restricted-product files

### Comparison with the Imperial files (commit `0198058`)

The nine files declare 42 public names in root name spaces (and 3 private ones). Compiling copies of the
Imperial `Basic.lean`, `Equiv.lean` and `TensorPi.lean` on the same Lean and Mathlib shows **17** of the
42 in that environment, among them four that a text scan does not see, because they are generated:
`AddEquiv.restrictedProductCongrRight` (by `to_additive` from `MulEquiv.restrictedProductCongrRight`),
`Equiv.restrictedProductCongrRight_apply` and `_symm_apply` (by `@[simps]`), and
`AddEquiv.restrictedProductCongrRight_apply` (by `simps! apply`). `TensorRestrictedProduct.lean` (which
needs `FLT.Mathlib.Algebra.IsDirectLimit`, not among the reference files) declares **10** more by its
text. So **27** of the 42 have the same name in the Imperial project (the survey's 23 plus the four
generated ones); **15** are the Library's own.

### What was done

- The 27 Imperial-named declarations keep their names and statements. 23 moved to three staged files
  mirroring the Imperial files, made by `tools/make_staged_files.py`, which copies the Imperial line ranges
  verbatim and marks every piece of Library text with `-- Library text:`; each header gives project, commit,
  file, line ranges, licence Apache-2.0, "staged for Mathlib", "delete when the Library's Mathlib has these
  declarations", and every difference:
  - `Langlands/Mathlib/Topology/Algebra/RestrictedProduct/Basic.lean` (Imperial `Basic.lean` 8-12, 38-88):
    `mapAlongLinearMap`, `mapAlongLinearMap_apply`, `inclusionLinearMap`;
  - `Langlands/Mathlib/Topology/Algebra/RestrictedProduct/Equiv.lean` (Imperial `Equiv.lean` 31-49, 105-126,
    520-589): the three congruences, `Equiv.restrictedProductCongrRight_apply`, `_symm_apply`,
    `AddEquiv.restrictedProductCongrRight_apply` and the eight flattening declarations;
  - `Langlands/Mathlib/DedekindDomain/FiniteAdeleRing/TensorRestrictedProduct.lean` (Imperial
    `TensorRestrictedProduct.lean` 24-91): `rangeLTensor`, `rangeLTensorLeft`, `lTensor`, `lTensorLeft`,
    `lTensor_tmul`, `lTensorLeft_tmul`. The Imperial project keeps this file outside `FLT/Mathlib/`; the
    header says so.
- **Four Imperial-named declarations stay where they were**, in
  `Langlands/LinearAlgebra/RestrictedProduct/TensorEquiv.lean`, under their root names: `lTensorEquiv`,
  `lTensorEquiv_tmul`, `lTensorEquivLeft`, `lTensorEquivLeft_tmul`. They take their bijectivity from the
  Library's own theorem `Langlands.LinearAlgebra.RestrictedProduct.tensorRestrictedProductComparison_proof`,
  which is proved from the staged `TensorRestrictedProduct` module, so a staged file cannot hold them
  without an import cycle; Imperial's proof (`lTensor_bijective`, a direct-limit argument with
  `lTensorPrincipalEquiv`, `tmulEquivRangeLTensor`, `TensorPi` and `IsDirectLimit`) is not used by the
  Library and would duplicate its own. The file's header and page say this and that they are to be deleted
  when Mathlib has them. This is the one departure from the brief's 5.2.
- The 15 Library-own declarations stay in their files, with the prefix `Langlands.LinearAlgebra.`, the name
  space of their directory (`Langlands.LinearAlgebra.RestrictedProduct.flattenLinearEquiv`,
  `Langlands.LinearAlgebra.RestrictedProduct.tensorPiComparison_proof`,
  `Langlands.LinearAlgebra.LinearEquiv.restrictedProductCongrRight_apply`, …). I first used
  `Langlands.RestrictedProduct`; it broke `FiniteAdeleTensorProof`: inside a name space `Langlands.…`, Lean
  takes `open scoped RestrictedProduct` to mean `Langlands.RestrictedProduct` (the innermost match), so
  Mathlib's `Πʳ` notation was no longer opened, and 68 files of `ref/tree` open `RestrictedProduct` inside a
  `Langlands…` name space (none inside `Langlands.LinearAlgebra…`, and none opens `LinearEquiv` or `AddEquiv`
  there).
- `Tensor.lean`, all of whose declarations moved, stays as a module that imports the two staged modules
  and declares nothing: it is a root and `TensorStatement` imports it. `Equiv.lean` imports the staged
  `Equiv`. The statement and proof files keep their division; they open `RestrictedProduct` before their
  name space (not `TensorPi*`, which use nothing of it), and their statements change only in the names.
- Uses: inside the directory; `Global/FiniteProjectivePiTensor.lean` line 18 (the only use outside it of a
  name that changed, in the workspace and in all of `ref/tree`). `Global/AdelicFunctoriality/
  FiniteAdeleTensorProof.lean` uses only names that did not change and needed no edit;
  `Global/CurvePlaceIntegralTensor.lean` uses none of the 42. No use was by dot notation.
- Statements, checked against a dump of all 42 types before part B: 22 identical; the flattening declarations
  identical up to the name of a universe parameter (`u_3` → `u_4`, from Imperial's unused section variable
  `H`); the three congruences and their coordinate lemmas differ only in the order of the implicit arguments
  (Imperial's: `A₁ A₂` and the `SetLike` data before `𝓕`), and the nine old statements, with the old
  variable order, are each proved by the declarations as they are now, applied to their explicit arguments
  only; the rest differ only by the renamed constants.

### The table (`FLT-RESTRICTED-PRODUCT.tsv` has all 42 rows: where it was, where it is, name, whether the Imperial project declares it, whether its text is now Imperial's)

| group | declarations | where now | name | text now Imperial's? |
|---|---|---|---|---|
| linear maps | `RestrictedProduct.mapAlongLinearMap`, `_apply`, `inclusionLinearMap` | staged `Basic` | unchanged | yes, verbatim |
| tensor maps | `RestrictedProduct.rangeLTensor`, `rangeLTensorLeft`, `lTensor`, `lTensorLeft`, `lTensor_tmul`, `lTensorLeft_tmul` | staged `TensorRestrictedProduct` | unchanged | yes, verbatim |
| congruences | `LinearEquiv.restrictedProductCongrRight` | staged `Equiv` | unchanged | yes, verbatim |
| | `Equiv.restrictedProductCongrRight` | staged `Equiv` | unchanged | yes except: no `@[simps]`; the two inverse laws are Library text |
| | `AddEquiv.restrictedProductCongrRight`; `Equiv.…_apply`, `Equiv.…_symm_apply`, `AddEquiv.…_apply` | staged `Equiv` | unchanged | no (Library text; see below) |
| flattening | `RestrictedProduct.flatten`, `flatten_apply`, `flattenEquiv`, `flatten_equiv_apply`, `flatten_equiv_symm_apply`, `flattenEquiv'`, `flatten_equiv'_apply`, `flatten_equiv'_symm_apply` | staged `Equiv` | unchanged | yes, verbatim |
| equivalences | `RestrictedProduct.lTensorEquiv`, `_tmul`, `lTensorEquivLeft`, `_tmul` | `LinearAlgebra/RestrictedProduct/TensorEquiv` (unchanged place) | unchanged | no: Imperial statements, Library proofs |
| Library's own | `AddEquiv.…_symm_apply`, `LinearEquiv.…_apply`, `LinearEquiv.…_symm_apply`, `RestrictedProduct.flattenLinearEquiv` + 5 | `LinearAlgebra/RestrictedProduct/Equiv` (unchanged place) | prefix `Langlands.LinearAlgebra.` | no (not Imperial's) |
| | `TensorRestrictedProductComparison`, `tensorRestrictedProductComparison_proof`, `TensorPiComparison`, `tensorPiComparison_proof`, `TensorEquivInverseLaws`, `tensorEquivInverseLaws_proof` (`RestrictedProduct.`) | their statement/proof files (unchanged place) | prefix `Langlands.LinearAlgebra.` | no (not Imperial's) |

### What differs from the Imperial text, and why

- Everywhere: the module-system keywords (`module`, `public import`, `@[expose] public section`) are removed,
  as the Library's files are ordinary files; the imports are those the kept declarations need; the module
  docstrings are the Library's; only the declarations the Library uses are taken.
- `Equiv.restrictedProductCongrRight`: Imperial's `@[simps]` is dropped, because it generates
  `Equiv.restrictedProductCongrRight_apply`/`_symm_apply` with other statements (the whole map,
  `⇑e x = map … x`) than the Library's coordinate lemmas of the same names (`… x i = φ i (x i)`), whose names
  and statements are kept. Its inverse laws use the Library's two lines (`Equiv.symm_apply_apply`,
  `Equiv.apply_symm_apply`): Imperial's `by ext; simp` makes no progress in an ordinary file at this Lean
  and Mathlib (Mathlib's `RestrictedProduct.map_apply` fires only with
  `backward.isDefEq.respectTransparency` off), and I did not add that option.
- `AddEquiv.restrictedProductCongrRight` is the Library's direct definition (same data): Imperial's comes
  from `to_additive` of `MulEquiv.restrictedProductCongrRight`, which would bring the multiplicative version,
  unused by the Library, and a `simps!` lemma `AddEquiv.restrictedProductCongrRight_apply` with another
  statement than the Library's lemma of that name.
- Consequence to note for the Mathlib bump: `Equiv.restrictedProductCongrRight_apply`, `_symm_apply` and
  `AddEquiv.restrictedProductCongrRight_apply` have Imperial's names but not Imperial's statements; when
  Mathlib takes the Imperial file, their uses in the Library must move to Mathlib's forms.
- The staged `TensorRestrictedProduct` keeps Imperial's `set_option backward.isDefEq.respectTransparency
  false in` before `lTensor`, which the Library's earlier port had dropped; it is Imperial text and local to
  that declaration.
- Imperial's unused section variables (`A₁ A₂` in `Basic`, `H D` in the flattening) are back; this is what
  renames the flattening's universe parameter.

### Pages

The three staged files have new pages giving the origin as the header does and saying what is Imperial
text and what is not (composed from the sections of the old pages that describe these declarations).
`Equiv.md` and `Tensor.md` are rewritten to describe the files as they are; `TensorEquiv.md` and the six
statement and proof pages have the new names and a section "Names and place (22 November 2026)";
`Global/FiniteProjectivePiTensor.md` names the theorem's new name.

## 6. Edits outside the two bodies

`FLT-LIBRARY-EDITS.tsv` (113 rows): for part A, the 62 Library Lean files and 36 pages with what changed in
each, `Langlands/MathlibBase.lean` and its page, the import replacement as one row with the counts by
directory, and the 4 files not in the workspace that the script edits; for part B, the six new staged
files and pages and `Global/FiniteProjectivePiTensor` with its page. Nothing outside them was edited.
No `sorry`, `admit`, `axiom`, `native_decide` or `unsafe` was added, and no file-wide option; the only
`set_option … in` lines added are the two of the Imperial text in the staged `TensorRestrictedProduct`.

## 7. Build times (Lean processes on CPUs 24-31)

| build | time |
|---|---|
| baseline, all roots, before any edit (29 out-of-date modules and their dependents) | 1,063 s (2 failures) |
| round 1, renames only (stopped from outside at 15,304 of 15,309 jobs) | not timed to the end |
| round 2, full rebuild after renames + import replacement (every module) | **5,645 s** (2 failures, the same) |
| part B: the directory and its importers / then all roots | 12 s / 14 s |
| tests (b) and (c) | 5-7 s each (the brief's estimate of 3 min for weil-conjectures' import did not show on a warm cache) |
| copies outside the workspace (110 modules, 8 jobs) | 153 s |

## 8. What was not done

- The two modules that failed before any edit were not repaired (rules), so test (a) stops at 1,828 of
  1,831, and the one-line edits of `GroupScheme/FiniteFreeAlgebraUnits.lean` and
  `FiniteFreeAlgebraUnipotentUnits.lean` could not be compiled.
- The four `lTensorEquiv…` declarations were not moved to a staged file (reason in section 5).
- The 8 edits of the four Library files outside the workspace exist only in the script's table; they were
  checked on compiled copies, not committed.
- 24 of the 81 reported files were judged by reading, not compiled: their closures miss 45 to 849 modules
  of the workspace.
- The clashes with the Stacks and FontaineWintenberger copies (survey 1.8) are outside the brief and were
  not touched; nothing was switched to weil-conjectures' theorems.
