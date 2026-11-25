# FAG import closures, assumption scan and focused compile

Evidence for [`../etale-premises-sheaf-libraries-audit.md`](../etale-premises-sheaf-libraries-audit.md),
Section 5.6 (item 5 for FAG). It was prepared on 17 November 2026, and every closure and
scan was regenerated on 18 November 2026 with a corrected import parser (see "Correction"
below). Later every line count was recomputed as a count of newline characters, and the
closures of nine further modules were added (last two sections before the compile). The first
closure and scan data served the study of Laumon's theorem; the five modules used there are
called the Laumon roots below, and their import closures the Laumon closures. This is a
development record. It is not a Library statement and does not make any FAG declaration part
of the Library.

## Source

formal-arithmetic-geometry/weil-conjectures at commit `a25955cde4f85f67bef3149a6efc3efe20c22132`,
registered literature `formal-arithmetic-geometry-weil-conjectures-a25955c`. The scan read a
depth-1 git checkout of that commit. Module names below are relative to the root namespace
`WeilConjectures` unless written in full. File paths are relative to the repository root.

## Method

The closures and scans were made by a Python script that reads source text only. It runs no
Lean and no repository code.

1. **Module files.** A module `A.B.C` belongs to the repository if `A/B/C.lean` exists at the
   repository root or under `Comparator/` (the source directory of the `Weil.*` and
   `LeanEvalWeil.*` libraries in `lakefile.toml`). Every other import is external (Mathlib and
   its dependencies).
2. **Comments and strings.** In each file, nested block comments, documentation comments, line
   comments and string literals are replaced by blanks, keeping line numbers.
3. **Imports.** The blanked header is read as a sequence of tokens separated by whitespace,
   following Lean's header grammar: an optional `module`, an optional `prelude`, then import
   commands `[public] [meta] import [all] M`. The first tokens that do not form an import
   command end the header. An import command may therefore be wrapped across lines, as in
   `public import` followed by the module name on the next line.
4. **Closure.** Breadth-first search from the root modules through repository imports.
   "Lines" is the total number of newline characters in the closure's files, the convention
   of the Stacks table in Section 7.1 of the audit note. "Mathlib modules
   imported directly" counts the distinct `Mathlib.*` modules that some closure file imports.
5. **Scan.** Every line of the blanked text is searched for: `sorry`, `sorryAx`, `admit`,
   `axiom`, `opaque`, `implemented_by`, `extern`, `unsafe`, `native_decide`, `decide +native`
   (and `native := true`), `skipKernelTC`, `ofReduceBool`/`reduceBool`, `addDecl`/`axiomDecl`/
   `mkAxiom`, `#eval`, `run_cmd`/`run_tac`/`run_elab`/`run_meta`, `initialize`,
   `maxHeartbeats 0`, `set_option debug.`, `set_option backward.`, and definitions of syntax,
   macros and elaborators. Each hit is recorded with file and line. The hits in the premise
   closure, and the `addDecl` and `initialize` hits of the larger closures, were read in the
   source.

A text scan cannot tell whether a root theorem depends on a `sorry` in its closure. Only
`#print axioms` after a build settles that. The repository's `lakefile.toml` sets
`warn.sorry = false`, so a build does not warn about them.

**Correction.** The first version of this report read the header line by line and ended it
at the first line that was not a complete import command. A wrapped `public import` (the
module name on the next line) ended the header, so that import and every later one in the
file were missed. A later check found this; for
example `SixFunctors/Etale/Derived/DirectImageVanishingTorsion.lean:11-12` and
`SixFunctors/Etale/SmoothBaseChange/HigherDirectImage/CohomPresheaf.lean:12-13` wrap their
imports. With the corrected parser the premise closure grew from 7,255 to 7,275 modules and the
union of the Laumon closures from 16,814 to 16,839. The 19 premise modules outside that
union are the same 19 modules, and the 17 `sorry` sites are the same 17 sites. The tables
below are from the corrected run; the earlier figures are given in brackets where they
changed. The focused compile at the end of this report used a fixed list of 467 modules,
which the corrected parser reproduces, so it is unaffected.

**Line counts.** In earlier versions of this report, the "Lines" column counted one more line per file
than the number of newline characters. A later check
found this: for example 103,409 was reported for the
467-module closure of `CohomologyLimit`, which has 102,942 newline characters. Every "Lines"
figure below is now a count of newline characters, so the FAG and Stacks tables use the same
convention. The module counts and the scans did not change.

## Closures

| Root | Repository modules | Lines | Mathlib modules imported directly | `sorry` sites |
|---|---|---|---|---|
| `SixFunctors.Etale.BaseChangeTheorems.SmoothProperLocallyConstant` | 7,258 [7,238] | 1,245,786 | 1,577 | 0 |
| `SixFunctors.Etale.BaseChangeTheorems.Proper` | 6,978 [6,958] | 1,191,229 | 1,565 | 0 |
| `SixFunctors.Etale.BaseChangeTheorems.Smooth` | 6,561 [6,544] | 1,122,976 | 1,550 | 0 |
| `SixFunctors.Etale.Derived.Finiteness.Proper` | 7,050 [7,030] | 1,204,390 | 1,569 | 0 |
| `AlgebraicGeometry.Sites.CohomologyLimit` | 467 | 102,942 | 603 | 0 |
| **union of these five (the premise closure)** | **7,275 [7,255]** | **1,252,455** | **1,578** | **0** |
| `TraceFormula.Specialization.NearbyFiniteness` (Laumon root) | 14,545 [14,525] | 3,074,777 | 1,887 | 11 |
| `SixFunctors.NearbyCycles.GaloisAction` (Laumon root) | 13,484 [13,464] | 2,867,634 | 1,849 | 11 |
| `FourierTransform.Inversion` (Laumon root) | 8,460 [8,440] | 1,505,236 | 1,664 | 1 |
| `WeilSheaf.FourierInversion` (Laumon root) | 16,818 [16,793] | 3,490,737 | 1,935 | 14 |
| `WeilSheaf.WeilFourierInversion` (Laumon root) | 13,533 [13,513] | 2,879,580 | 1,862 | 13 |
| union of the five Laumon roots | 16,839 [16,814] | 3,494,755 | 1,935 | 17 |
| `Statement` (the headline Weil conjectures) | 17,339 [17,314] | 3,610,380 | 1,991 | 14 |
| whole repository (roots `WeilConjectures` and `WeilConjectures.Statement`) | 26,796 | 5,482,914 | 2,186 | 209 |

Every closure except the `CohomologyLimit` closure contains one module of `Comparator/`,
`Weil.Definitions`; the other modules are under `WeilConjectures/`. The whole repository's
count did not change because its root module imports every module.

## Scan results

**Premise closure (7,275 modules).** No `sorry`, `sorryAx`, `admit`, axiom declaration,
`opaque`, `implemented_by`, `extern`, `unsafe`, `native_decide`, `decide +native`,
`skipKernelTC`, `ofReduceBool`, `addDecl`, `#eval`, `initialize`, `maxHeartbeats 0` or
`set_option debug.`. The other hits are:

- six `run_tac` blocks inside proofs:
  `WeilConjectures/AlgebraicGeometry/HigherDirectImageTransitionCoreComposition.lean:384`,
  `WeilConjectures/AlgebraicGeometry/HigherDirectImageRawTransitionToHomCore.lean:257` (found
  only by the corrected parser),
  `WeilConjectures/AlgebraicGeometry/HigherDirectImageOverMapCoefficient.lean:239`,
  `WeilConjectures/AlgebraicGeometry/EtaleSingletonTensorPureImage.lean:65`,
  `WeilConjectures/AlgebraicGeometry/RawModuleScalarCoefficientSquare.lean:154`,
  `WeilConjectures/AlgebraicGeometry/EtaleSingletonTensorNormalizationEvaluation.lean:56`;
- two `local macro_rules` that make the tactic `lia` try `le_refl`/`omega` or `decide` in one
  file each: `WeilConjectures/AlgebraicGeometry/EtaleComplexFirstPageContinuity.lean:28`,
  `WeilConjectures/AlgebraicGeometry/EtaleCEPrescribedNormalizedFirstPages.lean:127`;
- 4,469 lines `set_option backward.…` (elaboration options such as
  `backward.isDefEq.respectTransparency`, which change elaboration, not the kernel).

**Larger closures.** The Laumon closures, the headline closure and the whole repository also
contain `WeilConjectures/Tactic/FirstOrderApply.lean`. Its tactic adds theorem declarations with
`addDecl (.thmDecl …)` (line 470), which the kernel checks, and it keeps an `IO.Ref` declared
with `initialize` (line 45). The whole repository has a second `addDecl` hit outside these
closures, 171 `run_cmd`/`run_tac` hits and 61 syntax, macro or elaborator definitions. These were
not read one by one.

## `sorry` sites

Seventeen distinct sites occur in the union of the Laumon closures. The letters say which
roots' closures contain each site: N = `TraceFormula.Specialization.NearbyFiniteness`, G =
`SixFunctors.NearbyCycles.GaloisAction`, I = `FourierTransform.Inversion`, F =
`WeilSheaf.FourierInversion`, W = `WeilSheaf.WeilFourierInversion`.

| File and line | Closures |
|---|---|
| `WeilConjectures/AlgebraicGeometry/Completed/CompletedExtensionZeroComparison.lean:1771` | N G F W |
| `WeilConjectures/AlgebraicGeometry/Completed/CompletedExtensionZeroComparison.lean:1809` | N G F W |
| `WeilConjectures/AlgebraicGeometry/Finite/Coefficient/FiniteCoefficientExchangeTransport.lean:72` | N G F W |
| `WeilConjectures/AlgebraicGeometry/OrderedExchange/OrderedExchangeTowerExchange.lean:84` | N G F W |
| `WeilConjectures/AlgebraicGeometry/OrderedExchange/OrderedExchangeTowerExchange.lean:95` | N G F W |
| `WeilConjectures/AlgebraicGeometry/Pbc/PbcCoefficientTwists.lean:181` | N G F W |
| `WeilConjectures/CategoryTheory/AdicSites/Morphism/CompletionMateComparison.lean:875` | N G F W |
| `WeilConjectures/CategoryTheory/AdicSites/Morphism/CompletionMateComparison.lean:2547` | N G F W |
| `WeilConjectures/SixFunctors/CoefficientReduction.lean:860` | N G F W |
| `WeilConjectures/SixFunctors/Etale/Derived/IntegralVerdier.lean:449` | N G F W |
| `WeilConjectures/SixFunctors/Etale/Derived/RationalStage.lean:228` | N G F W |
| `WeilConjectures/EtaleCohomology/Purity/Smooth/AffineSpaceTrace.lean:56` | I |
| `WeilConjectures/WeilSheaf/AffineLineBundle.lean:131` | F |
| `WeilConjectures/WeilSheaf/SmoothPurity.lean:298` | F |
| `WeilConjectures/WeilSheaf/UpperShriekUnitTensorMap.lean:102` | F |
| `WeilConjectures/WeilSheaf/WeilFourierInversion.lean:70` | W |
| `WeilConjectures/WeilSheaf/WeilFourierInversion.lean:100` | W |

The 14 sites of the headline `Statement` closure are exactly the 14 sites of the
`WeilSheaf.FourierInversion` closure (the eleven N G F W sites and the three F sites). The
repository's README says that the main theorems do not use them, and that `#print axioms` at its
commit `91ebbc09a7` showed only the standard axioms. Neither claim was rechecked here. The 209
sites of the whole repository lie in 155 files: 113 under `WeilConjectures/AlgebraicGeometry`,
41 under `SixFunctors`, 13 under `CategoryTheory`, 11 under `SmoothPurity`, 8 under
`PoincareDuality`, 8 under `WeilSheaf`, 6 under `Algebra`, 4 under `DeligneLaumon`, 2 under
`EtaleCohomology`, and one each under `ProperBaseChange`, `RingTheory` and `Topology`.

## Premise modules outside the Laumon closures

All but 19 of the 7,275 premise modules lie in the union of the five Laumon closures. The 19
are the same with both parsers:

- `AlgebraicGeometry.Sites.CohomologyLimit` (Stacks tag 09YQ) and fifteen modules that it
  imports: `Algebra.Homology.ExtResolution`; `AlgebraicGeometry.Sites.EtaleHypercover`,
  `AlgebraicGeometry.Sites.HypercoverDescent`, `AlgebraicGeometry.Sites.UpperStarSectionsLimit`,
  `AlgebraicGeometry.Sites.UpperStarSectionsLimitModule`,
  `AlgebraicGeometry.Sites.UpperStarSectionsModule`;
  `AlgebraicTopology.SemiSimplicialObject.Basic`,
  `AlgebraicTopology.SemiSimplicialObject.Coskeleton`; `CategoryTheory.Sites.LocallyExact`;
  `CategoryTheory.Sites.SemiSimplicialHypercover.Basic`, `….Cohomology`, `….Cone`,
  `….FreeResolution`, `….Map`, `….Refinement`;
- `SixFunctors.Etale.BaseChangeTheorems.Smooth`,
  `SixFunctors.Etale.BaseChangeTheorems.SmoothProperLocallyConstant` and
  `SixFunctors.Etale.BaseChangeTheorems.SmoothProperSpecialization`.

## Modules cited for statements C.5–C.9

The corrected script was run on 18 November 2026 for the modules that the audit
cites for generic base change over a field (statements C.5), for Galois actions over a field
(C.6), for inertia (C.7) and for the stalk formula (C.9). The smooth-source theorem (C.8)
`Etale.smoothGenericDirectImage` lies in the `Deligne` module itself, so it adds no root. The
prime-field form from which it is derived, in `AlgebraicGeometry.SmoothGenericDirectImage`
(also C.8), has a closure of 8,210 modules, all inside the `Deligne` closure and inside the
Laumon closures.
Topological invariance (03SI, `SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`, also in
C.9) is already in the premise closure, through `AlgebraicGeometry.Sites.CohomologyLimit`.
"Outside P" counts the modules not in the premise closure above (7,275 modules). "Outside
P ∪ T" counts those not in the union of the premise closure and the five Laumon closures
(16,858 modules). The first nine rows were first computed with the line-by-line parser; the
earlier figures are given in brackets where they changed.

| Root | Repository modules | Lines | Mathlib modules imported directly | `sorry` sites | Outside P | Outside P ∪ T |
|---|---|---|---|---|---|---|
| `SixFunctors.Etale.Derived.Finiteness.Deligne` | 8,230 [8,210] | 1,453,610 | 1,652 | 0 | 979 | 0 |
| `AlgebraicGeometry.Sites.GaloisModule` | 81 | 13,746 | 185 | 0 | 0 | 0 |
| `AlgebraicGeometry.GeometricFrobenius` | 4 | 1,135 | 11 | 0 | 0 | 0 |
| `AlgebraicGeometry.FundamentalGroup.CurveDualTateModule` | 5,801 | 1,039,910 | 1,567 | 0 | 307 | 52 |
| `AlgebraicGeometry.FundamentalGroup.DecompositionGroup` | 68 | 14,774 | 159 | 0 | 0 | 0 |
| `AlgebraicGeometry.FiniteLocallyConstantEtale` | 113 | 26,237 | 243 | 0 | 0 | 0 |
| `RingTheory.InertiaIndEtale` | 37 | 9,857 | 110 | 0 | 6 | 6 |
| `ConstructibleSheaf.LowerStarSpecialization` | 310 | 69,880 | 485 | 0 | 2 | 2 |
| `EtaleCohomology.Purity.RealSheaves.BoundaryStalk` | 4,051 | 724,030 | 1,355 | 0 | 40 | 27 |
| `SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.StalkFormula` (03Q9) | 967 | 196,704 | 787 | 0 | 2 | 2 |
| `AlgebraicGeometry.Sites.StrictHenselizationField` | 5 | 1,268 | 20 | 0 | 0 | 0 |
| `AlgebraicGeometry.EtaleSheafDiscreteContinuousRep` | 97 | 16,188 | 204 | 0 | 4 | 4 |
| union of the first nine | 8,421 [8,401] | | | 0 | 1,168 | 62 |
| union of all twelve | 8,443 | | | 0 | 1,174 | 68 |
| union of the twelve and the five premise roots | 8,449 | 1,512,166 | 1,680 | 0 | 1,174 | 68 |

In these closures the scan finds no `sorry`, `sorryAx`, `admit`, axiom declaration,
`opaque`, `implemented_by`, `extern`, `unsafe`, `native_decide`, `decide +native`,
`skipKernelTC`, `ofReduceBool`, `addDecl`, `#eval`, `initialize`, `maxHeartbeats 0` or
`set_option debug.`. The `Deligne` closure has 33 `run_tac` hits inside proofs (the six of
the premise closure and 27 others) and the two `local macro_rules` for `lia` listed above. The
`CurveDualTateModule` closure has two of the premise closure's `run_tac` hits. The other hits
are `set_option backward.…` lines. The `run_tac` hits outside the premise closure were not read
one by one.

The two modules of the `StalkFormula` closure outside P ∪ T are
`CategoryTheory.DerivedCategory.ExtPlus` and the root itself. The four of
`EtaleSheafDiscreteContinuousRep` are the root, `AlgebraicGeometry.GaloisPointGeometricComparison`,
`RepresentationTheory.DiscreteContinuousRep` and
`RepresentationTheory.DiscreteModule.DiscreteContinuousRep`.
The six modules of `RingTheory.InertiaIndEtale`'s closure outside P ∪ T are
`RingTheory.GenericEtale`, `RingTheory.InertiaIndEtale`,
`RingTheory.InertiaStrictHenselization`, `RingTheory.InertiaUnramifiedPoint`,
`RingTheory.ProEtale.IndEtaleDirectedUnion` and `RingTheory.StrictlyHenselianInvariants`.
The 27 modules of `BoundaryStalk`'s closure outside P ∪ T are
`AlgebraicGeometry.Curve.BoundaryNeighbourhood`, `AlgebraicGeometry.CurveRegularCover`,
twelve modules `AlgebraicGeometry.FundamentalGroup.*` (`DenseOpen`, `DenseOpenNormal`,
`ExtendOverPoints`, `Extension`, `FrobeniusConjugacy`, `FrobeniusDecomposition`,
`HomotopyExactSequence`, `Inertia`, `InertiaNeighbourhood`, `RestrictionWeilGroup`,
`StalkTransport`, `WeilGroupDense`), four modules `ConstructibleSheaf.*` (`LowerStarOpenStalk`,
`LowerStarOpenStalkFinite`, `LowerStarSpecialization`, `OnePoint`), six modules
`EtaleCohomology.Purity.RealSheaves.*` (`Boundary`, `BoundaryConstruction`, `BoundaryInertia`,
`BoundaryStalk`, `Construction`, `Weights`), `Mathlib.RingTheory.Ideal.Pointwise`,
`RingTheory.InertiaUnramifiedPoint` and `SixFunctors.Etale.UpperLowerStar.UnitMono`. The two
of `LowerStarSpecialization` are `ConstructibleSheaf.LowerStarOpenStalk` and
`ConstructibleSheaf.LowerStarSpecialization`.

## Nine further cited modules

The same script was run for nine further modules that the audit cites:
the limit cones over finite subextensions and 09YQ for `Sheaf.H` (statements C.10, route (i)
of bridge F3), the factorization of a geometric point through its strict localization and its
use over a field (C.10), and the comparisons of cohomology groups and the cospecialization map
(C.11, bridges F1, F3 and F5). The composition rule `Etale.cohomologyPullbackFunctorial`
(C.10) and the module of the cospecialization map, `AlgebraicGeometry.Sites.Cospecialization`
(C.11), are already in the premise closure, so they add no root. "Outside P" and "Outside P ∪
T" are as in the previous section.

| Root | Repository modules | Lines | Mathlib modules imported directly | `sorry` sites | Outside P | Outside P ∪ T |
|---|---|---|---|---|---|---|
| `AlgebraicGeometry.IntermediateFieldLimit` | 1 | 280 | 4 | 0 | 1 | 0 |
| `SixFunctors.ProEtale.GaloisAcyclic.FieldExtension` | 1,190 | 230,162 | 886 | 0 | 88 | 0 |
| `WeilSheaf.CondensedModelFiniteLevelColimit` | 706 | 163,078 | 749 | 0 | 243 | 1 |
| `AlgebraicGeometry.Sites.CohomologyContinuity` | 947 | 187,882 | 791 | 0 | 0 | 0 |
| `SixFunctors.Etale.BaseChangeTheorems.CospecializationSections` | 468 | 102,340 | 619 | 0 | 0 | 0 |
| `AlgebraicGeometry.Sites.StrictHenselizationLocal` | 2 | 798 | 11 | 0 | 0 | 0 |
| `AlgebraicGeometry.Sites.FieldCohomologicalDimension` | 5,217 | 907,455 | 1,448 | 0 | 0 | 0 |
| `SixFunctors.Etale.ConstantCohomologyExt` | 7,083 | 1,209,309 | 1,572 | 0 | 71 | 1 |
| `SixFunctors.Etale.ForgetModuleCohomology` | 1,097 | 215,501 | 842 | 0 | 62 | 0 |
| union of the twelve roots of the previous section, the five premise roots and these nine | 8,550 | 1,539,264 | 1,691 | 0 | 1,275 | 70 |
| the same without `WeilSheaf.CondensedModelFiniteLevelColimit` | 8,466 | 1,515,233 | 1,682 | 0 | 1,191 | 69 |

The module outside P ∪ T in the `CondensedModelFiniteLevelColimit` closure is the root
itself, and so is the one in the `ConstantCohomologyExt` closure. `IntermediateFieldLimit`
lies in the Laumon closures but not in the premise closure. The scan finds in these closures
no `sorry`, `sorryAx`, `admit`, axiom declaration, `opaque`, `implemented_by`, `extern`,
`unsafe`, `native_decide`, `decide +native`, `skipKernelTC`, `ofReduceBool`, `addDecl`,
`#eval`, `initialize`, `maxHeartbeats 0` or `set_option debug.`. The `ConstantCohomologyExt`
closure has the six `run_tac` blocks and the two `lia` macros of the premise closure; the
other eight have no hits other than `set_option backward.…` lines. The union of all 26 roots has the 33
`run_tac` blocks and the two macros of the `Deligne` closure. A separate recount, with
other tools, of the nine module counts, the counts outside P ∪ T and both unions with their
lines found the same values.

## Two modules cited for bridge F5

The same script was run for the two modules that bridge F5 cites
(statements C.12): the universal property of the strict localization and the strict
henselianity of `B_Q`. The germ formulas cited with them are in `Cospecialization`,
`LowerStarSpecialization` and `BoundaryStalk`, which are already counted.

| Root | Repository modules | Lines | Mathlib modules imported directly | `sorry` sites | Outside P | Outside P ∪ T |
|---|---|---|---|---|---|---|
| `AlgebraicGeometry.Sites.StrictLocalizationUniversal` | 592 | 129,730 | 695 | 0 | 3 | 0 |
| `RingTheory.StrictlyHenselianNormal` | 7 | 1,611 | 29 | 0 | 0 | 0 |
| union of the 26 roots of the previous section and these two | 8,553 | 1,540,119 | 1,691 | 0 | 1,278 | 70 |

The three modules of the `StrictLocalizationUniversal` closure outside P are the root,
`AlgebraicGeometry.Sites.StrictLocalizationMap` and
`AlgebraicGeometry.FundamentalGroup.Representable`, all three in the Laumon closures. The
two closures have no hits other than `set_option backward.…` lines.

## Focused compile on the Library's Lean pin

**Input.** The 467 repository modules of the closure of
`WeilConjectures.AlgebraicGeometry.Sites.CohomologyLimit`, copied without change into a private
draft. All 467 files are byte-identical to the files at the pin. Their aggregate SHA-256 is
`3b91f83a18ee1c93aecfeda24a32e7798a05d657f4f0a3df7e75da0a6901552e`, the SHA-256 of the output
of `sha256sum` run on the 467 relative paths in byte order. The Lean service reported the tree
hash as beginning `40aa7a8f`.

**Environment.** Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. FAG itself is on Lean 4.35.0 and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

**Result.** The build fails. Lake built 190
modules and 70 failed with 346 errors. The remaining 207 were not built, so 346 is a lower bound
for the closure. By origin, the failed modules are 50
under `WeilConjectures/Mathlib` (200 errors), 10 under `WeilConjectures/FromJoel` (80 errors) and
10 others (66 errors).

Two Mathlib modules that the closure imports directly do not exist at `5ed2965`:
`Mathlib.CategoryTheory.Functor.Quadrifunctor` (reported for
`FromJoel.CategoryTheory.Functor.Quadrifunctor`), and
`Mathlib.Order.Int.ConditionallyCompleteOrder`, which is
`Mathlib/Data/Int/ConditionallyCompleteOrder.lean` at `5ed2965`. The second was found by the
import scan; the module that imports it was among those not built.

Errors by kind:

| Errors | Kind |
|---|---|
| 85 | unsolved goals |
| 57 | `rewrite` found no instance of the pattern |
| 37 | type mismatch reported by the elaborator |
| 37 | kernel errors (application type mismatch, declaration type mismatch, declaration has metavariables), 25 of them in `FromJoel` |
| 31 | failed to synthesize an instance |
| 24 | `aesop` failed after exhaustive search |
| 24 | a tactic could not fill a default field or parameter (`naturality`, `map_id`, `functor_unitIso_comp`, fields of `Functor.CoreMonoidal`) |
| 15 | a tactic made no progress |
| 13 | unknown constant, identifier or field (for example `AlgHom.toRingHom_injective`, `CategoryTheory.End.mul_asHom`, `CategoryTheory.Aut.of`, `AlgEquiv.coe_toRingEquiv`) |
| 1 | imported module does not exist |
| 22 | other (no goals left, stuck metavariables, `rcases` on a non-inductive type, failed `rfl`, termination) |

These are the errors of a newer Mathlib's API meeting an older one: renamed or removed lemmas,
changed definitions that make proofs by `rfl`, `simp`, `rw` and `aesop` fail, and kernel
errors, mostly in `FromJoel` files. No edit was attempted. At this count, bringing the
closure to the Library's pin is a port, which this report does not start.

Failed modules, with the number of errors and the first error (names without the prefix
`WeilConjectures.`):

| Module | Errors | First error |
|---|---|---|
| `Mathlib.Algebra.Category.AlgCat.FilteredColimits` | 1 | line 87: Tactic `rewrite` failed: Did not find an occurrence of the pattern |
| `Mathlib.Algebra.Category.Ring.Constructions` | 1 | line 69: Unknown constant `AlgEquiv.coe_toRingEquiv` |
| `Mathlib.Algebra.Category.Ring.FilteredColimits` | 5 | line 111: Tactic `rfl` failed: The left-hand side |
| `Mathlib.Algebra.Category.Ring.FinitePresentation` | 2 | line 157: No goals to be solved |
| `Mathlib.Algebra.Homology.HomotopyCategory` | 2 | line 57: Tactic `apply` failed: could not unify the conclusion of `@Category.id_comp` |
| `Mathlib.Algebra.Homology.HomotopyCategory.Shift` | 1 | line 82: unsolved goals |
| `Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence` | 5 | line 57: Tactic `rewrite` failed: Did not find an occurrence of the pattern |
| `Mathlib.Algebra.Homology.SingleHomology` | 4 | line 36: `simp` made no progress |
| `Mathlib.AlgebraicGeometry.AffineOpenAlgebra` | 1 | line 58: Tactic `rewrite` failed: Did not find an occurrence of the pattern |
| `Mathlib.AlgebraicGeometry.Fiber` | 2 | line 66: Tactic `rewrite` failed: Did not find an occurrence of the pattern |
| `Mathlib.AlgebraicGeometry.IdealSheaf.Affine` | 5 | line 53: Tactic `rewrite` failed: Did not find an occurrence of the pattern |
| `Mathlib.AlgebraicGeometry.IdealSheaf.Basic` | 1 | line 46: Application type mismatch: The argument |
| `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` | 9 | line 243: (kernel) declaration has metavariables 'AlgebraicGeometry.Scheme.Over.restrictAffineOpens' |
| `Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified` | 2 | line 87: unsolved goals |
| `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` | 2 | line 76: failed to synthesize instance of type class |
| `Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite` | 1 | line 91: Type mismatch: After simplification, term |
| `Mathlib.AlgebraicGeometry.Scheme` | 1 | line 106: unsolved goals |
| `Mathlib.CategoryTheory.Abelian.CommSq` | 3 | line 62: unsolved goals |
| `Mathlib.CategoryTheory.Abelian.Injective.Resolution` | 6 | line 87: failed to synthesize instance of type class |
| `Mathlib.CategoryTheory.Adjunction.Mates` | 7 | line 166: Tactic `rewrite` failed: Did not find an occurrence of the pattern |
| `Mathlib.CategoryTheory.Enriched.FunctorCategory` | 6 | line 37: (kernel) declaration has metavariables 'CategoryTheory.Enriched.FunctorCategory.precompEnr… |
| `Mathlib.CategoryTheory.Galois.IsFundamentalgroup` | 3 | line 38: Unknown constant `CategoryTheory.Aut.of` |
| `Mathlib.CategoryTheory.Limits.FilteredColimitCommutesProduct` | 7 | line 84: (kernel) declaration type mismatch, 'CategoryTheory.Functor.piCompIso_hom_app' has type |
| `Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic` | 4 | line 143: `simp` made no progress |
| `Mathlib.CategoryTheory.Monoidal.Closed.Basic` | 2 | line 159: Tactic `rewrite` failed: Did not find an occurrence of the pattern |
| `Mathlib.CategoryTheory.Monoidal.FunctorCategory` | 11 | line 35: (kernel) declaration has metavariables 'CategoryTheory.Functor.Monoidal.const' |
| `Mathlib.CategoryTheory.Monoidal.Preadditive` | 4 | line 37: unsolved goals |
| `Mathlib.CategoryTheory.Monoidal.Rigid.Basic` | 2 | line 401: Tactic `rewrite` failed: Did not find an occurrence of the pattern |
| `Mathlib.CategoryTheory.MorphismProperty.Comma` | 15 | line 42: Tactic `aesop` failed, failed to prove the goal after exhaustive search. |
| `Mathlib.CategoryTheory.MorphismProperty.CommaSites` | 2 | line 62: Tactic `rewrite` failed: Did not find an occurrence of the pattern |
| `Mathlib.CategoryTheory.MorphismProperty.Composition` | 1 | line 44: Unknown constant `CategoryTheory.End.mul_asHom` |
| `Mathlib.CategoryTheory.MorphismProperty.Ind` | 2 | line 97: unsolved goals |
| `Mathlib.CategoryTheory.MorphismProperty.Limits` | 4 | line 73: `simp` made no progress |
| `Mathlib.CategoryTheory.MorphismProperty.OverAdjunction` | 31 | line 72: Type mismatch: After simplification, term |
| `Mathlib.CategoryTheory.Sites.ConstantSheaf` | 3 | line 79: (kernel) declaration has metavariables 'CategoryTheory.Functor.sheafPushforwardContinuousC… |
| `Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence` | 5 | line 36: (kernel) declaration has metavariables 'CategoryTheory.Equivalence.sheafCongrFunctorCompSh… |
| `Mathlib.CategoryTheory.Sites.ConstantSheafOver` | 7 | line 70: unsolved goals |
| `Mathlib.CategoryTheory.Sites.Continuous` | 1 | line 140: Type mismatch |
| `Mathlib.CategoryTheory.Sites.Over` | 3 | line 44: Tactic `rewrite` failed: Did not find an occurrence of the pattern |
| `Mathlib.CategoryTheory.Sites.Plus` | 3 | line 66: unsolved goals |
| `Mathlib.CategoryTheory.Sites.Point.Basic` | 1 | line 60: Application type mismatch: The argument |
| `Mathlib.CategoryTheory.Sites.Point.Category` | 1 | line 70: unsolved goals |
| `Mathlib.CategoryTheory.Sites.Point.Skyscraper` | 1 | line 53: Tactic `rewrite` failed: Did not find an occurrence of the pattern |
| `Mathlib.CategoryTheory.Sites.Pullback` | 2 | line 61: Tactic `rewrite` failed: Did not find an occurrence of the pattern |
| `Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject` | 6 | line 249: unsolved goals |
| `Mathlib.RingTheory.Etale.GeometricPoint` | 2 | line 262: Unknown constant `AlgHom.toRingHom_injective` |
| `Mathlib.RingTheory.Etale.StandardEtale` | 4 | line 225: unsolved goals |
| `Mathlib.RingTheory.Filtration` | 1 | line 381: Application type mismatch: The argument |
| `Mathlib.RingTheory.Flat.DescentAlgebra` | 1 | line 170: Tactic `rewrite` failed: Did not find an occurrence of the pattern |
| `Mathlib.RingTheory.Spectrum.Prime.Noetherian` | 4 | line 95: Tactic `rcases` failed: `x✝ : ?m.190` is not an inductive datatype |
| `FromJoel.Algebra.Homology.BifunctorSingle` | 2 | line 50: unsolved goals |
| `FromJoel.Algebra.Homology.DerivedCategory.DerivabilityStructureKInjectives` | 5 | line 159: failed to synthesize instance of type class |
| `FromJoel.Algebra.Homology.Embedding.HomEquiv` | 3 | line 116: unsolved goals |
| `FromJoel.Algebra.Homology.Embedding.StupidTrunc` | 7 | line 51: unsolved goals |
| `FromJoel.Algebra.Homology.HomologicalComplexFunctorEquiv` | 8 | line 55: (kernel) application type mismatch |
| `FromJoel.CategoryTheory.Functor.Derived.LeftDerived` | 24 | line 73: (kernel) application type mismatch |
| `FromJoel.CategoryTheory.Functor.Quadrifunctor` | 1 | line 6: module Mathlib.CategoryTheory.Functor.Quadrifunctor does not exist |
| `FromJoel.CategoryTheory.GuitartExact.Basic` | 22 | line 72: Application type mismatch: The argument |
| `FromJoel.CategoryTheory.Monoidal.Functor` | 4 | line 114: unsolved goals |
| `FromJoel.CategoryTheory.QuotientThree` | 4 | line 162: `simp` made no progress |
| `Algebra.Homology.ExtResolution` | 14 | line 125: unsolved goals |
| `Algebra.Homology.ResolutionByClass` | 1 | line 248: unsolved goals |
| `AlgebraicGeometry.Morphisms.UniversalHomeomorphism` | 4 | line 83: failed to synthesize instance of type class |
| `AlgebraicGeometry.Sites.EtaleTopologicalInvariance.Coprod` | 4 | line 42: `simp` made no progress |
| `AlgebraicGeometry.Sites.EtaleTopologicalInvariance.Cover` | 1 | line 97: failed to synthesize instance of type class |
| `AlgebraicGeometry.Sites.EtaleTopologicalInvariance.GlobalSections` | 2 | line 32: unsolved goals |
| `AlgebraicTopology.SemiSimplicialObject.Coskeleton` | 23 | line 125: Tactic `rewrite` failed: Did not find an occurrence of the pattern |
| `CategoryTheory.Sites.SemiSimplicialHypercover.FreeResolution` | 13 | line 146: Tactic `rewrite` failed: Did not find an occurrence of the pattern |
| `CategoryTheory.Sites.SemiSimplicialHypercover.Map` | 3 | line 42: failed to synthesize instance of type class |
| `RingTheory.ProEtale.WeaklyEtale` | 1 | line 155: unsolved goals |
