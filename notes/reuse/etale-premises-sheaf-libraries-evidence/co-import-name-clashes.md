# Shared declaration names of the Stacks and FAG closures

Evidence for [`../etale-premises-sheaf-libraries-audit.md`](../etale-premises-sheaf-libraries-audit.md),
Section 8 (Task 7360, item 6). Worker 19 prepared this list on 17 November 2026 and regenerated it on 18 November 2026 from
the corrected closures (see "How the list was made", step 1). It is an unreviewed development
record, not a Library statement.

## What is listed

The table lists the public declaration names declared both

- in the import closure of the seven Stacks premise roots of Section 7.1 at commit `c496df0`
  (AxiomMath/Stacks; 17,881 modules: 17,435 `StacksFrontier`, 446 `StacksCore`), and
- in the import closure of the five FAG premise roots of Section 5.6 together with the five
  Task 7342 roots at commit `a25955c` (formal-arithmetic-geometry/weil-conjectures; 16,858
  modules: the 16,839 of the Task 7342 closure and the 19 premise modules outside it).

**Counts.** 332 names. Of these, 286 are declared in the closure of the five FAG premise roots
(7,275 modules), and the other 46 only in the closure of the Task 7342 roots. On the FAG side,
137 names are declared in `WeilConjectures/Mathlib`, 15 in `WeilConjectures/FromJoel`, and 180
in other FAG files. On the Stacks side, 28 are in `StacksCore` and 304 in `StacksFrontier`.

**Correction.** The first version of this list had 327 names. Its closures came from a parser
that read the module headers line by line and stopped at the first `public import` whose module
name was on the next line, so it missed every import after such a wrapped command. With the
corrected parser the Stacks closure grew from 16,918 to 17,881 modules and the FAG union from
16,833 to 16,858. All 327 earlier rows are reproduced unchanged. Five names are new:
`AlgebraicGeometry.irreducibleSpace_of_connectedSpace` (in the FAG premise closure), and
`CategoryTheory.Limits.isColimitCofanMkOfIso`, `CategoryTheory.ObjectProperty.localizingClosure`,
`…ObjectProperty.le_localizingClosure` and `…ObjectProperty.localizingClosure_le` (in the Task
7342 closure only).

## How the list was made

The names were read from the source text, not from compiled environments, by a Python script:

1. The import closures were computed from the import commands of the module headers
   (`import`, `public import`, `meta import`, `import all`), read as a token sequence after
   comments were blanked, so that a command whose module name is on the next line is read,
   inside each repository (for FAG, `WeilConjectures/*` and the `Comparator/*` source
   directory of the `Weil.*` libraries).
2. In every module of a closure, comments and string literals were blanked. Declaration headers
   (`def`, `theorem`, `lemma`, `abbrev`, `instance` with a name, `structure`, `class`,
   `inductive`, `opaque`, `axiom`) were read with their modifiers. `namespace … end` blocks and
   `_root_.` were followed to form the full name. `private` declarations were skipped. Unnamed
   instances were skipped. An earlier pass had misread two unnamed instances with nested
   parentheses in their binders as the names `AlgebraicGeometry.))` and `AlgebraicGeometry.ᵒᵖ)`.
   The parser now discards such fragments, and the counts above are from the corrected pass.
3. The two sets of full names were intersected.
4. A second pass checked, for every listed declaration and on both sides, that it is public
   under Lean's module system: both repositories use the module system throughout, and each
   listed declaration lies in a `public section` (for example `@[expose] public section`) or
   carries the `public` modifier. All 332 are public on both sides. None is a module-private
   name that Lean would mangle.

Names that Lean generates (names of unnamed instances, structure projections, equation lemmas,
auxiliary definitions) were not produced. Two closures can clash in those too, so 332 is a
lower bound for what an import of both closures meets.

Eight entries were checked by hand against the source files. In all eight, both repositories
declare the name:
`AdicCompletion.isNoetherianRing`, `AlgebraicGeometry.HasCompactification` (a class in FAG
`WeilConjectures/Compactification/Defs.lean`, a def in Stacks
`StacksFrontier/AlgebraicGeometry/NagataCompactification/HasCompactification.lean`),
`AlgebraicGeometry.relativeFrobenius`, `AlgebraicGeometry.Scheme.Modules.injective_stalkLinearMap_of_mono`,
`CategoryTheory.Adjunction.isIso_homEquiv_symm_iff`, `CategoryTheory.IsPullback.of_comp_mono`,
`HomogeneousLocalization.val_fromZeroRingHom` and `IsRegularLocalRing.isDomain`. Several
entries name different mathematical objects on the two sides (for example the two
`relativeFrobenius`, which take different arguments). A renaming fork must therefore rename,
not merge.

## Which shared names Lean rejects

Lean does not reject every name that two imported modules both declare. When it merges the
imports of a module, Lean 4.34 (`Environment.finalizeImport`, with the check `subsumesInfo` in
the toolchain file `src/lean/Lean/Environment.lean`, line 2268) accepts two declarations of the
same name if both are theorems with the same elaborated type, the same list of universe
parameter names, and the same `all` field. Otherwise the import fails with "already
imported". An instance of a class whose values are propositions (such as `Module.Flat` or
`Functor.Additive`) is a theorem for this check. The rule was confirmed in the project's Lean
service on test modules (Worker 19's diagnostics, 17 November 2026):

| Diagnostic | Two imported modules declare the same name as | Result |
|---|---|---|
| `33a977fe` | two theorems with the same statement | accepted |
| `9e5650a8` | two theorems with different statements | rejected |
| `43197044` | two definitions `Nat := 1` and `Nat := 2` | rejected |
| `65c7211e` | two instances of the same proposition-valued class | accepted |
| `19b14067` | a theorem and an instance of a proposition-valued class, same statement | accepted |

For two definitions the check returns `false` whatever their values, so the value in the
third test does not matter. The same rule explains a feature of Stacks: 35 names are declared
twice inside the closure of its seven premise roots, and all 35 are theorems, lemmas or
instances of proposition-valued classes, none a definition. For example `AlgebraicGeometry.Scheme.ord_one` is a theorem
both in `StacksFrontier/AlgebraicGeometry/Chow/ProperPushforwardPrincipal/Basic.lean` and in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Curves/OrderOfVanishingSupport.lean`, and
both modules lie in the closure of the 0GLH root.

The 332 shared names fall into three groups. The last column of the table gives the first
group.

- **113 names, 99 of them in the FAG premise closure: rejected whatever the statements.** On
  at least one side the declaration is a `def`, `abbrev`, `class` or `structure`, or an
  instance of a class that carries data. One instance is of the last kind:
  `AlgebraicGeometry.ProjectiveSpace.over`, an instance of `Scheme.CanonicallyOver`, whose
  field `hom` is a morphism.
- **187 names, 161 in the FAG premise closure:** a `theorem` or `lemma` on both sides.
- **32 names, 26 in the FAG premise closure:** an instance on at least one side and a theorem
  or instance on the other. Each of these instances is of a proposition-valued class (for
  example `IsNoetherianRing`, `Module.Flat`, `PreservesLimitsOfShape`, `HasFiniteBiproducts`).

Lean accepts a name of the last two groups (219 names) only if the two elaborated statements
and universe parameter names agree exactly. That was not checked: it needs both libraries
elaborated in one environment. Both repositories pin the same upstream toolchain, Lean
`v4.35.0` with Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` (each `lean-toolchain` and
`lake-manifest.json`), so a Lake project at that pin could require both. The project's Lean
service, the only one this audit used, runs the Library's pin instead (Lean 4.34.0, Mathlib
`5ed2965`). There only focused samples were checked: a 318-module Stacks sample built after
30 edited files, and an unedited 467-module FAG sample failed (Sections 5.6 and 7.2 of the
note). Neither library was built at its own pin. Some of the 219 differ visibly in the source. For example the two
`CategoryTheory.Functor.preservesLimitsOfShape_sheafPushforwardContinuous` bind the index
category with explicit universes `w₁ w₂` in FAG and with `Type*` in Stacks. A module that
imports both closures therefore meets at least 113 certain clashes, and up to 332.

## Reading the table

The fourth column says whether the FAG declaration lies in the closure of the five FAG premise
roots. The fifth column says "yes, always" for the first group above and "only if the two
statements differ" for the other two. Where a name is declared in several modules of one
closure, all of them are listed. The duplicates are declarations in mutually non-importing
modules of the same repository.

## The list

| Name | FAG module (kind) | Stacks module (kind) | In FAG premise closure | Rejected by Lean |
|---|---|---|---|---|
| `AddCommGrpCat.monoidalCategory` | `WeilConjectures.CategoryTheory.RingObjects.Ab` (instance) | `StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleTensor` (def) | yes | yes, always |
| `AdicCompletion.isNoetherianRing` | `WeilConjectures.RingTheory.AdicCompletionNoetherian` (theorem) | `StacksFrontier.RingTheory.AdicCompletion.NoetherianRing.PowerSeriesSurjection` (instance) | yes | only if the two statements differ |
| `Algebra.IsCentral.baseChange` | `WeilConjectures.Mathlib.Algebra.Central.TensorProduct` (instance) | `StacksCore.Algebra.Central.TensorProduct` (instance) | yes | only if the two statements differ |
| `Algebra.IsGeometricallyRegular` | `WeilConjectures.RingTheory.GRing` (def) | `StacksFrontier.RingTheory.GeometricallyRegular.Defs` (class) | yes | yes, always |
| `Algebra.IsRelativeGlobalCompleteIntersection` | `WeilConjectures.AlgebraicGeometry.RelativeGlobalCompleteIntersection` (def) | `StacksFrontier.RingTheory.CompleteIntersection.Defs` (class) | yes | yes, always |
| `Algebra.IsSeparableExtension` | `WeilConjectures.FieldTheory.SeparableExtension` (def) | `StacksFrontier.FieldTheory.Separable.Defs` (class) | yes | yes, always |
| `Algebra.WeaklyEtale.of_isLocalization` | `WeilConjectures.Mathlib.RingTheory.Etale.Weakly` (theorem) | `StacksFrontier.AlgebraicGeometry.ProEtale.Site.GeometricPointStalk` (theorem) | yes | only if the two statements differ |
| `Algebra.isRegularRing_of_smooth` | `WeilConjectures.RingTheory.RegularRingSmoothAscent` (theorem) | `StacksFrontier.RingTheory.Smooth.RegularRing` (theorem) | yes | only if the two statements differ |
| `Algebra.isRegularRing_tensorProduct_of_isGeometricallyRegular` | `WeilConjectures.RingTheory.GeometricallyRegularFieldExtension` (theorem) | `StacksFrontier.RingTheory.GeometricallyRegular.FieldExtension` (theorem) | yes | only if the two statements differ |
| `Algebra.isSeparableExtension_of_perfectField` | `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Limits.PerfectSeparable` (theorem) | `StacksFrontier.FieldTheory.Separable.PerfectField` (lemma) | yes | only if the two statements differ |
| `AlgebraicGeometry.AffineSpace.isClosedImmersion_homOfVector` | `WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace` (lemma) | `StacksFrontier.AlgebraicGeometry.PseudoCoherent.ClosedImmersion` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.ChowModification` | `WeilConjectures.AlgebraicGeometry.ChowLemma` (def) | `StacksFrontier.AlgebraicGeometry.Limits.ChowLemmaNoetherian0200` (structure) | yes | yes, always |
| `AlgebraicGeometry.FormallySmooth` | `WeilConjectures.AlgebraicGeometry.FormallySmooth` (def) | `StacksFrontier.AlgebraicGeometry.Morphisms.FormallySmooth.Defs` (abbrev) | yes | yes, always |
| `AlgebraicGeometry.HasCompactification` | `WeilConjectures.Compactification.Defs` (class) | `StacksFrontier.AlgebraicGeometry.NagataCompactification.HasCompactification` (def) | yes | yes, always |
| `AlgebraicGeometry.HasCompactification.of_eq` | `WeilConjectures.Compactification.Defs` (lemma) | `StacksFrontier.AlgebraicGeometry.NagataCompactification.HasCompactification` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.HasCompactification.of_isClosedImmersion` | `WeilConjectures.Compactification.Constructions` (theorem) | `StacksFrontier.AlgebraicGeometry.NagataCompactification.HasCompactification` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.HasCompactification.of_isPullback` | `WeilConjectures.Compactification.BaseChange` (theorem) | `StacksFrontier.AlgebraicGeometry.NagataCompactification.HasCompactification` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.HasCompactification.of_isQuasiAffine` | `WeilConjectures.Compactification.Affine` (theorem) | `StacksFrontier.AlgebraicGeometry.NagataCompactification.HasCompactification` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.IsAbelianVariety` | `WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs` (class) | `StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVariety` (class) | yes | yes, always |
| `AlgebraicGeometry.IsCurve` | `WeilConjectures.AlgebraicGeometry.Curve` (class) | `StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs` (class) | yes | yes, always |
| `AlgebraicGeometry.IsProjective` | `WeilConjectures.AlgebraicGeometry.Morphisms.Projective` (class) | `StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Basic` (def) | yes | yes, always |
| `AlgebraicGeometry.IsQuasiAffineHom` | `WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine` (class) | `StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffine` (class) | yes | yes, always |
| `AlgebraicGeometry.IsQuasiProjective` | `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.QuasiProjective` (def) | `StacksFrontier.AlgebraicGeometry.QuasiProjective.Basic` (abbrev) | yes | yes, always |
| `AlgebraicGeometry.IsRegular` | `WeilConjectures.AlgebraicGeometry.Regular` (class) | `StacksFrontier.AlgebraicGeometry.Properties.Regular` (abbrev) | yes | yes, always |
| `AlgebraicGeometry.IsVariety` | `WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective` (class) | `StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic` (class) | yes | yes, always |
| `AlgebraicGeometry.LocallyQuasiFinite.of_etale` | `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite` (instance) | `StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Fiber` (instance) | yes | only if the two statements differ |
| `AlgebraicGeometry.Proj.comp_fromOfGlobalSections` | `WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic` (lemma) | `StacksFrontier.AlgebraicGeometry.ProjectiveSpaceSections.FromGlobalSections` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.Proj.iSup_basicOpen_homogeneous_eq_top` | `WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor` (lemma) | `StacksFrontier.AlgebraicGeometry.RelativeProj.FlatOverBase` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.Proj.isClosedImmersion_map` | `WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor` (theorem) | `StacksFrontier.AlgebraicGeometry.ProjClosedImmersion.Basic` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.Proj.map_congr` | `WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor` (lemma) | `StacksFrontier.AlgebraicGeometry.Blowup.RelativeProj` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.Proj.map_irrelevant_comp_appTop_eq_top` | `WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic` (lemma) | `StacksFrontier.AlgebraicGeometry.ProjectiveSpaceSections.FromGlobalSections` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.Proj.map_toSpecZero` | `WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor` (lemma) | `StacksFrontier.AlgebraicGeometry.Blowup.RelativeProj` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.Proj.toBasicOpenOfGlobalSections_comp_basicOpenIsoSpec_hom` | `WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic` (lemma) | `StacksFrontier.AlgebraicGeometry.ProjectiveSpaceSections.GradedNaturality` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.ProjectiveSpace` | `WeilConjectures.AlgebraicGeometry.ProjectiveSpace` (def) | `StacksFrontier.AlgebraicGeometry.Limits.ProjectiveSpace` (def) | yes | yes, always |
| `AlgebraicGeometry.ProjectiveSpace.isAffineOpen_standardOpen` | `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts` (lemma) | `StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCharts` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.ProjectiveSpace.over` | `WeilConjectures.AlgebraicGeometry.ProjectiveSpace` (instance) | `StacksFrontier.AlgebraicGeometry.Limits.ProjectiveSpace` (instance) | yes | yes, always |
| `AlgebraicGeometry.ProjectiveSpace.standardOpen` | `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfSections` (def) | `StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCharts` (def) | yes | yes, always |
| `AlgebraicGeometry.RingedSpace.moduleStalkFunctor` | `WeilConjectures.Algebra.Homology.ModuleStalkFunctor` (def) | `StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.CohomologyFiniteFreeLocus` (abbrev) | yes | yes, always |
| `AlgebraicGeometry.Scheme.Hom.appLE_congr_hom` | `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski` (lemma) | `StacksFrontier.AlgebraicGeometry.Pushout.FlatSectionsDescent` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.Scheme.Hom.appLE_top_top` | `WeilConjectures.Mathlib.AlgebraicGeometry.Scheme` (lemma) | `StacksFrontier.AlgebraicGeometry.EulerCharIso.SchemeIso` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.Scheme.Hom.apply_eq_of_comp_eq` | `WeilConjectures.AlgebraicGeometry.Curve.GenericModelSpread` (lemma) | `StacksFrontier.AlgebraicGeometry.Morphisms.HenselianLocalFinitePiece` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.Scheme.Hom.apply_fiberι` | `WeilConjectures.AlgebraicGeometry.ProEtale.Coherent.Etale` (lemma) | `StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Basic` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.Scheme.Hom.bijective_residueFieldMap` | `WeilConjectures.ConstructibleSheaf.FinitePushforward.PointSplitting` (lemma) | `StacksFrontier.AlgebraicGeometry.F6Rank128.FiberResidueField` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.Scheme.Hom.fiberMap` | `WeilConjectures.Mathlib.AlgebraicGeometry.Fiber` (def) | `StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.SourceMap` (def) | yes | yes, always |
| `AlgebraicGeometry.Scheme.Hom.imageMap` | `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant` (def) | `StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Basic` (def) | yes | yes, always |
| `AlgebraicGeometry.Scheme.Hom.imageMap_comp` | `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant` (lemma) | `StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Basic` (lemma) | yes | only if the two statements differ |
| `AlgebraicGeometry.Scheme.Hom.imageMap_id` | `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant` (lemma) | `StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Basic` (lemma) | yes | only if the two statements differ |
| `AlgebraicGeometry.Scheme.Hom.imageMap_imageι` | `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant` (lemma) | `StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Basic` (lemma) | yes | only if the two statements differ |
| `AlgebraicGeometry.Scheme.Hom.isFiniteLocallyFree_relativeDifferentials` | `WeilConjectures.AlgebraicGeometry.SmoothRelativeDifferentialsFiniteLocallyFree` (theorem) | `StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.DifferentialsLocallyFree` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.Scheme.Hom.ker_comp_of_isSchemeTheoreticallyDominant` | `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant` (lemma) | `StacksFrontier.AlgebraicGeometry.Existence.Descent` (lemma) | yes | only if the two statements differ |
| `AlgebraicGeometry.Scheme.Hom.ker_toImage` | `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme` (lemma) | `StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeSystem` (lemma) | yes | only if the two statements differ |
| `AlgebraicGeometry.Scheme.Hom.range_imageι` | `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme` (lemma) | `StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.ImmersionClosure` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.Scheme.Hom.relativeDifferentials` | `WeilConjectures.AlgebraicGeometry.Modules.Differentials` (def) | `StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Relative` (def) | yes | yes, always |
| `AlgebraicGeometry.Scheme.Hom.toImage_imageMap` | `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant` (lemma) | `StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Basic` (lemma) | yes | only if the two statements differ |
| `AlgebraicGeometry.Scheme.IdealSheafData.colon` | `WeilConjectures.AlgebraicGeometry.Hilbert.Curve` (def) | `StacksFrontier.AlgebraicGeometry.Divisors.IdealSheafColon` (def) | yes | yes, always |
| `AlgebraicGeometry.Scheme.IdealSheafData.comap_map_of_isClosedImmersion` | `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial` (lemma) | `StacksFrontier.AlgebraicGeometry.ClosedImmersion.IdealSheafComapMap` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.Scheme.IdealSheafData.comap_mul_of_isOpenImmersion` | `WeilConjectures.Blowup.FiniteDegree.Algebra` (lemma) | `StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.IdealSheafComap` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.Scheme.IdealSheafData.comap_pow_of_isOpenImmersion` | `WeilConjectures.Blowup.FiniteDegree.Algebra` (lemma) | `StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.IdealSheafComap` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.Scheme.IdealSheafData.ideal_colon` | `WeilConjectures.AlgebraicGeometry.Hilbert.Curve` (lemma) | `StacksFrontier.AlgebraicGeometry.Divisors.IdealSheafColon` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.Scheme.IdealSheafData.ideal_eq_top_of_disjoint_support` | `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Basic` (lemma) | `StacksFrontier.AlgebraicGeometry.IdealPowerHomColimit.Restriction` (lemma) | yes | only if the two statements differ |
| `AlgebraicGeometry.Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure` | `WeilConjectures.AlgebraicGeometry.Modules.HilbertPolynomial` (instance) | `StacksFrontier.AlgebraicGeometry.CoherentPushforwardCriteria.ClosureSubscheme` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.Scheme.IdealSheafData.isPullback_comap` | `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial` (lemma) | `StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniSmooth` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal` | `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme` (instance) | `StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme` (instance) | yes | only if the two statements differ |
| `AlgebraicGeometry.Scheme.IdealSheafData.locallyOfFinitePresentation_subschemeι` | `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation` (lemma) | `StacksFrontier.AlgebraicGeometry.Flatness.IsomorphismFunctorRepresentability` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.Scheme.IsQuasiAffine.of_forall_exists_isQuasiAffine_basicOpen` | `WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine` (lemma) | `StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineStability` (lemma) | yes | only if the two statements differ |
| `AlgebraicGeometry.Scheme.IsQuasiAffine.of_isQuasiAffineHom` | `WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine` (lemma) | `StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineStability` (lemma) | yes | only if the two statements differ |
| `AlgebraicGeometry.Scheme.Modules.Hom.app_presheaf_map` | `WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator` (lemma) | `StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison` (lemma) | yes | only if the two statements differ |
| `AlgebraicGeometry.Scheme.Modules.IsAmple` | `WeilConjectures.AlgebraicGeometry.Ample` (def) | `StacksFrontier.AlgebraicGeometry.Ample.Defs` (def) | yes | yes, always |
| `AlgebraicGeometry.Scheme.Modules.exteriorPower` | `WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower` (def) | `StacksFrontier.AlgebraicGeometry.DeRham.Complex.DifferentialForms` (abbrev) | no | yes, always |
| `AlgebraicGeometry.Scheme.Modules.germ_smul` | `WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk` (lemma) | `StacksFrontier.AlgebraicGeometry.Chow.MeromorphicOrder.Stalk` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.Scheme.Modules.injective_stalkLinearMap_of_mono` | `WeilConjectures.AlgebraicGeometry.Cohomology.FlatBaseChangeSheaf` (lemma) | `StacksFrontier.AlgebraicGeometry.Modules.StalkMono` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.Scheme.Modules.isIso_of_isIso_pullback_map` | `WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk` (theorem) | `StacksFrontier.AlgebraicGeometry.Modules.AffineSections` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.Scheme.Modules.isIso_presheaf_map_of_eq` | `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Restrict` (lemma) | `StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.UnitQuasicoherent` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.Scheme.Modules.isIso_restrictFunctor_map_of_le` | `WeilConjectures.AlgebraicGeometry.Modules.VanishingOnOpen` (lemma) | `StacksFrontier.AlgebraicGeometry.SupportedQuotient.Basic` (lemma) | yes | only if the two statements differ |
| `AlgebraicGeometry.Scheme.Modules.isIso_restrictFunctor_map_pullback_map` | `WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator` (lemma) | `StacksFrontier.AlgebraicGeometry.SupportedQuotient.Basic` (lemma) | yes | only if the two statements differ |
| `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_biprod` | `WeilConjectures.AlgebraicGeometry.Cohomology.QuasicoherentExtension` (lemma) | `StacksFrontier.AlgebraicGeometry.QuasiCoherent.Extend.GraphKernel` (instance) | yes | only if the two statements differ |
| `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_cokernel` | `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel` (theorem) | `StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.Affine` (instance) | yes | only if the two statements differ |
| `AlgebraicGeometry.Scheme.Modules.pullbackSection` | `WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator` (def) | `StacksFrontier.AlgebraicGeometry.PullbackSections.Affine` (def) | yes | yes, always |
| `AlgebraicGeometry.Scheme.Modules.stalkFunctor` | `WeilConjectures.AlgebraicGeometry.Modules.StalkExact` (def) | `StacksFrontier.AlgebraicGeometry.Modules.StalkSupport` (abbrev) | yes | yes, always |
| `AlgebraicGeometry.Scheme.Modules.tensorObj` | `WeilConjectures.AlgebraicGeometry.Modules.Invertible` (abbrev) | `StacksFrontier.AlgebraicGeometry.Modules.TensorStalkGenerators` (abbrev) | yes | yes, always |
| `AlgebraicGeometry.Scheme.ProEt.topology_eq_restrictedTopology` | `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale` (lemma) | `StacksFrontier.AlgebraicGeometry.Spaces.ProetaleComparison` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.Scheme.bot_not_mem_smallEtaleTopology` | `WeilConjectures.ConstructibleSheaf.KernelCokernel` (lemma) | `StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantModuleSheafIrreducibleSectionsRing` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.Scheme.connectedComponentOpens` | `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.BettiCardinalities` (def) | `StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ConnectedComponents` (def) | yes | yes, always |
| `AlgebraicGeometry.Scheme.iSup_connectedComponentOpens` | `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.BettiCardinalities` (lemma) | `StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ConnectedComponents` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.Scheme.isClosed_connectedComponentOpens` | `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.BettiCardinalities` (lemma) | `StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ConnectedComponents` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.Scheme.isUnit_map_of_le_basicOpen` | `WeilConjectures.Mathlib.AlgebraicGeometry.Restrict` (lemma) | `StacksFrontier.AlgebraicGeometry.Morphisms.Affine.Fiber` (lemma) | yes | only if the two statements differ |
| `AlgebraicGeometry.Scheme.isUnit_of_basicOpen_eq_top` | `WeilConjectures.Mathlib.AlgebraicGeometry.Scheme` (lemma) | `StacksFrontier.AlgebraicGeometry.Spaces.FittingIdealGeometricStalk` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.Scheme.mem_connectedComponentOpens` | `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.BettiCardinalities` (lemma) | `StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ConnectedComponents` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.Scheme.normalization` | `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization` (abbrev) | `StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Scheme` (abbrev) | yes | yes, always |
| `AlgebraicGeometry.Scheme.ord_one` | `WeilConjectures.AlgebraicGeometry.Curve.Divisor` (lemma) | `StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.Basic` (theorem); `StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.OrderOfVanishingSupport` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.Scheme.presheaf_map_map_apply` | `WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator` (lemma) | `StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsAlgebra` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.Scheme.subcanonical_smallEtaleTopology` | `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale` (instance) | `StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleInverseImageRepresentable` (instance) | yes | only if the two statements differ |
| `AlgebraicGeometry.affineLine` | `WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace` (abbrev) | `StacksFrontier.AlgebraicGeometry.RationalFunctions.Basic` (abbrev) | yes | yes, always |
| `AlgebraicGeometry.baseChangeCone` | `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit` (def) | `StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.BaseChange` (abbrev) | yes | yes, always |
| `AlgebraicGeometry.baseChangeDiagram` | `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit` (def) | `StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.BaseChange` (abbrev) | yes | yes, always |
| `AlgebraicGeometry.baseChangeDiagram_map_fst` | `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit` (lemma) | `StacksFrontier.AlgebraicGeometry.FibreDimensionLimit.Basic` (lemma) | yes | only if the two statements differ |
| `AlgebraicGeometry.baseChangeDiagram_map_snd` | `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit` (lemma) | `StacksFrontier.AlgebraicGeometry.FibreDimensionLimit.Basic` (lemma) | yes | only if the two statements differ |
| `AlgebraicGeometry.baseChangeMap` | `WeilConjectures.AlgebraicGeometry.PicardFunctor` (abbrev) | `StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.BaseChange` (def) | yes | yes, always |
| `AlgebraicGeometry.baseChangeMap_comp` | `WeilConjectures.AlgebraicGeometry.PicardFunctor` (lemma) | `StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.BaseChange` (lemma) | yes | only if the two statements differ |
| `AlgebraicGeometry.baseChangeMap_fst` | `WeilConjectures.AlgebraicGeometry.Picard.TwistedDescent` (lemma) | `StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.BaseChange` (lemma) | yes | only if the two statements differ |
| `AlgebraicGeometry.baseChangeMap_snd` | `WeilConjectures.AlgebraicGeometry.Picard.TwistedDescent` (lemma) | `StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.BaseChange` (lemma) | yes | only if the two statements differ |
| `AlgebraicGeometry.connectedSpace_spec_of_isLocalRing` | `WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLineStrictlyLocalSections` (lemma) | `StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategory.InertiaDiagram` (theorem) | no | only if the two statements differ |
| `AlgebraicGeometry.etale_left` | `WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.TwistedSheaf` (lemma) | `StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.GaloisTrivializationExists` (instance) | no | only if the two statements differ |
| `AlgebraicGeometry.etale_specMap_algebraMap` | `WeilConjectures.AlgebraicGeometry.GaloisFieldCover` (instance) | `StacksFrontier.AlgebraicGeometry.Spaces.FieldPointGaloisDescent` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.exists_affineOpens_le_preimage` | `WeilConjectures.Blowup.BlowupUniversal` (lemma) | `StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafDataFromCartesian` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.exists_etale_isPullback_of_isLimit` | `WeilConjectures.AlgebraicGeometry.Sites.EtaleLimitDescent` (theorem) | `StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.EtaleCover` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.exists_isProper_baseChange_of_isLimit` | `WeilConjectures.AlgebraicGeometry.EventuallyProper` (theorem) | `StacksFrontier.AlgebraicGeometry.ChowFiniteType.ModuleSupport` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.exists_specializes_of_mem_closure_range` | `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` (theorem) | `StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.InvariantOpenBetween` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.flat_specMap_algebraMap` | `WeilConjectures.AlgebraicGeometry.Picard.Jacobian` (lemma) | `StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Basic` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.irreducibleSpace_of_connectedSpace` | `WeilConjectures.AlgebraicGeometry.GroupScheme.Basic` (theorem) | `StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.Irreducible` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.isIntegralHom_of_iSup_eq_top` | `WeilConjectures.AlgebraicGeometry.Morphisms.Finite.Limit` (lemma) | `StacksFrontier.AlgebraicGeometry.EventualFiniteness.Basic` (lemma) | yes | only if the two statements differ |
| `AlgebraicGeometry.isIso_morphismRestrict_of_le` | `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant` (theorem) | `StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GraphConstruction` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.isIso_morphismRestrict_of_le_opensRange` | `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale` (lemma) | `StacksFrontier.AlgebraicGeometry.Crystalline.SheafComparison` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType` | `WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian` (theorem) | `StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Basic` (lemma) | yes | only if the two statements differ |
| `AlgebraicGeometry.isProper_descendsAlong_surjective_inf_flat_inf_quasiCompact` | `WeilConjectures.AlgebraicGeometry.FieldExtensionDescent` (instance) | `StacksFrontier.AlgebraicGeometry.Descent.ProperFpqcLocalAtTarget` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.isProper_imageι_comp` | `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper` (theorem) | `StacksFrontier.AlgebraicGeometry.Morphisms.Proper.SchemeTheoreticImage` (lemma) | yes | only if the two statements differ |
| `AlgebraicGeometry.isPullback_baseChangeMap` | `WeilConjectures.AlgebraicGeometry.PicardFunctor` (lemma) | `StacksFrontier.AlgebraicGeometry.Flatness.FlatteningInjectiveBaseChange` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.isPullback_lift_of_isPullback` | `WeilConjectures.AlgebraicGeometry.Sites.HypercoverDescent` (lemma) | `StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.EtaleObject` (lemma) | yes | only if the two statements differ |
| `AlgebraicGeometry.isPushout_appTop_of_flat` | `WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.GlobalSections` (theorem) | `StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineFlatBaseChange` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.isQuasicoherent_of_iso` | `WeilConjectures.AlgebraicGeometry.Modules.DescentEffective` (lemma) | `StacksFrontier.AlgebraicGeometry.Duality.DerivedAmplitude.UpperBounds` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.isReduced_of_etale` | `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale` (theorem) | `StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.isReduced_of_flat_of_surjective` | `WeilConjectures.AlgebraicGeometry.FieldExtensionDescent` (lemma) | `StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.Reduced` (lemma) | yes | only if the two statements differ |
| `AlgebraicGeometry.isReduced_of_smooth` | `WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced` (theorem) | `StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.isSchemeTheoreticallyDominant_iff_isIso_imageι` | `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant` (theorem) | `StacksFrontier.AlgebraicGeometry.Morphisms.Closure.SchemeTheoreticallyDense` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.isSeparated_descendsAlong_surjective_inf_flat_inf_quasiCompact` | `WeilConjectures.AlgebraicGeometry.FieldExtensionDescent` (instance) | `StacksFrontier.AlgebraicGeometry.Descent.ProperFpqcLocalAtTarget` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.isSeparated_of_surjective_universallyClosed` | `WeilConjectures.AlgebraicGeometry.IsSeparatedOfSurjectiveUniversallyClosed` (theorem) | `StacksFrontier.AlgebraicGeometry.Morphisms.Proper.SeparatedDescent` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.isSheaf_presheafHom` | `WeilConjectures.AlgebraicGeometry.Modules.FpqcSections` (lemma) | `StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.Basic` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.locallyOfFinitePresentation_diagonal` | `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation` (instance) | `StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Diagonal` (lemma) | yes | only if the two statements differ |
| `AlgebraicGeometry.locallyOfFinitePresentation_of_comp` | `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation` (theorem) | `StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Basic` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.picardDegree` | `WeilConjectures.AlgebraicGeometry.Picard.Degree` (def) | `StacksFrontier.AlgebraicGeometry.Picard.CurveDegree` (def) | yes | yes, always |
| `AlgebraicGeometry.range_morphismRestrict` | `WeilConjectures.AlgebraicGeometry.GenericFiber.RadicialSmoothing` (lemma) | `StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemCovering` (lemma) | yes | only if the two statements differ |
| `AlgebraicGeometry.range_snd_of_isPullback` | `WeilConjectures.Mathlib.AlgebraicGeometry.OpenImmersion` (theorem) | `StacksFrontier.AlgebraicGeometry.Descent.OpenImmersionEtaleDescent` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.relativeFrobenius` | `WeilConjectures.AlgebraicGeometry.RelativeFrobenius` (def) | `StacksFrontier.AlgebraicGeometry.Variety.Frobenius.Twist` (def) | no | yes, always |
| `AlgebraicGeometry.relativeFrobenius_fst` | `WeilConjectures.AlgebraicGeometry.RelativeFrobenius` (lemma) | `StacksFrontier.AlgebraicGeometry.Variety.Frobenius.Twist` (theorem) | no | only if the two statements differ |
| `AlgebraicGeometry.relativeFrobenius_snd` | `WeilConjectures.AlgebraicGeometry.RelativeFrobenius` (lemma) | `StacksFrontier.AlgebraicGeometry.Variety.Frobenius.Twist` (theorem) | no | only if the two statements differ |
| `AlgebraicGeometry.ringKrullDim_stalk_le_topologicalKrullDim` | `WeilConjectures.Mathlib.AlgebraicGeometry.Properties` (theorem) | `StacksFrontier.AlgebraicGeometry.Curves.NodeStalkCharacterization` (theorem) | yes | only if the two statements differ |
| `AlgebraicGeometry.specIsoOfAlgEquiv` | `WeilConjectures.AlgebraicGeometry.AffinePresentation` (def) | `StacksFrontier.AlgebraicGeometry.FundamentalGroup.NormalLocalExactSequence` (def) | no | yes, always |
| `AlgebraicGeometry.specIsoOfAlgEquiv_hom_comp` | `WeilConjectures.AlgebraicGeometry.AffinePresentation` (lemma) | `StacksFrontier.AlgebraicGeometry.FundamentalGroup.NormalLocalExactSequence` (theorem) | no | only if the two statements differ |
| `AlgebraicGeometry.topologicalKrullDim_eq_of_smoothOfRelativeDimension` | `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth` (theorem) | `StacksFrontier.AlgebraicGeometry.Variety.Curve.SmoothRelativeDimension` (theorem) | yes | only if the two statements differ |
| `CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_hom_app_comp` | `WeilConjectures.WeilSheaf.FieldCoefficientTateTwist` (lemma) | `StacksFrontier.CategoryTheory.Adjunction.Mates` (theorem) | no | only if the two statements differ |
| `CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_inv_app_comp` | `WeilConjectures.SixFunctors.ProEtale.FiniteLocallyConstantCokernel.ConstantPullback` (lemma) | `StacksFrontier.CategoryTheory.Adjunction.LeftAdjointUniqTranspose` (theorem) | no | only if the two statements differ |
| `CategoryTheory.Adjunction.isIso_homEquiv_symm_iff` | `WeilConjectures.CategoryTheory.Sites.PullbackLocallyBijective` (lemma) | `StacksFrontier.CategoryTheory.Adjunction.LeftAdjointUniqTranspose` (theorem) | no | only if the two statements differ |
| `CategoryTheory.Adjunction.mapHomologicalComplex` | `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction` (def) | `StacksFrontier.Algebra.Homology.DerivedCategory.KInjective.AdjointAndProducts` (def) | yes | yes, always |
| `CategoryTheory.Adjunction.mapHomotopyCategory` | `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction` (def) | `StacksFrontier.Algebra.Homology.HomotopyCategory.Adjunction` (def) | yes | yes, always |
| `CategoryTheory.Adjunction.mapHomotopyCategoryPlus` | `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction` (def) | `StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorBoundedBelow` (def) | yes | yes, always |
| `CategoryTheory.CommSq.shortComplexIsoShortComplex'` | `WeilConjectures.Mathlib.CategoryTheory.Abelian.CommSq` (def) | `StacksCore.CategoryTheory.Abelian.CommSq` (def) | yes | yes, always |
| `CategoryTheory.ExactCouple` | `WeilConjectures.Algebra.Homology.ExactCouple.Basic` (structure) | `StacksCore.Algebra.Homology.ExactCouple` (structure) | yes | yes, always |
| `CategoryTheory.ExactCouple.d` | `WeilConjectures.Algebra.Homology.ExactCouple.Basic` (def) | `StacksCore.Algebra.Homology.ExactCouple` (def) | yes | yes, always |
| `CategoryTheory.ExactCouple.dComplex` | `WeilConjectures.Algebra.Homology.ExactCouple.Basic` (def) | `StacksCore.Algebra.Homology.ExactCouple` (abbrev) | yes | yes, always |
| `CategoryTheory.ExactCouple.derived` | `WeilConjectures.Algebra.Homology.ExactCouple.Basic` (def) | `StacksCore.Algebra.Homology.ExactCouple` (abbrev) | yes | yes, always |
| `CategoryTheory.ExactCouple.derivedIter` | `WeilConjectures.Algebra.Homology.ExactCouple.Basic` (def) | `StacksCore.Algebra.Homology.ExactCouple.SpectralSequence` (abbrev) | yes | yes, always |
| `CategoryTheory.ExactCouple.derivedIter_succ` | `WeilConjectures.Algebra.Homology.ExactCouple.Basic` (lemma) | `StacksCore.Algebra.Homology.ExactCouple.SpectralSequence` (lemma) | yes | only if the two statements differ |
| `CategoryTheory.ExactCouple.derivedIter_zero` | `WeilConjectures.Algebra.Homology.ExactCouple.Basic` (lemma) | `StacksCore.Algebra.Homology.ExactCouple.SpectralSequence` (lemma) | yes | only if the two statements differ |
| `CategoryTheory.ExactCouple.f'` | `WeilConjectures.Algebra.Homology.ExactCouple.Basic` (def) | `StacksCore.Algebra.Homology.ExactCouple` (def) | yes | yes, always |
| `CategoryTheory.ExactCouple.f'_α'` | `WeilConjectures.Algebra.Homology.ExactCouple.Basic` (lemma) | `StacksCore.Algebra.Homology.ExactCouple` (lemma) | yes | only if the two statements differ |
| `CategoryTheory.ExactCouple.g'` | `WeilConjectures.Algebra.Homology.ExactCouple.Basic` (def) | `StacksCore.Algebra.Homology.ExactCouple` (def) | yes | yes, always |
| `CategoryTheory.ExactCouple.g'_f'` | `WeilConjectures.Algebra.Homology.ExactCouple.Basic` (lemma) | `StacksCore.Algebra.Homology.ExactCouple` (lemma) | yes | only if the two statements differ |
| `CategoryTheory.ExactCouple.spectralSequence` | `WeilConjectures.Algebra.Homology.ExactCouple.Basic` (def) | `StacksCore.Algebra.Homology.ExactCouple.SpectralSequence` (abbrev) | yes | yes, always |
| `CategoryTheory.ExactCouple.α'` | `WeilConjectures.Algebra.Homology.ExactCouple.Basic` (def) | `StacksCore.Algebra.Homology.ExactCouple` (def) | yes | yes, always |
| `CategoryTheory.ExactCouple.α'_g'` | `WeilConjectures.Algebra.Homology.ExactCouple.Basic` (lemma) | `StacksCore.Algebra.Homology.ExactCouple` (lemma) | yes | only if the two statements differ |
| `CategoryTheory.Functor.CommShift₂.postcompInt` | `WeilConjectures.Mathlib.CategoryTheory.Shift.CommShiftTwo` (def) | `StacksFrontier.CategoryTheory.Shift.CommShiftTwoPostcomp` (instance) | yes | yes, always |
| `CategoryTheory.Functor.LaxMonoidal.transport` | `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor` (def) | `StacksFrontier.CategoryTheory.Monoidal.ConjugateMonoidal` (def) | yes | yes, always |
| `CategoryTheory.Functor.LaxMonoidal.transport_ε` | `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor` (lemma) | `StacksFrontier.CategoryTheory.Monoidal.ConjugateMonoidal` (lemma) | yes | only if the two statements differ |
| `CategoryTheory.Functor.LaxMonoidal.transport_μ` | `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor` (lemma) | `StacksFrontier.CategoryTheory.Monoidal.ConjugateMonoidal` (lemma) | yes | only if the two statements differ |
| `CategoryTheory.Functor.bijective_map_of_iso` | `WeilConjectures.CategoryTheory.Monoidal.Closed.DualFullyFaithful` (lemma) | `StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorFullyFaithful` (theorem) | no | only if the two statements differ |
| `CategoryTheory.Functor.flip_additive` | `WeilConjectures.CategoryTheory.Monoidal.KFlatBifunctorTransport` (theorem) | `StacksFrontier.CategoryTheory.Functor.Bifunctor` (instance) | no | only if the two statements differ |
| `CategoryTheory.Functor.flip_obj_additive` | `WeilConjectures.CategoryTheory.Monoidal.KFlatBifunctorTransport` (theorem) | `StacksFrontier.CategoryTheory.Functor.Bifunctor` (instance) | no | only if the two statements differ |
| `CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic` | `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology` (theorem) | `StacksFrontier.Algebra.Homology.DerivedCategory.CompositionOfRightDerivedFunctors` (theorem) | yes | only if the two statements differ |
| `CategoryTheory.Functor.isRightDerivedFunctor_rightDerivedFunctorPlus_comp` | `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp` (instance) | `StacksFrontier.Algebra.Homology.DerivedCategory.CompositionComparisonIso` (instance) | yes | only if the two statements differ |
| `CategoryTheory.Functor.isTriangulated_rightDerivedFunctorPlus` | `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus` (instance) | `StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective.Leray` (lemma) | yes | only if the two statements differ |
| `CategoryTheory.Functor.isZero_homologyFunctor_mapDerivedCategory_obj` | `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` (lemma) | `StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegree` (theorem) | yes | only if the two statements differ |
| `CategoryTheory.Functor.iterate` | `WeilConjectures.Mathlib.CategoryTheory.Functor.Basic` (def) | `StacksFrontier.AlgebraicTopology.StandardResolution.Godement` (def) | yes | yes, always |
| `CategoryTheory.Functor.iterate_add` | `WeilConjectures.Mathlib.CategoryTheory.Functor.Basic` (lemma) | `StacksFrontier.AlgebraicTopology.StandardResolution.Godement` (theorem) | yes | only if the two statements differ |
| `CategoryTheory.Functor.mapDerivedCategoryCompIsoOfIso` | `WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelDerived` (def) | `StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryCompQh` (def) | no | yes, always |
| `CategoryTheory.Functor.mapDerivedCategoryCompIso_hom_app_Q` | `WeilConjectures.CategoryTheory.DerivedCategory.FreeComparisonMapDerivedCategory` (lemma) | `StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryCompIsoOnHomotopyCategory` (theorem) | no | only if the two statements differ |
| `CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso` | `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` (def) | `StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegree` (def) | yes | yes, always |
| `CategoryTheory.Functor.mapDerivedCategoryPlus` | `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` (def) | `StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorBoundedBelow` (def) | yes | yes, always |
| `CategoryTheory.Functor.mapDerivedCategoryPlusFactorsh` | `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` (def) | `StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorBoundedBelow` (def) | yes | yes, always |
| `CategoryTheory.Functor.mapDerivedCategoryPlusIdIso` | `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` (def) | `StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ThickeningInvariance` (def) | yes | yes, always |
| `CategoryTheory.Functor.mapHomologicalComplexCompHomologyFunctorIso` | `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Cech` (def) | `StacksFrontier.RingTheory.Dualizing.DerivedHomBaseChange.Conservative` (def) | yes | yes, always |
| `CategoryTheory.Functor.mapHomologicalComplexHomologyIso` | `WeilConjectures.FromJoel.Algebra.Homology.PreservesQuasiIso` (def) | `StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose` (def) | yes | yes, always |
| `CategoryTheory.Functor.mapHomologicalComplexHomologyIso_hom_app_eq` | `WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryHomologyNatIso` (lemma) | `StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomologyCompare` (theorem) | no | only if the two statements differ |
| `CategoryTheory.Functor.mapHomotopyCategoryCompIso_hom_app_quotient` | `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.GaloisActionUnitTransportInputs` (lemma) | `StacksFrontier.Algebra.Homology.HomotopyCategory.MapCompIsoCommShift` (theorem) | no | only if the two statements differ |
| `CategoryTheory.Functor.mapHomotopyCategoryFactors_hom_app_eq_id` | `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence` (lemma) | `StacksFrontier.Algebra.Homology.HomotopyCategory.MapCompIsoCommShift` (theorem) | no | only if the two statements differ |
| `CategoryTheory.Functor.mapHomotopyCategoryIdIso` | `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory` (def) | `StacksFrontier.Algebra.Homology.HomotopyCategory.AdjunctionComparison` (def) | yes | yes, always |
| `CategoryTheory.Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app` | `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Plus` (lemma) | `StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalarsDerived` (theorem) | yes | only if the two statements differ |
| `CategoryTheory.Functor.mapHomotopyCategoryPlusCompIso_refl_inv_app` | `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Plus` (lemma) | `StacksFrontier.Algebra.Homology.DerivedCategory.CompositionComparisonAssoc` (lemma) | yes | only if the two statements differ |
| `CategoryTheory.Functor.mapHomotopyCategoryPlusIdIso` | `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Plus` (def) | `StacksFrontier.Algebra.Homology.DerivedCategory.ExactIdentityComparison` (def) | yes | yes, always |
| `CategoryTheory.Functor.modObjObj` | `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod` (def) | `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforward` (abbrev) | no | yes, always |
| `CategoryTheory.Functor.preservesFiniteLimits_sheafPushforwardContinuous` | `WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous` (instance) | `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Relocalization` (instance) | yes | only if the two statements differ |
| `CategoryTheory.Functor.preservesLimitsOfShape_sheafPushforwardContinuous` | `WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous` (instance) | `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Relocalization` (instance) | yes | only if the two statements differ |
| `CategoryTheory.Functor.reflectsIsomorphisms_mapDerivedCategory` | `WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryReflectsIsomorphisms` (instance) | `StacksFrontier.RingTheory.Dualizing.DerivedHomBaseChange.Conservative` (instance) | no | only if the two statements differ |
| `CategoryTheory.Functor.rightAcyclic` | `WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic` (def) | `StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicObjects` (def) | yes | yes, always |
| `CategoryTheory.Functor.rightAcyclic_of_injective` | `WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic` (lemma) | `StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution` (lemma) | yes | only if the two statements differ |
| `CategoryTheory.Functor.rightDerivedFunctorPlusCompIso` | `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp` (def) | `StacksFrontier.Algebra.Homology.DerivedCategory.CompositionComparisonIso` (def) | yes | yes, always |
| `CategoryTheory.Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic` | `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology` (def) | `StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusComparisons` (def) | yes | yes, always |
| `CategoryTheory.Functor.rightDerivedFunctorPlusCompIso_assoc` | `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp` (lemma) | `StacksFrontier.Algebra.Homology.DerivedCategory.CompositionComparisonAssoc` (theorem) | yes | only if the two statements differ |
| `CategoryTheory.Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus` | `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact` (def) | `StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow` (def) | yes | yes, always |
| `CategoryTheory.Functor.rightDerivedFunctorPlusNatIso` | `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp` (def) | `StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusComparisons` (def) | yes | yes, always |
| `CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous_unit_app_hom` | `WeilConjectures.CategoryTheory.Sites.PullbackLocallyBijective` (lemma) | `StacksFrontier.CategoryTheory.Sites.PullbackComparisonInjectivity` (theorem) | no | only if the two statements differ |
| `CategoryTheory.Functor.sheafPullbackIso` | `WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback` (def) | `StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePullbackFunctoriality` (def) | yes | yes, always |
| `CategoryTheory.GradedObject.add_apply` | `WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns` (theorem) | `StacksCore.CategoryTheory.GradedObject.Abelian` (lemma) | yes | only if the two statements differ |
| `CategoryTheory.GradedObject.neg_apply` | `WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns` (theorem) | `StacksCore.CategoryTheory.GradedObject.Abelian` (lemma) | yes | only if the two statements differ |
| `CategoryTheory.GrothendieckTopology.IsWeaklyContractible` | `WeilConjectures.CategoryTheory.Sites.WeaklyContractible` (def) | `StacksFrontier.CategoryTheory.Sites.WeaklyContractible` (def) | no | yes, always |
| `CategoryTheory.GrothendieckTopology.Point.sheafFiberIso` | `WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Category` (def) | `StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.OpenClosedSequence` (def) | yes | yes, always |
| `CategoryTheory.GrothendieckTopology.Point.ulift` | `WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Basic` (def) | `StacksFrontier.CategoryTheory.Sites.Point.UniverseChange` (def) | yes | yes, always |
| `CategoryTheory.GrothendieckTopology.Point.uliftPresheafFiberIso` | `WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Basic` (def) | `StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleFlatTopos` (def) | yes | yes, always |
| `CategoryTheory.GrothendieckTopology.preservesLimitsOfShape_overPullback` | `WeilConjectures.SixFunctors.ProEtale.Adic.TowerIsoLifting` (instance) | `StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.WeakSerreSets.OverPullbackLimits` (instance) | no | only if the two statements differ |
| `CategoryTheory.InjectiveResolution.isoRightDerivedObjOfQuasiIso` | `WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic` (def) | `StacksFrontier.Algebra.Homology.Resolution.NatIntBridge` (def) | yes | yes, always |
| `CategoryTheory.IsCompactObject` | `WeilConjectures.CategoryTheory.CompactObject` (def) | `StacksFrontier.CategoryTheory.Triangulated.CompactObjects.ThickSubcategory` (class) | no | yes, always |
| `CategoryTheory.IsPullback.comp_mono_iff` | `WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic` (lemma) | `StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalk.PullbackMono` (theorem) | yes | only if the two statements differ |
| `CategoryTheory.IsPullback.of_comp_mono` | `WeilConjectures.AlgebraicGeometry.FibreDimension` (lemma) | `StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalk.PullbackMono` (theorem) | yes | only if the two statements differ |
| `CategoryTheory.Limits.biproductFinSuccIso` | `WeilConjectures.CategoryTheory.Preadditive.FinitePowerCokernel` (def) | `StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentBiproduct` (def) | no | yes, always |
| `CategoryTheory.Limits.isColimitCofanMkOfIso` | `WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedRightAdjointCategory` (def) | `StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCoarsening` (def) | no | yes, always |
| `CategoryTheory.Limits.isColimitCokernelCoforkOfIso` | `WeilConjectures.SixFunctors.ProEtale.Adic.ZModPowGLLift` (def) | `StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.TensorQuasicoherent` (def) | no | yes, always |
| `CategoryTheory.Limits.sigmaComparison_comp` | `WeilConjectures.Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products` (lemma) | `StacksFrontier.CategoryTheory.Triangulated.CoproductComparison` (theorem) | yes | only if the two statements differ |
| `CategoryTheory.Monoidal.functorCategoryMonoidalPreadditive` | `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive` (instance) | `StacksFrontier.CategoryTheory.Monoidal.FunctorCategoryTensorColimits` (instance) | yes | only if the two statements differ |
| `CategoryTheory.MonoidalClosed.curry_add` | `WeilConjectures.CategoryTheory.Monoidal.Closed.Preadditive` (lemma) | `StacksFrontier.Algebra.Homology.InternalHomComplex` (lemma) | yes | only if the two statements differ |
| `CategoryTheory.MonoidalClosed.curry_units_smul` | `WeilConjectures.CategoryTheory.Monoidal.Closed.Preadditive` (lemma) | `StacksFrontier.Algebra.Homology.InternalHomComplex` (lemma) | yes | only if the two statements differ |
| `CategoryTheory.MonoidalClosed.preIso` | `WeilConjectures.CategoryTheory.Monoidal.Closed.DualFullyFaithful` (def) | `StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.TensorHomAdjunction` (def) | no | yes, always |
| `CategoryTheory.MonoidalClosed.uncurry_add` | `WeilConjectures.CategoryTheory.Monoidal.Closed.Preadditive` (lemma) | `StacksFrontier.Algebra.Homology.InternalHomComplex` (lemma) | yes | only if the two statements differ |
| `CategoryTheory.MonoidalClosed.uncurry_units_smul` | `WeilConjectures.CategoryTheory.Monoidal.Closed.Preadditive` (lemma) | `StacksFrontier.Algebra.Homology.InternalHomComplex` (lemma) | yes | only if the two statements differ |
| `CategoryTheory.NatIso.rightDerived` | `WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived` (def) | `StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralHigherDirectImageComposition` (def) | yes | yes, always |
| `CategoryTheory.NatTrans.isIso_app_of_isColimit_cofan` | `WeilConjectures.CategoryTheory.DerivedCategory.Telescope` (lemma) | `StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EilenbergWatts` (lemma) | yes | only if the two statements differ |
| `CategoryTheory.NatTrans.isIso_app_of_isColimit_mapCocone` | `WeilConjectures.CategoryTheory.Abelian.HomologyFilteredColimit` (lemma) | `StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaCokernel` (lemma) | no | only if the two statements differ |
| `CategoryTheory.NatTrans.isIso_app_of_iso` | `WeilConjectures.Mathlib.CategoryTheory.NatIso` (lemma) | `StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaCokernel` (lemma) | yes | only if the two statements differ |
| `CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.ulift` | `WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Conservative` (lemma) | `StacksFrontier.CategoryTheory.Sites.Point.UniverseChange` (theorem) | yes | only if the two statements differ |
| `CategoryTheory.ObjectProperty.le_localizingClosure` | `WeilConjectures.CategoryTheory.Triangulated.LocalizingClosure` (lemma) | `StacksFrontier.CategoryTheory.Triangulated.LocalizingClosure` (lemma) | no | only if the two statements differ |
| `CategoryTheory.ObjectProperty.localizingClosure` | `WeilConjectures.CategoryTheory.Triangulated.LocalizingClosure` (def) | `StacksFrontier.CategoryTheory.Triangulated.LocalizingClosure` (inductive) | no | yes, always |
| `CategoryTheory.ObjectProperty.localizingClosure_le` | `WeilConjectures.CategoryTheory.Triangulated.LocalizingClosure` (lemma) | `StacksFrontier.CategoryTheory.Triangulated.LocalizingClosure` (lemma) | no | only if the two statements differ |
| `CategoryTheory.Presheaf.isSheaf_of_isSheaf_forget_commRingCat` | `WeilConjectures.AlgebraicGeometry.Sites.EtaleStructureSheaf` (lemma) | `StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicQuasicoherent` (theorem) | yes | only if the two statements differ |
| `CategoryTheory.Presieve.IsSeparatedFor.of_le` | `WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine` (lemma) | `StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineSheafCondition` (theorem) | yes | only if the two statements differ |
| `CategoryTheory.Presieve.map_comp` | `WeilConjectures.Mathlib.CategoryTheory.Sites.Sieves` (lemma) | `StacksFrontier.CategoryTheory.Sites.MorphismOfSites` (theorem) | yes | only if the two statements differ |
| `CategoryTheory.Pretriangulated.coproductTriangle` | `WeilConjectures.Mathlib.CategoryTheory.Triangulated.CoproductTriangle` (def) | `StacksFrontier.CategoryTheory.Triangulated.CoproductComparison` (def) | no | yes, always |
| `CategoryTheory.Pretriangulated.coproductTriangle_distinguished` | `WeilConjectures.Mathlib.CategoryTheory.Triangulated.CoproductTriangle` (lemma) | `StacksFrontier.CategoryTheory.Triangulated.CoproductComparison` (theorem) | no | only if the two statements differ |
| `CategoryTheory.Sheaf.additive_sheafSections_obj` | `WeilConjectures.CategoryTheory.Sites.SectionsWithSupport` (instance) | `StacksFrontier.Algebra.Homology.DerivedCategory.SheafSectionsRightDerived` (instance) | no | only if the two statements differ |
| `CategoryTheory.Sheaf.injective_obj` | `WeilConjectures.CategoryTheory.Sites.CechSheaf` (lemma) | `StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.InjectiveSheafVanishing` (theorem) | yes | only if the two statements differ |
| `CategoryTheory.Sheaf.monoidalPreadditive` | `WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal` (instance) | `StacksFrontier.CategoryTheory.Sites.MonoidalPreadditive` (theorem) | yes | only if the two statements differ |
| `CategoryTheory.Sheaf.presheafToSheafCompTensorLeftIso` | `WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal` (def) | `StacksFrontier.CategoryTheory.Sites.MonoidalColimits` (def) | yes | yes, always |
| `CategoryTheory.Sheaf.presheafToSheafCompTensorRightIso` | `WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal` (def) | `StacksFrontier.CategoryTheory.Sites.MonoidalColimits` (def) | yes | yes, always |
| `CategoryTheory.Sheaf.tensorLeftIso` | `WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal` (def) | `StacksFrontier.CategoryTheory.Sites.MonoidalPreadditive` (def) | yes | yes, always |
| `CategoryTheory.Sheaf.tensorRightIso` | `WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal` (def) | `StacksFrontier.CategoryTheory.Sites.MonoidalPreadditive` (def) | yes | yes, always |
| `CategoryTheory.ShortComplex.exact_map_iff_epi_map_kernel_lift` | `WeilConjectures.CategoryTheory.Sites.WeaklyContractible` (lemma) | `StacksCore.Algebra.Homology.ShortComplex.Exact` (lemma) | no | only if the two statements differ |
| `CategoryTheory.ShortComplex.homologyπ_comp_mapHomologyIso_hom` | `WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.PreservesHomology` (lemma) | `StacksFrontier.Algebra.Homology.ShortComplex.MapHomologyPi` (lemma) | no | only if the two statements differ |
| `CategoryTheory.ShortComplex.mapHomologyIso_comp_hom` | `WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.PreservesHomology` (lemma) | `StacksFrontier.Algebra.Homology.ShortComplex.MapHomologyComp` (theorem) | no | only if the two statements differ |
| `CategoryTheory.SpectralSequence.AbutsTo` | `WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic` (def) | `StacksFrontier.Algebra.Homology.SpectralSequence.AbutsTo` (def) | yes | yes, always |
| `CategoryTheory.SpectralSequence.AbutsTo.of_iso` | `WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic` (lemma) | `StacksFrontier.Algebra.Homology.SpectralSequence.AbutsToTransport` (theorem) | yes | only if the two statements differ |
| `CategoryTheory.SpectralSequence.AbutsTo.of_nonempty_iso` | `WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic` (lemma) | `StacksFrontier.Algebra.Homology.SpectralSequence.AbutsToTransport` (theorem) | yes | only if the two statements differ |
| `CategoryTheory.SpectralSequence.pageInfinity` | `WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic` (def) | `StacksCore.Algebra.Homology.SpectralSequence.PageInfinity` (def) | yes | yes, always |
| `CategoryTheory.Subobject.exists_obj_top` | `WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits` (theorem) | `StacksCore.CategoryTheory.Subobject.Limits` (lemma) | yes | only if the two statements differ |
| `CategoryTheory.Subobject.factors_of_epi_comp` | `WeilConjectures.Algebra.Homology.DerivedCategory.MittagLefflerArtinian` (lemma) | `StacksFrontier.CategoryTheory.Subobject.Butterfly` (lemma) | no | only if the two statements differ |
| `CategoryTheory.Subobject.map_obj_eq_mk` | `WeilConjectures.Mathlib.CategoryTheory.Subobject.FactorThru` (theorem) | `StacksCore.CategoryTheory.Subobject.Lattice` (lemma) | yes | only if the two statements differ |
| `CategoryTheory.conjugateEquiv_leftUnitor_inv` | `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars` (lemma) | `StacksFrontier.CategoryTheory.Bicategory.OverPullbackPseudofunctor` (lemma) | yes | only if the two statements differ |
| `CategoryTheory.constantSheafAdj_unit_app_comp_map` | `WeilConjectures.SixFunctors.ProEtale.FiniteLocallyConstantCokernel.ConstantPullback` (lemma) | `StacksFrontier.CategoryTheory.Sites.Cohomology.DegreeZeroTerminal` (theorem) | no | only if the two statements differ |
| `CategoryTheory.mateEquiv_eq_of_unit` | `WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates` (lemma) | `StacksFrontier.CategoryTheory.Adjunction.MateOfUnitSquare` (theorem) | yes | only if the two statements differ |
| `CategoryTheory.nonempty_hasRightDual_of_retract` | `WeilConjectures.CategoryTheory.Monoidal.Dualizable` (theorem) | `StacksCore.CategoryTheory.Monoidal.Rigid.Retract` (theorem) | no | only if the two statements differ |
| `CategoryTheory.whiskerRight_coevaluation_evaluation` | `WeilConjectures.CategoryTheory.Monoidal.Dualizable` (lemma) | `StacksCore.CategoryTheory.Monoidal.Rigid.Lemmas` (lemma) | no | only if the two statements differ |
| `CochainComplex.KFlat` | `WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat` (abbrev) | `StacksFrontier.Algebra.Homology.KFlat` (def) | yes | yes, always |
| `CochainComplex.Minus` | `WeilConjectures.FromJoel.Algebra.Homology.CochainComplexMinus` (abbrev) | `StacksFrontier.Algebra.Homology.HomotopyCategory.Minus` (abbrev) | yes | yes, always |
| `CochainComplex.internalHomEquiv` | `WeilConjectures.Algebra.Homology.InternalHom` (def) | `StacksFrontier.Algebra.Homology.InternalHomComplex` (def) | yes | yes, always |
| `CochainComplex.internalHomπ` | `WeilConjectures.Algebra.Homology.InternalHom` (def) | `StacksFrontier.Algebra.Homology.InternalHomComplex` (abbrev) | yes | yes, always |
| `CochainComplex.minus` | `WeilConjectures.FromJoel.Algebra.Homology.CochainComplexMinus` (def) | `StacksFrontier.Algebra.Homology.HomotopyCategory.Minus` (def) | yes | yes, always |
| `CochainComplex.monoidalClosed` | `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableTransfer` (def) | `StacksFrontier.Algebra.Homology.InternalHomComplex` (def) | no | yes, always |
| `CochainComplex.ιTensorObj_d` | `WeilConjectures.Mathlib.Algebra.Homology.Monoidal` (lemma) | `StacksFrontier.Homology.HomComplex.Basic` (theorem) | yes | only if the two statements differ |
| `CommRingCat.etale` | `WeilConjectures.RingTheory.ProEtale.Etale` (def) | `StacksFrontier.RingTheory.Etale.FilteredColimit.Basic` (def) | yes | yes, always |
| `CommRingCat.etale_iff` | `WeilConjectures.RingTheory.ProEtale.Etale` (lemma) | `StacksFrontier.RingTheory.Etale.FilteredColimit.Basic` (lemma) | yes | only if the two statements differ |
| `DerivedCategory.Plus.exists_iso_singleFunctor_obj_of_isGE_of_isLE` | `WeilConjectures.CategoryTheory.DerivedCategory.PlusDevissage` (lemma) | `StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowTruncation` (theorem) | yes | only if the two statements differ |
| `DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso` | `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus` (def) | `StacksFrontier.Algebra.Homology.DerivedCategory.TruncGELTSingle` (def) | yes | yes, always |
| `GradedRingHom.exists_mem_of_surjective` | `WeilConjectures.Mathlib.RingTheory.GradedAlgebra.RingHom` (theorem) | `StacksFrontier.AlgebraicGeometry.ProjClosedImmersion.Basic` (theorem) | yes | only if the two statements differ |
| `HenselianLocalRing.of_isIntegral` | `WeilConjectures.RingTheory.ProEtale.WStrictlyLocalUniversalHomeomorphism` (theorem) | `StacksFrontier.RingTheory.Henselian.StrictHenselization.BaseChange` (theorem) | no | only if the two statements differ |
| `HenselianLocalRing.of_ringEquiv` | `WeilConjectures.Mathlib.RingTheory.Henselian` (theorem) | `StacksFrontier.RingTheory.Henselian.StrictHenselization.BaseChange` (theorem) | yes | only if the two statements differ |
| `Homeomorph.image_mem_irreducibleComponents` | `WeilConjectures.Mathlib.Topology.NoetherianSpace` (theorem) | `StacksFrontier.AlgebraicGeometry.FibreDimension.AffineComponents` (theorem) | yes | only if the two statements differ |
| `Homeomorph.spectralSpace` | `WeilConjectures.Mathlib.Topology.Spectral.Basic` (theorem) | `StacksFrontier.Topology.Spectral.SierpinskiEmbedding` (theorem) | yes | only if the two statements differ |
| `HomogeneousLocalization.val_algebraMap` | `WeilConjectures.Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization` (lemma) | `StacksFrontier.RingTheory.HomogeneousLocalization.BaseAlgebra` (theorem) | yes | only if the two statements differ |
| `HomogeneousLocalization.val_fromZeroRingHom` | `WeilConjectures.Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization` (lemma) | `StacksFrontier.RingTheory.HomogeneousLocalization.BaseAlgebra` (theorem) | yes | only if the two statements differ |
| `HomologicalComplex.Acyclic.of_iso` | `WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex` (lemma) | `StacksFrontier.Algebra.Homology.KFlat` (theorem) | yes | only if the two statements differ |
| `HomologicalComplex.cyclesShortComplex` | `WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex` (def) | `StacksFrontier.Homology.CyclesShortComplex` (def) | yes | yes, always |
| `HomologicalComplex.isIso_ιStupidTrunc_f` | `WeilConjectures.FromJoel.Algebra.Homology.Embedding.StupidTrunc` (lemma) | `StacksFrontier.Algebra.Homology.Embedding.StupidTrunc` (lemma) | yes | only if the two statements differ |
| `HomologicalComplex.isIso_ιTruncLE_f` | `WeilConjectures.FromJoel.Algebra.Homology.Embedding.TruncLE` (lemma) | `StacksFrontier.Algebra.Homology.Embedding.TruncLEDegreewise` (lemma) | yes | only if the two statements differ |
| `HomologicalComplex.isIso_πStupidTrunc_f` | `WeilConjectures.FromJoel.Algebra.Homology.Embedding.StupidTrunc` (lemma) | `StacksFrontier.Algebra.Homology.Embedding.StupidTrunc` (lemma) | yes | only if the two statements differ |
| `HomologicalComplex.isIso_πTruncGE_f` | `WeilConjectures.FromJoel.Algebra.Homology.Embedding.TruncGE` (lemma) | `StacksFrontier.Algebra.Homology.Embedding.TruncLEDegreewise` (lemma) | yes | only if the two statements differ |
| `HomologicalComplex.linear_homologyFunctor` | `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Linear` (instance) | `StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedFunctorAdditive` (instance) | yes | only if the two statements differ |
| `HomologicalComplex.ιStupidTrunc` | `WeilConjectures.FromJoel.Algebra.Homology.Embedding.StupidTrunc` (def) | `StacksFrontier.Algebra.Homology.Embedding.StupidTrunc` (def) | yes | yes, always |
| `HomologicalComplex.πStupidTrunc` | `WeilConjectures.FromJoel.Algebra.Homology.Embedding.StupidTrunc` (def) | `StacksFrontier.Algebra.Homology.Embedding.StupidTrunc` (def) | yes | yes, always |
| `HomologicalComplex₂.total.map_add` | `WeilConjectures.FromJoel.Algebra.Homology.TotalComplex` (lemma) | `StacksCore.Algebra.Homology.TotalComplex` (lemma) | yes | only if the two statements differ |
| `HomologicalComplex₂.total.map_zero` | `WeilConjectures.FromJoel.Algebra.Homology.TotalComplex` (lemma) | `StacksCore.Algebra.Homology.TotalComplex` (lemma) | yes | only if the two statements differ |
| `Ideal.isNoetherianRing_fiber` | `WeilConjectures.RingTheory.FibreRingNoetherian` (theorem) | `StacksFrontier.RingTheory.Etale.IndEtaleFibres` (theorem) | yes | only if the two statements differ |
| `Ideal.map_iInf_of_flat` | `WeilConjectures.Mathlib.RingTheory.Flat.Equalizer` (theorem) | `StacksFrontier.RingTheory.Ideal.Annihilator.FlatBaseChange` (theorem) | yes | only if the two statements differ |
| `Ideal.map_inf_of_flat` | `WeilConjectures.Mathlib.RingTheory.Flat.Equalizer` (theorem) | `StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.Algebra` (theorem) | yes | only if the two statements differ |
| `Ideal.mem_map_smul_top_iff` | `WeilConjectures.Mathlib.RingTheory.Flat.Localization` (lemma) | `StacksFrontier.AlgebraicGeometry.Flatness.FinitelyPresented.FreeMapSpreadingOut` (theorem) | yes | only if the two statements differ |
| `IntermediateField.mem_fixingSubgroup_adjoin_iff` | `WeilConjectures.Mathlib.FieldTheory.KrullTopology` (theorem) | `StacksCore.FieldTheory.Galois.Basic` (theorem) | yes | only if the two statements differ |
| `IsAnalyticallyUnramified` | `WeilConjectures.RingTheory.AnalyticallyUnramified` (def) | `StacksFrontier.RingTheory.AnalyticallyUnramified.Defs` (def) | yes | yes, always |
| `IsCField` | `WeilConjectures.FieldTheory.Cr` (class) | `StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.CFields` (abbrev) | yes | yes, always |
| `IsCField.of_ringEquiv` | `WeilConjectures.FieldTheory.Cr` (theorem) | `StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.CFieldFiniteExtension` (theorem) | yes | only if the two statements differ |
| `IsClosed.isClosed_constructibleTopology` | `WeilConjectures.Mathlib.Topology.Spectral.ConstructibleTopology` (lemma) | `StacksFrontier.Topology.Spectral.ConstructibleTopology` (theorem) | yes | only if the two statements differ |
| `IsCohenRing` | `WeilConjectures.RingTheory.CohenRing` (def) | `StacksFrontier.RingTheory.CohenRing` (class) | yes | yes, always |
| `IsGRing` | `WeilConjectures.RingTheory.GRing` (def) | `StacksFrontier.RingTheory.GRing.Defs` (def) | yes | yes, always |
| `IsN1` | `WeilConjectures.RingTheory.JapaneseDomain` (def) | `StacksFrontier.RingTheory.Nagata.Defs` (abbrev) | yes | yes, always |
| `IsNagataRing` | `WeilConjectures.RingTheory.NagataRing` (def) | `StacksFrontier.RingTheory.Nagata.Defs` (class) | yes | yes, always |
| `IsRegularLocalRing.isDomain` | `WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs` (instance) | `StacksFrontier.RingTheory.RegularLocalRing.Basic` (theorem) | yes | only if the two statements differ |
| `IsRegularLocalRing.uniqueFactorizationMonoid` | `WeilConjectures.RingTheory.RegularLocalRing.UniqueFactorization` (theorem) | `StacksFrontier.RingTheory.RegularLocalRing.UniqueFactorization` (theorem) | yes | only if the two statements differ |
| `IsRegularRing.of_faithfullyFlat` | `WeilConjectures.RingTheory.RegularRingFaithfullyFlatDescent` (theorem) | `StacksFrontier.RingTheory.RegularRing.FaithfullyFlatDescent` (theorem) | yes | only if the two statements differ |
| `IsSepClosed.of_ringEquiv` | `WeilConjectures.Mathlib.FieldTheory.IsSepClosed` (theorem) | `StacksFrontier.RingTheory.Henselian.StrictHenselization.QuasiFinite` (theorem) | yes | only if the two statements differ |
| `IsUniversallyJapanese` | `WeilConjectures.RingTheory.NagataRing` (def) | `StacksFrontier.RingTheory.Nagata.Defs` (abbrev) | yes | yes, always |
| `Module.Flat.pi` | `WeilConjectures.Mathlib.RingTheory.Flat.Basic` (instance) | `StacksFrontier.RingTheory.Flat.Pi` (theorem) | yes | only if the two statements differ |
| `Module.Flat.prod` | `WeilConjectures.Mathlib.RingTheory.Flat.Basic` (instance) | `StacksFrontier.RingTheory.Flat.Prod` (theorem) | yes | only if the two statements differ |
| `Module.Flat.tensorProduct_of_flat` | `WeilConjectures.Mathlib.RingTheory.Flat.Stability` (theorem) | `StacksFrontier.RingTheory.Flat.BaseChangeAlongFlatAlgebra` (theorem) | yes | only if the two statements differ |
| `ModuleCat.finite_of_exactPairing` | `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Monoidal.DualFinite` (theorem) | `StacksCore.Algebra.Category.ModuleCat.Dualizable` (theorem) | no | only if the two statements differ |
| `MvPolynomial.IsHomogeneous.eval₂Hom_const_mul` | `WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous` (lemma) | `StacksFrontier.AlgebraicGeometry.ProjectiveSpaceSections.HomogeneousRescale` (theorem) | yes | only if the two statements differ |
| `MvPolynomial.IsHomogeneous.eval₂_const_mul` | `WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous` (theorem) | `StacksFrontier.AlgebraicGeometry.ProjectiveSpaceSections.HomogeneousRescale` (theorem) | yes | only if the two statements differ |
| `MvPolynomial.homogeneousSubmoduleZeroEquiv` | `WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous` (def) | `StacksFrontier.AlgebraicGeometry.Curves.PlaneCurveGenus` (def) | yes | yes, always |
| `PresheafOfModules.pullbackOplaxMonoidal` | `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback` (instance) | `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackMonoidal` (def) | yes | yes, always |
| `PresheafOfModules.pushforwardLaxMonoidal` | `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal` (instance) | `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackMonoidal` (def) | yes | yes, always |
| `PresheafOfModules.tmulRight` | `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHom` (def) | `StacksFrontier.Algebra.Category.ModuleCat.Presheaf.MonoidalClosed` (def) | yes | yes, always |
| `PresheafOfModules.tmulRight_apply` | `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHom` (lemma) | `StacksFrontier.Algebra.Category.ModuleCat.Presheaf.MonoidalClosed` (lemma) | yes | only if the two statements differ |
| `PrimeSpectrum.isConstructible_of_forall_exists_basicOpen` | `WeilConjectures.RingTheory.RelativeComponentConstructible` (theorem) | `StacksFrontier.RingTheory.GeometricallyIntegral.ReducedLocus` (theorem) | yes | only if the two statements differ |
| `PrimeSpectrum.isSpectralMap_comap` | `WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.Topology` (theorem) | `StacksFrontier.RingTheory.Spectrum.Prime.SpectralComap` (theorem) | yes | only if the two statements differ |
| `Ring.ord_ringEquiv` | `WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Basic` (theorem) | `StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.ComponentOrder` (theorem) | yes | only if the two statements differ |
| `RingHom.Flat.codescendsAlong_faithfullyFlat` | `WeilConjectures.Mathlib.RingTheory.Flat.FaithfullyFlat.Descent` (lemma) | `StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FpqcDescent` (lemma) | yes | only if the two statements differ |
| `SetLike.GradeZero.isScalarTower` | `WeilConjectures.Mathlib.Algebra.DirectSum.Internal` (instance) | `StacksFrontier.AlgebraicGeometry.ProjectiveSpaceNoetherian.Basic` (theorem) | yes | only if the two statements differ |
| `SheafOfModules.hasFiniteBiproducts` | `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree` (instance) | `StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentFromCoherence` (instance) | yes | only if the two statements differ |
| `SheafOfModules.monoidalCategory` | `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal` (def) | `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal` (def) | yes | yes, always |
| `SheafOfModules.monoidalClosed` | `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed` (def) | `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensor` (def) | yes | yes, always |
| `SheafOfModules.preservesColimitsOfShape_toSheaf` | `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification` (instance) | `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToSheafColimits` (theorem) | yes | only if the two statements differ |
| `SheafOfModules.sum_val_app_apply` | `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free` (lemma) | `StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentFromCoherence` (theorem) | yes | only if the two statements differ |
| `SheafOfModules.symmetricCategory` | `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal` (def) | `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal` (def) | yes | yes, always |
| `TensorProduct.bijective_smul_tmul` | `WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Associator` (lemma) | `StacksFrontier.AlgebraicGeometry.Modules.TensorStalkGenerators` (theorem) | yes | only if the two statements differ |
| `TopologicalSpace.NoetherianSpace.finite_connectedComponents` | `WeilConjectures.Mathlib.Topology.NoetherianSpace` (instance) | `StacksFrontier.Topology.Noetherian.LocallyConnected` (lemma) | yes | only if the two statements differ |
| `constructibleTopology_le` | `WeilConjectures.Mathlib.Topology.Spectral.ConstructibleTopology` (lemma) | `StacksFrontier.Topology.Spectral.ConstructibleTopology` (theorem) | yes | only if the two statements differ |
| `isN1_of_isN2` | `WeilConjectures.RingTheory.JapaneseDomain` (theorem) | `StacksFrontier.RingTheory.Nagata.Japanese.Localization` (theorem) | yes | only if the two statements differ |
| `ringKrullDim_ne_top_of_finiteType` | `WeilConjectures.Mathlib.RingTheory.KrullDimension.Polynomial` (theorem) | `StacksFrontier.RingTheory.KrullDimension.FiniteTypeNeTop` (theorem) | yes | only if the two statements differ |
| `topologicalKrullDimAt` | `WeilConjectures.Mathlib.Topology.KrullDimension` (def) | `StacksFrontier.Topology.Dimension.Krull` (def) | yes | yes, always |
