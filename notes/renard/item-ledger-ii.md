# Renard 2026, Chapter II: item-by-item coverage ledger

This note is the Chapter II part of the item ledger of the whole book, in the format of
the other chapter ledgers
([Chapter IV](item-ledger-iv.md), [Chapter V](item-ledger-v.md),
[Chapter VI](item-ledger-vi.md), [Chapter VII](item-ledger-vii.md)). It lists the headed items
of Chapter II and the unheaded assertions found, with printed / PDF pages
(PDF = printed + 6), Lean declarations and proof status at Library commit
`9951a27f5fd8ebbdc4bbe68eb6be65b1d0c2eb4a`; statements published later, at Library
`a54dda0d7c7c0fd4f76308fad8525ba13d9b4ce8`, are marked as such in their rows. The note
declares no section complete. A published statement is not a proof; every row keeps the proof status explicit.
The proof-status update of 14 November 2026 below rechecks every S row at Library
`4f4af6baed8c8e029e87c8303ea44c8f1d9f2f86` and supersedes those statuses.
The later focused correction below, checked at Library
`be1ec61194b5b92447fe21556e835dcc30c124e2`, adds the older stalk-kernel
statement omitted from that pass. The focused proof update of 17 November
2026, checked at Library `97101ec2cc4411be78e03b2b1cab978fecf441f9`,
records its exact proof.

Focused update, 13 November 2026: the II.2.5 rows were checked against Library
`2e5aa9989a9e5567670a14eb7079e3a844641990`. The original-module stalk
statement and regular-module Example were published at
`730bd1f25b056b8106a2697e003c1ef1733a6b30`; distributions, the full
restriction sheaf, module-sheaf basis change and the all-open vector/module
equivalence were published at `51e4d8972659f1ffcf0ca89e8eee9540a30b52d3`.
The original-module stalk comparison was then still unproved (proved since;
see the proof-status update below). Other rows retain their
earlier audit dates.

Further focused update, 13 November 2026, checked against Library
`451cce4ca176c34856be86a36801b7a3b585ae77`: the full locally constant
distribution/homeomorphism comparison and the exact proof of the six-clause
open/closed Proposition first appeared in the Library at
`7f43c3c930ff92f76dae6589da1678ad729017e5`. The two rows, evidence and pending
list below incorporate them. The original-module stalk comparison was still
unproved at that check, and the base-`T_c` equivalence composite was not yet
in the Library. Both are now resolved; see the proof-status update of
14 November 2026 below. Other rows retain their earlier audit dates.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. Chapter II is printed
pp.30–56 / PDF pp.36–62.

## Proof-status update, 14 November 2026

This update checks every row with status S
against Library `4f4af6baed8c8e029e87c8303ea44c8f1d9f2f86`. A statement is marked proved
(P) only when a Library theorem has exactly that statement as its type, with no further
hypotheses. Each theorem line was read, and no `sorry` or `admit` was found in its file.
The table gives the Library commit at which each proof first appeared. For the two
assembly modules `RenardHaarProof` and `RenardConvolutionProof`, and for the other
`RenardHaar*Proof` and `RenardConvolution*Proof` modules, no first commit was recorded;
both assembly files are present in all 36 Library snapshots that were compared. The II.3 prefixes (`RQ`, `RH`, …) are those
of the II.3 map listed below; `Distribution` abbreviates
`Langlands.HarmonicAnalysis.Distribution`, and the other short names are in
`Langlands.Sheaf.Renard`. That pass left no S row among the rows then listed.
The focused correction below added a distinct statement with status S at
that check; the proof update of 17 November records its exact proof.

The explicit base-`T_c` form of the II.2.5 Remark is the
published construction
[CompactVectorSheafModuleEquivalence](../../Langlands/Sheaf/Renard/CompactVectorSheafModuleEquivalence.md):
`basisEquivalence B : VectorSheaf X ≌ ScalarModuleSheaf B` for any open basis `B`, and
`compactEquivalence hX` for the basis `T_c` of compact opens of a t.d. space. Both compose
the all-open equivalence `VectorSheafModuleEquivalence.equivalence X` with the inverse of
the module-sheaf basis change. It is a definition module, first in Library
`0c3f30c2`.

| Row | Theorem | Proof module | First Library commit |
| --- | --- | --- | --- |
| II.1.2 vector-valued spaces | `Langlands.HarmonicAnalysis.VectorTestFunctionProof.assertions` | [VectorTestFunctionProof](../../Langlands/HarmonicAnalysis/VectorTestFunctionProof.md) | `cfedefb6` |
| II.1.3 products and tensor products | `Distribution.TensorProductProof.assertions` | [TensorProductProof](../../Langlands/HarmonicAnalysis/Distribution/TensorProductProof.md) | `51e4d897` |
| II.2.4 Proposition | `Langlands.Sheaf.Renard.compactOpenSheafCharacterization` | [CompactOpenSheafCharacterizationProof](../../Langlands/Sheaf/Renard/CompactOpenSheafCharacterizationProof.md) | `73b1430a` |
| II.2.4 Example, `F_c(X) = 𝒟(X)` | `Langlands.Sheaf.Renard.locallyConstantCompactSections` | [LocallyConstantCompactSectionsProof](../../Langlands/Sheaf/Renard/LocallyConstantCompactSectionsProof.md) | `73b1430a` |
| II.2.4 Example, `𝒟(X)` unital iff `X` compact | `Langlands.Sheaf.Renard.pointwiseTestAlgebraUnitalIffCompact` | [PointwiseTestAlgebraUnitalProof](../../Langlands/Sheaf/Renard/PointwiseTestAlgebraUnitalProof.md) | `73b1430a` |
| II.2.5 Theorem, sheaf comparison | `CompactSectionEquivalence.sheafComparisonIsIso` | [SheafComparisonIsIsoProof](../../Langlands/Sheaf/Renard/SheafComparisonIsIsoProof.md) | `b128d289` |
| II.2.5 Theorem, module comparison | `ModuleProjectorComparison.moduleComparisonIsIso` | [ModuleProjectorComparisonProof](../../Langlands/Sheaf/Renard/ModuleProjectorComparisonProof.md) | `cfedefb6` |
| II.2.5 Theorem, `M ↦ M_c(X)` an equivalence | `CompactSectionEquivalence.compactSectionFunctorIsEquivalence` | [CompactSectionEquivalenceProof](../../Langlands/Sheaf/Renard/CompactSectionEquivalenceProof.md) | `cc5aa77f` |
| II.2.5 Theorem, the inverse functor an equivalence | `CompactSectionEquivalence.projectorFunctorIsEquivalence` | [ProjectorFunctorEquivalenceProof](../../Langlands/Sheaf/Renard/ProjectorFunctorEquivalenceProof.md) | `cc5aa77f` |
| II.2.5 stalk `M_x = M / M(x)` | `ProjectorStalk.projectorStalkDescription` | [ProjectorStalkProof](../../Langlands/Sheaf/Renard/ProjectorStalkProof.md) | `ba00e097` |
| II.3.3 non-Hausdorff orbit quotient | `RQ.nonHausdorffOrbitQuotient` | [RenardOrbitNonHausdorffProof](../../Langlands/Topology/RenardOrbitNonHausdorffProof.md) | `cfedefb6` |
| II.3.6 | `RH.statements` | [RenardHaarProof](../../Langlands/HarmonicAnalysis/Distribution/RenardHaarProof.md) | not recorded; present in all 36 Library snapshots compared |
| II.3.9 Theorem, averaging map, Remark | `HR.statements` | [RenardHomogeneousProof](../../Langlands/HarmonicAnalysis/RenardHomogeneousProof.md) | `cfedefb6` |
| II.3.9 warning (nonexistence) | `HR.nonexistence` | [RenardHomogeneousNonexistenceProof](../../Langlands/HarmonicAnalysis/RenardHomogeneousNonexistenceProof.md) | `cfedefb6` |
| II.3.10 | `RC.statements` | [RenardConvolutionProof](../../Langlands/HarmonicAnalysis/Distribution/RenardConvolutionProof.md) | not recorded; present in all 36 Library snapshots compared |
| II.3.11 | `RK.statements` | [RenardCompactSubgroupProof](../../Langlands/HarmonicAnalysis/Distribution/RenardCompactSubgroupProof.md) | `b128d289` |
| II.3.12 Lemma and Remarks | `RU.statements` | [RenardUniformDensityProof](../../Langlands/HarmonicAnalysis/Distribution/RenardUniformDensityProof.md) | `b128d289` |
| II.3.12 Proposition | `HE.statements` | [RenardHeckeProof](../../Langlands/HarmonicAnalysis/Distribution/RenardHeckeProof.md) | `cfedefb6` |
| II.3.13 Definitions and Remark | `FH.statements` | [RenardFullHeckeProof](../../Langlands/HarmonicAnalysis/Distribution/RenardFullHeckeProof.md) | `cc5aa77f` |
| II.3.13 Lemma | `EP.statements` | [RenardEssentialProductsProof](../../Langlands/HarmonicAnalysis/Distribution/RenardEssentialProductsProof.md) | `cc5aa77f` |
| II.3.13 Theorem | `CO.statements` | [RenardCompletionProof](../../Langlands/HarmonicAnalysis/Distribution/RenardCompletionProof.md) | `cc5aa77f` |
| II.3.13 Corollary | `CZ.statements` | [RenardCenterProof](../../Langlands/HarmonicAnalysis/Distribution/RenardCenterProof.md) | `51e4d897` |

## Focused stalk-kernel correction, 14 November 2026

The two original-module stalk statement pairs and the
published `ProjectorStalkProof` were checked against Library
`be1ec61194b5b92447fe21556e835dcc30c124e2`, and II.2.5, printed
pp.40–42 / PDF pp.46–48, was reread. The exact proof of
`ProjectorStalk.ProjectorStalkDescription` remains published and proved.
Its independent-universe `ProjectorStalk.annihilatorDescription` identifies
the literal test-annihilator condition with vanishing under a compact-open
neighborhood projector.

The older published statement
[`Langlands.HarmonicAnalysis.PointwiseTestModule.NondegenerateStalkKernelStatement`](../../Langlands/HarmonicAnalysis/PointwiseTestStalkKernelStatement.md)
is a separate exact proof obligation. For locally profinite `X : Type uX`
and an additive `M : Type uM` with a nondegenerate nonunital action of
`𝒟(X)`, it states both the projector equivalence and equivalence with
membership in
`AddSubgroup.closure {y | ∃ f m', f x = 0 ∧ f • m' = y}`.
The latter is the module-side form of the compact-section stalk Remark on
printed p.42, derived through the preceding module/sheaf equivalence; it
is not a clause of `ProjectorStalkDescription`. Both statements retain
their existing universe scopes, and no supersession is claimed.

The exact `NondegenerateStalkKernelStatement.{uX,uM}` proof includes the
additive-closure clause at independent space and module universes. At the
14 November check a search of that Library found no exact proof of it, so
the earlier all-proved claim needed this exception. The following update
records the subsequent exact proof.

## Focused stalk-kernel proof update, 17 November 2026

This update was checked against Library
`97101ec2cc4411be78e03b2b1cab978fecf441f9`, with II.2.5, printed
pp.40–42 / PDF pp.46–48, reread. The theorem
[`Langlands.HarmonicAnalysis.PointwiseTestModule.nondegenerateStalkKernel`](../../Langlands/HarmonicAnalysis/PointwiseTestStalkKernelProof.md)
has exactly `NondegenerateStalkKernelStatement.{uX,uM}` as its type.
It proves both equivalences for a locally profinite space `X : Type uX`
and an additive commutative group `M : Type uM` with the supplied
nondegenerate nonunital action of `𝒟(X)`. The space and carrier universes
remain independent, and the input requires no complex module structure.

The proof first translates the published
`ProjectorStalk.annihilatorDescription` between compact basis opens and
compact clopen subsets, preserving the original characteristic action.
For the generated-subgroup clause, let `a` be a neighborhood indicator
killing `m` and `e` an indicator fixing `m`. Then `g = e - a * e`
vanishes at `x` and satisfies `g • m = m`, placing `m` among the
generators. Conversely, local constancy gives a compact-open
neighborhood indicator annihilating each generator `f • m'` with
`f x = 0`. Minimality of `AddSubgroup.closure` gives inclusion in the
literal annihilator subgroup. The canonical complex module recovered
from nondegeneracy is used to access that subgroup; the original test
action is retained.

The first equivalence is the original-module stalk-kernel passage on
printed pp.40–41. The second is the module-side form of the compact-section
span in the Remark on printed p.42, through the preceding module/sheaf
equivalence. The Lean proof gives a direct module argument for this
derived formulation. The colimit and quotient comparisons are the
separately published `ProjectorStalkProof` results above.

In the Library:

- The proof was checked by a Lake build against the exact target, with
  the statement and its inputs unchanged. It first appeared in the
  Library at `9e39a73d21bd6ed6fac00b01cc5e01c0db5d105b`.
- The pair at the checked Library has Lean SHA256
  `85e77953470f54003e0b839dfd711aa5c298ea67c44477aa5a1a31b4b8f94057`
  and Markdown SHA256
  `c620855b13c27234ba771920e1b6db2623b8cfc72d1a2a631997f14ba5b6d9a3`.
  A fresh development compilation also finished with zero errors or
  warnings.

This closes the separately listed stalk-kernel proof obligation. The
other rows retain their stated audit dates and source clarifications.

## How the rows were checked

Chapter II was read in the text extraction and each row checked against the Library
Markdown of the cited modules. Detailed source maps exist and are the
reference for sub-assertions:

- II.1–II.2.2: the dated Chapter II updates of the [coverage ledger](coverage.md) and the
  [germ-sheaf progress note](germ-sheaf-progress.md); the source defect in II.2.1 is in the
  [basis-sheafification audit](basis-sheafification-source.md);
- II.2.5: the [compact-section equivalence map](compact-section-equivalence-progress.md)
;
- II.3: the [II.3 map](ii3-td-groups.md), whose prefixes `FA`, `GA`, `GF`, `D`,
  `RQ`, `FS`/`FP`, `TD`, `RH`, `RM`, `RC`, `RU`, `RK`, `HE`, `HF`, `HR`, `FH`, `EP`, `CO`, `CZ`,
  `HT`/`HA` this note reuses.

Proof status was checked at the commit above with a namespace-aware scan for theorems whose
type is exactly the named statement (`proved by`). Where a module proves several clauses
through one aggregate theorem, the row names the aggregate. Status codes are those of the other
ledgers: **P** proved, **S** statement published, its proof open, **D** definition or
construction, **C** covered by other published results, **St** step of a proof, **X**
expository, **Rec** recalled, **G** genuine gap.

## II.1 Topology of t.d. spaces (30–32 / 36–38)

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| II.1.1 t.d. spaces and t.d. groups; compact open subgroups at the identity; van Dantzig | 30 / 36 | `Langlands.Topology.IsLocallyProfinite`, `isLocallyProfinite_iff_mathlib`; `Langlands.Topology.LocallyProfiniteStatements.VanDantzig` | D; P (`LocallyProfiniteProof.locallyProfiniteAssertions` proves the aggregate `LocallyProfiniteAssertions`) |
| II.1.1 Lemma (i) locally closed subspaces; (ii) finite disjoint compact-open refinements | 30 / 36 | `LocallyProfiniteStatements.LocallyClosedSubspaces`, `FiniteDisjointRefinement` | P (same aggregate) |
| II.1.1 Proposition: Baire property | 30 / 36 | `LocallyProfiniteStatements.DenseOpenIntersections` | P (same aggregate) |
| II.1.2 spaces `𝒞^∞(X)`, `𝒟(X)`, `𝒟′(X)`; support of a function | 30 / 36 | `LocallyConstant X ℂ`, `Langlands.HarmonicAnalysis.SchwartzBruhat`, `Langlands.HarmonicAnalysis.Distribution` | D |
| II.1.2 Lemma: disjoint indicator decomposition; Proposition (II.1.2.1); Corollary (II.1.2.2) | 31 / 37 | `Langlands.HarmonicAnalysis.TestFunctionDistributionStatements.Assertions` | P (`TestFunctionDistributionProof.assertions`) |
| II.1.2 support of a distribution; a distribution supported on a closed `Z` is uniquely `p_Z^*(T₀)` | 31 / 37 | topological support of [TopologicalSupport](../../Langlands/HarmonicAnalysis/Distribution/TopologicalSupport.md); `Distribution.ClosedSupportedDescentStatement` | D; P (`closedSupportedDescent`) |
| II.1.2 `ℰ′(X)` and the pairing `⟨T, f⟩` with `𝒞^∞(X)` | 31 / 37 | `Distribution.compactlySupported`, `Distribution.compactSupportPairing` | D |
| II.1.2 vector-valued spaces, (II.1.2.3)–(II.1.2.4), injectivity and bijectivity | 32 / 38 | `VectorTestFunction.Space`, `smoothTensorMap`, `compactTensorMap`; `VectorTestFunctionStatements.Assertions` | D; P (`VectorTestFunctionProof.assertions`) |
| II.1.3 product of t.d. spaces, rectangles, `𝒟(X×Y) ≃ 𝒟(X) ⊗ 𝒟(Y)`, tensor product of distributions, Fubini, Proposition `Supp(T₁⊗T₂) = Supp T₁ × Supp T₂` | 32 / 38 | `Distribution.TensorProductStatements.Assertions` (nine clauses); constructions `SchwartzBruhat.tensorLinearMap`, `Distribution.tensor` | P (`Distribution.TensorProductProof.assertions`, published on 12 November 2026) |

## II.2 Sheaves on a t.d. space (33–43 / 39–49)

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| II.2.1 Definitions: presheaves and sheaves of base `T₀`, morphisms (II.2.1.1), condition (F) | 33–34 / 39–40 | `Langlands.Sheaf.Renard.OpenBasis`, `RawPresheaf`, `Presheaf` (normalized), `SheafCondition`, `BasisSheaf` | D |
| II.2.1 stalks, germs and the étalé space; sections (II.2.1.2); `F⁺` | 34–35 / 40–41 | [BasisStalk](../../Langlands/Sheaf/Renard/BasisStalk.md), `BasisStalkRepresentativesStatement`, germ sections | D; P (`basisStalkRepresentatives`) |
| II.2.1 Proposition: `F ↦ F⁺` is left adjoint to the forgetful functor | 35 / 41 | `GermUniversalStatement` (universal property, natural Hom equivalences, `germAdjunction`) | P (`germUniversal`) |
| II.2.1 Lemma: a section with zero germs is zero; (II.2.1.3)–(II.2.1.5) | 36 / 42 | `RenardSheafGermSeparationStatement` | P (`renardSheafGermSeparation`). Source issue S1 below |
| II.2.1 Remark: uniqueness of `(F⁺, ι_F)`; a sheaf is isomorphic to `F⁺` | 37 / 43 | `RenardSheafGermUnitIsoStatement` | P (`renardSheafGermUnitIso`) |
| II.2.1 end: sheaves of base `T₀` and of base `T` are equivalent categories | 37 / 43 | [BasisAllOpenEquivalence](../../Langlands/Sheaf/Renard/BasisAllOpenEquivalence.md) (the actual equivalence) and [GermSectionBasisComparison](../../Langlands/Sheaf/Renard/GermSectionBasisComparison.md) | D (an equivalence of categories, constructed) |
| II.2.1 basis change for the module sheaves of II.2.3, used in the II.2.5 Remark | 37–39 / 43–45 | [ModuleBasisChange](../../Langlands/Sheaf/Renard/ModuleBasisChange.md): `equivalence B R`, `scalarEquivalence B`, `compactScalarEquivalence hX` | D. Any topological `X : Type u` and chosen open basis; the ring presheaf must be given on all opens. This covers `𝒞^∞_X`; module sections have universe `max u v`, with the scalar specializations in universe `u`. The underlying additive functors are the published basis-change functors |
| II.2.1 abelian structure of the presheaf and sheaf categories (used later) | — | `PresheafAbelianStatement`, `BasisSheafAbelianStatement` | P (`presheafAbelianStatement`, `basisSheafAbelianStatement`) |
| II.2.2 Definition: support of a section | 37 / 43 | `germSupport`, `germSupportAmbient`, `CompactGermSections` | D |
| II.2.2 Proposition: the support is closed in `U` | 37 / 43 | `GermSupportClosednessStatement` | P (`germSupportClosedness`) |
| II.2.2 `F_c(U)`, sections with compact support | 38 / 44 | `CompactGermSections`, `compactGermSectionSubgroup`, `compactGermSectionsFunctor` | D |
| II.2.3 sheaves of `R`-modules on a ringed space | 38 / 44 | [RingedBasisModules](../../Langlands/Sheaf/Renard/RingedBasisModules.md), [RingedBasisModuleAdapter](../../Langlands/Sheaf/Renard/RingedBasisModuleAdapter.md) | D |
| II.2.4 `T_c` is a basis; Proposition: `F ≅ F₁` with `F₁(U) ⊂ F_c(X)` increasing, union `F_c(X)`, restriction to `U` fixing and to `V ∖ U` killing `F₁(U)` | 38 / 44 | `ProjectorBasisSheaf.compactOpenBasis`; `CompactOpenSheafCharacterizationStatement` | D; P (`compactOpenSheafCharacterization`; statement published at Library `a54dda0d`) |
| II.2.4 Example: `𝒞^∞_X` is a sheaf of rings with `F_c(X) = 𝒟(X)`; `𝒟(X)` unital iff `X` compact; `𝒟(X)` an algebra with idempotents, `χ_U` filtering | 38 / 44 | `LocallyConstantScalar.basisSheaf`; `LocallyConstantCompactSectionsStatement`, `PointwiseTestAlgebraUnitalIffCompactStatement`; `PointwiseTestAlgebra.isIdempotented`, `exists_characteristic_local_unit` | D; P (`locallyConstantCompactSections`, `pointwiseTestAlgebraUnitalIffCompact`; statements `65079fee`); P (the last two) |
| II.2.5 Proposition: a sheaf of vector spaces is a sheaf of `𝒞^∞_X`-modules | 38 / 44 | [VectorSheafScalars](../../Langlands/Sheaf/Renard/VectorSheafScalars.md) (`module`, `germ_lc_smul`, `restrictSemilinear`, `appLinear`) | D (the action and its laws are proved in the module) |
| II.2.5 Remark: the two notions are equivalent categories, also for base `T` | 39 / 45 | [VectorSheafModuleEquivalence](../../Langlands/Sheaf/Renard/VectorSheafModuleEquivalence.md): `equivalence X : VectorSheaf X ≌ ModuleSheaf X`, where `ModuleSheaf X = RingedBasis.ModuleSheaf (scalarRingedBasis X)` on all opens | D, for any topological `X : Type u`, with section universe `u`. The inverse restricts scalars through constant functions; the unit and counit are identities on sections. Module-sheaf basis change is now published separately above. The explicit base-`T_c` form is the published [CompactVectorSheafModuleEquivalence](../../Langlands/Sheaf/Renard/CompactVectorSheafModuleEquivalence.md) `compactEquivalence hX`, with `basisEquivalence B` for any open basis |
| II.2.5 Lemma: the action of `𝒟(X)` on a nondegenerate module extends uniquely to `𝒞^∞(X)` | 39 / 45 | [PointwiseTestModule](../../Langlands/HarmonicAnalysis/PointwiseTestModule.md) (the extension); `PointwiseTestModule.SmoothExtensionUniqueStatement` | D; P (`smoothExtensionUnique`) |
| II.2.5 Theorem: `M_c(X)` is a nondegenerate `𝒟(X)`-module and `M ↦ M_c(X)` is an equivalence; the inverse `M ↦ (U ↦ χ_U·M)`, (II.2.5.1)–(II.2.5.2) | 39–40 / 45–46 | `CompactSectionTestModule`, `ProjectorVectorSheaf`, `SheafProjectorComparison`, `ModuleProjectorComparison` (constructions); `CompactSectionEquivalence.SheafComparisonIsIso`, `ModuleProjectorComparison.ModuleComparisonIsIso`, `CompactSectionEquivalence.CompactSectionFunctorIsEquivalence`, `CompactSectionEquivalence.ProjectorFunctorIsEquivalence` | D; P (`sheafComparisonIsIso`, `moduleComparisonIsIso`, `compactSectionFunctorIsEquivalence`, `projectorFunctorIsEquivalence`) |
| II.2.5 stalk of the sheaf of a module: `M_x = M / M(x)`, `M(x) = {m \| ∃ f, f(x) ≠ 0, f·m = 0}` | 40–41 / 46–47 | `ProjectorStalk.ProjectorStalkDescription`: literal annihilator submodule; additive quotient comparison with the actual basis stalk at independent universes, and canonical complex-linear all-open stalk comparison at a common space/carrier universe | P (`ProjectorStalk.projectorStalkDescription`); published statement. This concerns the quotient of the original module, distinct from the compact-section stalk quotient below |
| II.2.5 original-module stalk kernel and its vanishing-test generated subgroup; the second clause is derived from the compact-section Remark | 40–42 / 46–48 | `Langlands.HarmonicAnalysis.PointwiseTestModule.NondegenerateStalkKernelStatement.{uX,uM}`: the literal test-annihilator condition is equivalent both to compact-clopen neighborhood-projector vanishing and to membership in the additive subgroup generated by `f • m'` with `f x = 0`, for a nondegenerate nonunital test action at independent space/module universes | P: `Langlands.HarmonicAnalysis.PointwiseTestModule.nondegenerateStalkKernel` in [PointwiseTestStalkKernelProof](../../Langlands/HarmonicAnalysis/PointwiseTestStalkKernelProof.md); both equivalences at independent universes, with the checks in the focused proof update above |
| II.2.5 Example: `M = 𝒟(X)` gives `𝒞^∞_X` | 41 / 47 | [RegularProjectorSheaf](../../Langlands/Sheaf/Renard/RegularProjectorSheaf.md): `regularSheafIso`, `sectionScalarEquiv_smul` | D; actual sheaf isomorphism for locally profinite `X : Type u`, with proved compatibility for all locally constant scalars |
| II.2.5 Example: for continuous `q : X → Y`, nondegenerate `𝒟(X)`-modules are nondegenerate `𝒟(Y)`-modules; `𝒟(X)` is a nondegenerate `𝒟(Y)`-bimodule; forgetful and pseudo-forgetful functors (`q_!`, `q_*`) and their adjoints (`q^!`, `q^{-1}`) | 41 / 47 | the module structure through `q`: [CoinvariantTestModule](../../Langlands/Sheaf/Renard/CoinvariantTestModule.md) `pullbackModule q M` (`g · m = (g ∘ q) · m`, through the published extension of the action to `𝒞^∞(X)`, which agrees with `(g ∘ q) χ_U · m`) and its proved nondegeneracy `pullback_nondegenerate` for t.d. `Y`; they are stated for compatible test actions of an arbitrary group, and the trivial group gives the plain module. The bimodule `𝒟(X)` is the case `M = 𝒟(X)` (the algebras are commutative). The functors are I.2.3's `F_AB`, `ˇF_AB`, `I_AB`, `P_AB` for this bimodule, whose final Remark is `RenardForgetfulFunctor.ForgetfulFunctorRemarkStatement`, proved by `RenardForgetfulFunctor.forgetfulFunctorRemark` (see the [Chapter I ledger](item-ledger-i.md)) | D; P (nondegeneracy); C (the bimodule); X for the sheaf-theoretic names |
| II.2.5 restriction `F\|_Y` to a locally closed subset | 42 / 48 | [LocallyClosedRestriction](../../Langlands/Sheaf/Renard/LocallyClosedRestriction.md): `restrict F Y`, `restrictSection`, `stalkIso`, `restrictFunctor`; `closedCompactEquiv`, `closedCompactEquiv_restrictToClosed` | D. Locally representable families of actual ambient germs construct the sheaf, its stalk isomorphism and functoriality for every subset of any topological `X : Type u`. The comparison with the existing closed compact sections, support and restriction map uses `X : Type` |
| II.2.5 Definition: distributions `F_c(X)^*` on `F` and their `𝒞^∞(X)`-module structure | 42 / 48 | [Distributions](../../Langlands/Sheaf/Renard/Distributions.md): `Distribution F`, `compactSectionModule`, `distributionModule`, `smul_apply`, `transpose`, `functor` | D. Full complex algebraic dual, with `(f • T)(s) = T(f • s)`, complex compatibility and same-base equivariant transpose functor. Any topological `X : Type u`, with section universe `u`; no continuity, compactness or finite-dimensionality assumption |
| II.2.5 Proposition: `0 → F_c(U) → F_c(X) → F_c(Z) → 0` and its dual, for `Z = X ∖ U` | 42 / 48 | `ClosedRestriction.ClosedRestrictionExactStatement` in [ClosedRestrictionExactStatements](../../Langlands/Sheaf/Renard/ClosedRestrictionExactStatements.md); actual compact sections over closed `Z`, restriction map and extension-by-zero relation | P: `ClosedRestriction.closedRestrictionExact` in [ClosedRestrictionExactProof](../../Langlands/Sheaf/Renard/ClosedRestrictionExactProof.md). All six clauses are proved for locally profinite `X : Type`, with full algebraic duals and no finite-dimensionality hypothesis. The separately published `closedCompactEquiv` identifies the closed compact-section model with that of the full restriction sheaf |
| II.2.5 Remark: `F_x = F_c(X)/⟨f·φ, f(x) = 0⟩` | 42 / 48 | `CompactSectionStalks.StalkQuotientComparison` (with the map `stalkQuotientMap`) | P: `CompactSectionStalks.stalkQuotientComparison` in [CompactSectionStalksProof](../../Langlands/Sheaf/Renard/CompactSectionStalksProof.md) |
| II.2.5 isomorphisms of sheaves over a homeomorphism; induced isomorphisms of stalks and transposes | 42–43 / 48–49 | [HomeomorphSheafIso](../../Langlands/Sheaf/Renard/HomeomorphSheafIso.md): test-ring equivalence, original-module transport, compact-section and stalk equivalences, and dual transpose; [DistributionHomeomorph](../../Langlands/Sheaf/Renard/DistributionHomeomorph.md): comparisons with the `Distributions` model, `sectionEquiv` and `transpose`, with full locally constant scalar compatibility | D: both constructions are public. The `DistributionHomeomorph` module proves the derived comparison and equivariance laws for `X Y : Type` and a locally profinite source. Its scalar pullback alone retains independent base-space universes. No compactness, countability or finite-dimensionality hypothesis is added |

## II.3 t.d. topological groups (43–56 / 49–62)

All rows follow the [II.3 map](ii3-td-groups.md); its tables give the clause-level
correspondence. The aggregates `RQ.Statements`, `TD.Statements` and `RM.Statements` are proved
(by `statements` in `RenardOrbitQuotientProof`, `RenardTestDecompositionProof` and
`RenardModularProof`). At Library `4f4af6ba` the other aggregates (`RH`, `HR`, `RC`, `RK`,
`RU`, `HE`, `FH`, `EP`, `CO`, `CZ`) and the separate non-Hausdorff example are proved too; the
proof table is in the section "Proof-status update, 14 November 2026".

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| II.3.1 actions on functions, distributions; left/right translations; inversion | 43 / 49 | `FA.*`, `GA.*` | D (formulas proved) |
| II.3.2 Lemma (i) finite index of nested compact opens; (ii) `G/K` discrete, countable if `G` is countable at infinity | 43 / 49 | `FS.Assertions` | P (`FP.assertions`) |
| II.3.3 continuous actions; Proposition: finitely many orbits give an open orbit and locally closed orbits | 44 / 50 | `RQ.FiniteOrbitOpenOrbitStatement`, `RQ.FiniteOrbitsLocallyClosedStatement` | P (aggregate `RQ.Statements`). The open-orbit clause needs `Nonempty X` (source clarification S2) |
| II.3.3 orbit quotient; warning that it need not be Hausdorff | 44 / 50 | Mathlib's orbit quotient; `RQ.NonHausdorffOrbitQuotientStatement` | D; P (`RQ.nonHausdorffOrbitQuotient`) |
| II.3.3 Lemma: the projection is open; images of invariant closed and locally closed sets | 44 / 50 | `MulAction.isOpenQuotientMap_quotientMk`; `RQ.InvariantQuotientImagesStatement` | P (Mathlib; `RQ.Statements`) |
| II.3.3 a Hausdorff orbit quotient is t.d.; Corollary: `G/G_x ≃ X` for a transitive action | 44–45 / 50–51 | `RQ.HausdorffOrbitQuotientStatement`, `RQ.TransitiveQuotientHomeomorphismStatement` | P (`RQ.Statements`) |
| II.3.4 Lemma: `G/N` is t.d. for closed `N`; a t.d. group if `N` is normal | 45 / 51 | `RQ.ClosedSubgroupQuotientStatement` with Mathlib's quotient group topology | P (`RQ.Statements`) |
| II.3.5 fixed and uniformly fixed spaces; Lemma (i)–(ii): double-coset and coset expansions | 45–46 / 51–52 | `GF.*`; `TD.DoubleCosetExpansionStatement`, `TD.LeftInvariantExpansionStatement`, `TD.RightInvariantExpansionStatement` | D; P (`TD.Statements`) |
| II.3.5 Corollary: `𝒟(G)` lies in the uniformly bi-invariant functions; the uniform test unions equal `𝒟(G)` | 46 / 52 | composition of published theorems listed in the map | C |
| II.3.6 Proposition: Haar distributions, uniqueness up to a scalar; densities | 46–47 / 52–53 | `RH.Statements` | P (`RH.statements`) |
| II.3.7 modular character, Proposition (i)–(ii), Definition of unimodularity, Examples 1–3, automorphism module (II.3.7.1) | 47–48 / 53–54 | `D.renardModular`; `RM.Statements` | D; P (`RM.Statements`) |
| II.3.8 computation of the modular function, (II.3.8.1) | 48 / 54 | `RM.IndexFormulaStatement` | P (`RM.Statements`) |
| II.3.9 invariant measures on homogeneous spaces: warning, relative modular character, Theorem, averaging map, Remark | 48–50 / 54–56 | `HF.*`; `HR.Statements`; `HR.NonexistenceStatement` | D; P (`HR.statements`, `HR.nonexistence`) |
| II.3.10 convolution of distributions; Proposition (i)–(v); algebra structure; Lemma (Dirac formulas) | 50–51 / 56–57 | `D.convolution` (support clause proved intrinsically); `RC.Statements` | D; P (`RC.statements`) |
| II.3.11 Haar distribution of a compact subgroup; Lemma; Proposition (i)–(ii) | 51 / 57 | `D.compactSubgroupHaar`; `RK.Statements` | D; P (`RK.statements`) |
| II.3.12 Lemma: `𝒟(G) ≅` uniformly invariant `ℰ′(G)`; `H(G)`; Remarks 1–3; Proposition: `H(G)` has idempotents, inversion; corner Remarks | 51–53 / 57–59 | `RU.Statements`, `HE.Statements`; function-side results `HA.normalizedIndicator_idempotent`, `HA.finiteFamilyLocalUnits`, `HA.Corner` | P (`RU.statements`, `HE.statements`); P (function side). Source clarification S3 |
| II.3.13 Definitions `T*h`, `h*T`; Remark; essentially compact distributions | 53–54 / 59–60 | `D.rightHeckeConvolution`, `D.leftHeckeConvolution`, `D.rightEssentiallyCompact`; `FH.Statements` | D; P (`FH.statements`) |
| II.3.13 Lemma: `𝒟′(G)_{r.e.c.}` is a unital algebra extending `ℰ′(G)` | 54 / 60 | `EP.Statements` | P (`EP.statements`) |
| II.3.13 Theorem: `𝒟′(G)_{r.e.c.}` is the completion of `H(G)` | 55 / 61 | `CO.Statements` | P (`CO.statements`) |
| II.3.13 Corollary: the centre of `M(H(G))` is the conjugation-invariant essentially compact distributions; (II.3.13.2)–(II.3.13.3) | 55–56 / 61–62 | `CZ.Statements` | P (`CZ.statements`) |
| II.4 Notes | 56 / 62 | — | X |

## Source issues and clarifications

- **S1. II.2.1, (II.2.1.3) (printed p.36 / PDF p.42).** The inference from equal germs of the
  presheaf to equal sections is false as printed; the published
  [basis-sheafification audit](basis-sheafification-source.md) gives a counterexample and the
  repair (separation in the target sheaf on smaller basis opens), which the proved
  `germUniversal` uses.
- **S2. II.3.3 Proposition (printed p.44 / PDF p.50).** The existence of an open orbit needs
  `X` nonempty; the published statement keeps that hypothesis in the existence clause only.
- **S3. II.3.12 (printed p.52 / PDF p.58).** The text excludes the Dirac distribution from
  `H(G)` and calls `H(G)` nonunital; both hold exactly when `G` is not discrete. The published
  `RU.DiracMembershipStatement` and `RU.UnitCriterionStatement` state the corrected criteria.

## Genuine gaps of Chapter II

The previously listed full restriction, distribution and module-sheaf
basis-change construction gaps have the published constructions above, and
the explicit base-`T_c` vector/module equivalence is the published
`CompactVectorSheafModuleEquivalence`. The
II.2.4 Proposition and Example, the
four II.2.5 Theorem statements, the original-module
`ProjectorStalkDescription` and all II.3 aggregates are proved.
The older `NondegenerateStalkKernelStatement` now has the exact published
proof `nondegenerateStalkKernel`, including its additional
additive-closure clause at independent universes; see the focused proof
update. The former
exact-sequence gap is closed by the exact proof `closedRestrictionExact`. The
regular-module Example is a published construction with its intrinsic laws
proved. The separate compact-section stalk Remark is proved.

## The modules of the further focused update

- The `DistributionHomeomorph` pair first appeared in the Library at
  `7f43c3c930ff92f76dae6589da1678ad729017e5`. The actual section map is the published
  compact-section equivalence; its algebraic dual is identified with the
  existing homeomorphism transpose. Nondegeneracy of compact sections
  extends test-linearity to every locally constant multiplier.
- The proof of exactly
  `Langlands.Sheaf.Renard.ClosedRestriction.ClosedRestrictionExactStatement`
  first appeared at the same commit. It was checked by a Lake build against
  the exact target, with the statement and its inputs unchanged. The proof
  uses actual sheaf gluing and finite disjoint compact-open refinements,
  then algebraic duality. Construction of the full restriction sheaf is the
  separate published `LocallyClosedRestriction` result above.

For both pairs, the hashes match the public files at the checked Library
commit. The original-module stalk statement had no proof at that check
(its proof is now published; see the proof-status update).

## Pending

The proof obligations listed in this ledger have proved targets,
including the exact independent-universe stalk-kernel target
`NondegenerateStalkKernelStatement`; see the dated proof-status updates
above. The
full locally constant distribution/homeomorphism comparison and the explicit
base-`T_c` equivalence are public.
