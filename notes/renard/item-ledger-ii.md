# Renard 2026, Chapter II: item-by-item coverage ledger

Worker 1222, executor of the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`, revision 1. This note is the Chapter II part of the
item ledger that the task contract requires, in the format of the other chapter ledgers
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
statement omitted from that pass; its exact proof remains open.

Focused update, 13 November 2026: the II.2.5 rows were checked against Library
`2e5aa9989a9e5567670a14eb7079e3a844641990`. The original-module stalk
statement and regular-module Example were published at
`730bd1f25b056b8106a2697e003c1ef1733a6b30`; distributions, the full
restriction sheaf, module-sheaf basis change and the all-open vector/module
equivalence were published at `51e4d8972659f1ffcf0ca89e8eee9540a30b52d3`.
Their workspace and public Lean/Markdown pairs match the frozen candidates.
The original-module stalk comparison then still needed proof Task 6024
(proved since; see the proof-status update below). Other rows retain their
earlier audit dates.

Further focused update, 13 November 2026, checked against Library
`451cce4ca176c34856be86a36801b7a3b585ae77`: the full locally constant
distribution/homeomorphism comparison and the exact proof of the six-clause
open/closed Proposition are independently accepted and public at
`7f43c3c930ff92f76dae6589da1678ad729017e5`. The two rows, evidence and pending
list below incorporate those publications. Task 6024 remained ready with no
proof artifact at that check, and the base-`T_c` equivalence composite was
still with Worker 4. Both are now resolved; see the proof-status update of
14 November 2026 below. Other rows retain their earlier audit dates.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. Chapter II is printed
pp.30–56 / PDF pp.36–62.

## Proof-status update, 14 November 2026

Worker 4 made this update at Worker 1222's request. It checks every row with status S
against Library `4f4af6baed8c8e029e87c8303ea44c8f1d9f2f86`. A statement is marked proved
(P) only when a Library theorem has exactly that statement as its type, with no further
hypotheses. Worker 4 read each theorem line and found no `sorry` or `admit` in its file.
The table gives the published `lean.proof@1` record of each proof. Its Lean and Markdown
files at the checked commit have the SHA256 recorded in the record; integration IDs and
commits come from the publication receipts. No proof record was found for the two
assembly modules `RenardHaarProof` and `RenardConvolutionProof`, nor for the other
`RenardHaar*Proof` and `RenardConvolution*Proof` modules; both assembly files are present
in all 36 Library snapshots available locally. The II.3 prefixes (`RQ`, `RH`, …) are those
of the II.3 map listed below; `Distribution` abbreviates
`Langlands.HarmonicAnalysis.Distribution`, and the other short names are in
`Langlands.Sheaf.Renard`. That pass left no S row among the rows then listed.
The focused correction below adds a distinct statement with status S.

The explicit base-`T_c` form of the II.2.5 Remark, formerly kept by Worker 4, is the
published construction
[CompactVectorSheafModuleEquivalence](../../Langlands/Sheaf/Renard/CompactVectorSheafModuleEquivalence.md):
`basisEquivalence B : VectorSheaf X ≌ ScalarModuleSheaf B` for any open basis `B`, and
`compactEquivalence hX` for the basis `T_c` of compact opens of a t.d. space. Both compose
the all-open equivalence `VectorSheafModuleEquivalence.equivalence X` with the inverse of
the module-sheaf basis change. This is the `lean.definition@1` candidate
`b461191a-11cf-446b-ac4f-9c8baf45e6b2`, approved by Reviewer 1330 without
qualifications, integration ID `910137673abc4a54b29f17fc0472dc4a`, first in Library
`0c3f30c2`.

| Row | Theorem | Proof module | Proof record | Integration ID | First Library commit |
| --- | --- | --- | --- | --- | --- |
| II.1.2 vector-valued spaces | `Langlands.HarmonicAnalysis.VectorTestFunctionProof.assertions` | [VectorTestFunctionProof](../../Langlands/HarmonicAnalysis/VectorTestFunctionProof.md) | `04b88d1b-e7d6-4623-af96-03bf3c10bf67` | `dd56d9679d504bc7bae020648e4a5438` | `cfedefb6` |
| II.1.3 products and tensor products | `Distribution.TensorProductProof.assertions` | [TensorProductProof](../../Langlands/HarmonicAnalysis/Distribution/TensorProductProof.md) | `de06e23a-8791-41d4-ba83-c381a2a0aea7` | `a598899f40e44592b96412b41e869fb6` | `51e4d897` |
| II.2.4 Proposition | `Langlands.Sheaf.Renard.compactOpenSheafCharacterization` | [CompactOpenSheafCharacterizationProof](../../Langlands/Sheaf/Renard/CompactOpenSheafCharacterizationProof.md) | `23b32b1b-b83b-4ca1-a33f-f5f19567f16f` | `b4a29507c3b74483bed6fef2b5418db8` | `73b1430a` |
| II.2.4 Example, `F_c(X) = 𝒟(X)` | `Langlands.Sheaf.Renard.locallyConstantCompactSections` | [LocallyConstantCompactSectionsProof](../../Langlands/Sheaf/Renard/LocallyConstantCompactSectionsProof.md) | `28983920-60fc-4041-9bc0-0ce4f00f8575` | `8812f5f310a54bb3a3d7082172cee6b6` | `73b1430a` |
| II.2.4 Example, `𝒟(X)` unital iff `X` compact | `Langlands.Sheaf.Renard.pointwiseTestAlgebraUnitalIffCompact` | [PointwiseTestAlgebraUnitalProof](../../Langlands/Sheaf/Renard/PointwiseTestAlgebraUnitalProof.md) | `b8e10ec4-e7ff-4858-bd24-6540d8ef83ab` | `9b27e802f0f644e4b380960d88ec7f12` | `73b1430a` |
| II.2.5 Theorem, sheaf comparison | `CompactSectionEquivalence.sheafComparisonIsIso` | [SheafComparisonIsIsoProof](../../Langlands/Sheaf/Renard/SheafComparisonIsIsoProof.md) | `df4308b9-8372-477b-abe5-be5639dc5112` | `2e7af839346e41ca93d40c4c6fec4b45` | `b128d289` |
| II.2.5 Theorem, module comparison | `ModuleProjectorComparison.moduleComparisonIsIso` | [ModuleProjectorComparisonProof](../../Langlands/Sheaf/Renard/ModuleProjectorComparisonProof.md) | `e5074a48-0087-4f6f-a8ea-fb77115f6590` | `134b5b27f67a4e5fbda118a61ea98aec` | `cfedefb6` |
| II.2.5 Theorem, `M ↦ M_c(X)` an equivalence | `CompactSectionEquivalence.compactSectionFunctorIsEquivalence` | [CompactSectionEquivalenceProof](../../Langlands/Sheaf/Renard/CompactSectionEquivalenceProof.md) | `b6fe5188-6e1b-4fa6-8221-f71d70a73c24` | `5fc703e1fddd456bb4e4eda8f41d2866` | `cc5aa77f` |
| II.2.5 Theorem, the inverse functor an equivalence | `CompactSectionEquivalence.projectorFunctorIsEquivalence` | [ProjectorFunctorEquivalenceProof](../../Langlands/Sheaf/Renard/ProjectorFunctorEquivalenceProof.md) | `b08862f3-24b7-4ac8-8730-77b0578de5b0` | `7290143308c0449a9960a5ee54d3cf60` | `cc5aa77f` |
| II.2.5 stalk `M_x = M / M(x)` | `ProjectorStalk.projectorStalkDescription` | [ProjectorStalkProof](../../Langlands/Sheaf/Renard/ProjectorStalkProof.md) | `324b57a7-0088-440d-93c3-217a663a777b` | `e3977615dfec4afaa01eca82ed0cc7d2` | `ba00e097` |
| II.3.3 non-Hausdorff orbit quotient | `RQ.nonHausdorffOrbitQuotient` | [RenardOrbitNonHausdorffProof](../../Langlands/Topology/RenardOrbitNonHausdorffProof.md) | `d0be9e2b-e16b-40ed-a4fd-3a1e700ae48b` | `c1fec69e596745e1a2b641445efa815d` | `cfedefb6` |
| II.3.6 | `RH.statements` | [RenardHaarProof](../../Langlands/HarmonicAnalysis/Distribution/RenardHaarProof.md) | none found | none found | present in all 36 Library snapshots available locally |
| II.3.9 Theorem, averaging map, Remark | `HR.statements` | [RenardHomogeneousProof](../../Langlands/HarmonicAnalysis/RenardHomogeneousProof.md) | `0930f755-54c6-4e79-b188-6054bcbf46d4` | `bc435ce0153e4d30a18f1d4173e82de5` | `cfedefb6` |
| II.3.9 warning (nonexistence) | `HR.nonexistence` | [RenardHomogeneousNonexistenceProof](../../Langlands/HarmonicAnalysis/RenardHomogeneousNonexistenceProof.md) | `88155024-422d-49ce-8f2b-49a9093b79f5` | `beb398b032f84eebad8cc6d2e306abfd` | `cfedefb6` |
| II.3.10 | `RC.statements` | [RenardConvolutionProof](../../Langlands/HarmonicAnalysis/Distribution/RenardConvolutionProof.md) | none found | none found | present in all 36 Library snapshots available locally |
| II.3.11 | `RK.statements` | [RenardCompactSubgroupProof](../../Langlands/HarmonicAnalysis/Distribution/RenardCompactSubgroupProof.md) | `75da5762-9deb-4be2-b1b7-29e644e58db2` | `7e1dd56851ef4d2d8b81b09268582aca` | `b128d289` |
| II.3.12 Lemma and Remarks | `RU.statements` | [RenardUniformDensityProof](../../Langlands/HarmonicAnalysis/Distribution/RenardUniformDensityProof.md) | `f78b0a8b-7474-4db7-8b81-c416e10a1b67` | `d4dca118d56e4c7f9c3c2884d0d01f11` | `b128d289` |
| II.3.12 Proposition | `HE.statements` | [RenardHeckeProof](../../Langlands/HarmonicAnalysis/Distribution/RenardHeckeProof.md) | `20824593-d388-4461-8589-cdb5544a2252` | `d026caa343f84ccd857cec69edefcb95` | `cfedefb6` |
| II.3.13 Definitions and Remark | `FH.statements` | [RenardFullHeckeProof](../../Langlands/HarmonicAnalysis/Distribution/RenardFullHeckeProof.md) | `d18e70f4-8645-4000-8633-e344d64a5d9d` | `d7253eda1b07448da64006309a224942` | `cc5aa77f` |
| II.3.13 Lemma | `EP.statements` | [RenardEssentialProductsProof](../../Langlands/HarmonicAnalysis/Distribution/RenardEssentialProductsProof.md) | `d8c4cb23-efa6-45e8-b416-30ec3fca31a1` | `ef2dbea47c5f4b42b2cf2ec19e76e695` | `cc5aa77f` |
| II.3.13 Theorem | `CO.statements` | [RenardCompletionProof](../../Langlands/HarmonicAnalysis/Distribution/RenardCompletionProof.md) | `2b226627-05dc-40fd-97d7-f9a4d09cf8c6` | `8f2d164209ab4627ad1a4ce087166af0` | `cc5aa77f` |
| II.3.13 Corollary | `CZ.statements` | [RenardCenterProof](../../Langlands/HarmonicAnalysis/Distribution/RenardCenterProof.md) | `9a63757c-d353-4e18-8b43-b1e69add99b7` | `751f91df0f2d4df38642babf514b9eba` | `51e4d897` |

## Focused stalk-kernel correction, 14 November 2026

Worker 1222 checked the two original-module stalk statement pairs and the
published `ProjectorStalkProof` against Library
`be1ec61194b5b92447fe21556e835dcc30c124e2`, and reread II.2.5, printed
pp.40–42 / PDF pp.46–48. The exact proof of
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

Task 6922 (`de99dcc2-45dd-4e05-859b-a50d55157e35`) owns the exact
`NondegenerateStalkKernelStatement.{uX,uM}` proof, including the
additive-closure clause at independent space and module universes. At this
check it is revision 1, ready, with no proof candidate. Searches of the
current Library and task targets found no exact proof already closing it.
The earlier claim that every Chapter II statement is proved therefore
needs this exception. A related published proof supplies a route to the
first clause, rather than proof evidence for the entire target.

## How the rows were checked

Worker 1222 read Chapter II in the text extraction and checked each row against the Library
Markdown of the cited modules. Detailed source maps by other workers exist and are the
reference for sub-assertions:

- II.1–II.2.2: the dated Chapter II updates of the [coverage ledger](coverage.md) and the
  [germ-sheaf progress note](germ-sheaf-progress.md); the source defect in II.2.1 is in the
  [basis-sheafification audit](basis-sheafification-source.md);
- II.2.5: the [compact-section equivalence map](compact-section-equivalence-progress.md)
  (Task 5338);
- II.3: the [II.3 map](ii3-td-groups.md) (Task 5298), whose prefixes `FA`, `GA`, `GF`, `D`,
  `RQ`, `FS`/`FP`, `TD`, `RH`, `RM`, `RC`, `RU`, `RK`, `HE`, `HF`, `HR`, `FH`, `EP`, `CO`, `CZ`,
  `HT`/`HA` this note reuses.

Proof status was checked at the commit above with a namespace-aware scan for theorems whose
type is exactly the named statement (`proved by`). Where a module proves several clauses
through one aggregate theorem, the row names the aggregate. Task identifiers are task numbers
or the first eight hexadecimal digits of the task ID. Status codes are those of the other
ledgers: **P** proved, **S** statement published with an open proof task, **D** definition or
construction, **C** covered by other published results, **St** step of a proof, **X**
expository, **Rec** recalled, **A** candidate accepted and waiting for integration, **R** candidate under review, **G** genuine gap.

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
| II.1.2 vector-valued spaces, (II.1.2.3)–(II.1.2.4), injectivity and bijectivity | 32 / 38 | `VectorTestFunction.Space`, `smoothTensorMap`, `compactTensorMap`; `VectorTestFunctionStatements.Assertions` | D; P (`VectorTestFunctionProof.assertions`, task `7d487b2c`) |
| II.1.3 product of t.d. spaces, rectangles, `𝒟(X×Y) ≃ 𝒟(X) ⊗ 𝒟(Y)`, tensor product of distributions, Fubini, Proposition `Supp(T₁⊗T₂) = Supp T₁ × Supp T₂` | 32 / 38 | `Distribution.TensorProductStatements.Assertions` (nine clauses); constructions `SchwartzBruhat.tensorLinearMap`, `Distribution.tensor` | P (`Distribution.TensorProductProof.assertions`, Task 5751, published by Worker 1222 on 12 November 2026) |

## II.2 Sheaves on a t.d. space (33–43 / 39–49)

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| II.2.1 Definitions: presheaves and sheaves of base `T₀`, morphisms (II.2.1.1), condition (F) | 33–34 / 39–40 | `Langlands.Sheaf.Renard.OpenBasis`, `RawPresheaf`, `Presheaf` (normalized), `SheafCondition`, `BasisSheaf` | D |
| II.2.1 stalks, germs and the étalé space; sections (II.2.1.2); `F⁺` | 34–35 / 40–41 | [BasisStalk](../../Langlands/Sheaf/Renard/BasisStalk.md), `BasisStalkRepresentativesStatement`, germ sections | D; P (`basisStalkRepresentatives`) |
| II.2.1 Proposition: `F ↦ F⁺` is left adjoint to the forgetful functor | 35 / 41 | `GermUniversalStatement` (universal property, natural Hom equivalences, `germAdjunction`) | P (`germUniversal`) |
| II.2.1 Lemma: a section with zero germs is zero; (II.2.1.3)–(II.2.1.5) | 36 / 42 | `RenardSheafGermSeparationStatement` | P (`renardSheafGermSeparation`). Source issue S1 below |
| II.2.1 Remark: uniqueness of `(F⁺, ι_F)`; a sheaf is isomorphic to `F⁺` | 37 / 43 | `RenardSheafGermUnitIsoStatement` | P (`renardSheafGermUnitIso`) |
| II.2.1 end: sheaves of base `T₀` and of base `T` are equivalent categories | 37 / 43 | [BasisAllOpenEquivalence](../../Langlands/Sheaf/Renard/BasisAllOpenEquivalence.md) (the actual equivalence) and [GermSectionBasisComparison](../../Langlands/Sheaf/Renard/GermSectionBasisComparison.md) | D (an equivalence of categories, constructed) |
| II.2.1 basis change for the module sheaves of II.2.3, used in the II.2.5 Remark | 37–39 / 43–45 | [ModuleBasisChange](../../Langlands/Sheaf/Renard/ModuleBasisChange.md): `equivalence B R`, `scalarEquivalence B`, `compactScalarEquivalence hX` | D: published candidate `6522907f-bf86-42e4-983d-edd48d5d950b`. Any topological `X : Type u` and chosen open basis; the ring presheaf must be given on all opens. This covers `𝒞^∞_X`; module sections have universe `max u v`, with the scalar specializations in universe `u`. The underlying additive functors are the published basis-change functors |
| II.2.1 abelian structure of the presheaf and sheaf categories (used later) | — | `PresheafAbelianStatement`, `BasisSheafAbelianStatement` | P (`presheafAbelianStatement`, `basisSheafAbelianStatement`) |
| II.2.2 Definition: support of a section | 37 / 43 | `germSupport`, `germSupportAmbient`, `CompactGermSections` | D |
| II.2.2 Proposition: the support is closed in `U` | 37 / 43 | `GermSupportClosednessStatement` | P (`germSupportClosedness`) |
| II.2.2 `F_c(U)`, sections with compact support | 38 / 44 | `CompactGermSections`, `compactGermSectionSubgroup`, `compactGermSectionsFunctor` | D |
| II.2.3 sheaves of `R`-modules on a ringed space | 38 / 44 | [RingedBasisModules](../../Langlands/Sheaf/Renard/RingedBasisModules.md), [RingedBasisModuleAdapter](../../Langlands/Sheaf/Renard/RingedBasisModuleAdapter.md) | D |
| II.2.4 `T_c` is a basis; Proposition: `F ≅ F₁` with `F₁(U) ⊂ F_c(X)` increasing, union `F_c(X)`, restriction to `U` fixing and to `V ∖ U` killing `F₁(U)` | 38 / 44 | `ProjectorBasisSheaf.compactOpenBasis`; `CompactOpenSheafCharacterizationStatement` | D; P (`compactOpenSheafCharacterization`, Task 5779; statement candidate `65079fee`, published at Library `a54dda0d`) |
| II.2.4 Example: `𝒞^∞_X` is a sheaf of rings with `F_c(X) = 𝒟(X)`; `𝒟(X)` unital iff `X` compact; `𝒟(X)` an algebra with idempotents, `χ_U` filtering | 38 / 44 | `LocallyConstantScalar.basisSheaf`; `LocallyConstantCompactSectionsStatement`, `PointwiseTestAlgebraUnitalIffCompactStatement`; `PointwiseTestAlgebra.isIdempotented`, `exists_characteristic_local_unit` | D; P (`locallyConstantCompactSections`, `pointwiseTestAlgebraUnitalIffCompact`, Task 5779; statements `65079fee`); P (the last two) |
| II.2.5 Proposition: a sheaf of vector spaces is a sheaf of `𝒞^∞_X`-modules | 38 / 44 | [VectorSheafScalars](../../Langlands/Sheaf/Renard/VectorSheafScalars.md) (`module`, `germ_lc_smul`, `restrictSemilinear`, `appLinear`) | D (the action and its laws are proved in the module) |
| II.2.5 Remark: the two notions are equivalent categories, also for base `T` | 39 / 45 | [VectorSheafModuleEquivalence](../../Langlands/Sheaf/Renard/VectorSheafModuleEquivalence.md): `equivalence X : VectorSheaf X ≌ ModuleSheaf X`, where `ModuleSheaf X = RingedBasis.ModuleSheaf (scalarRingedBasis X)` on all opens | D: published candidate `e27ff568-7198-4e8d-a2c7-bd765d5e150a`, for any topological `X : Type u`, with section universe `u`. The inverse restricts scalars through constant functions; the unit and counit are identities on sections. Module-sheaf basis change is now published separately above. The explicit base-`T_c` form is the published [CompactVectorSheafModuleEquivalence](../../Langlands/Sheaf/Renard/CompactVectorSheafModuleEquivalence.md) `compactEquivalence hX` (candidate `b461191a-11cf-446b-ac4f-9c8baf45e6b2`), with `basisEquivalence B` for any open basis |
| II.2.5 Lemma: the action of `𝒟(X)` on a nondegenerate module extends uniquely to `𝒞^∞(X)` | 39 / 45 | [PointwiseTestModule](../../Langlands/HarmonicAnalysis/PointwiseTestModule.md) (the extension); `PointwiseTestModule.SmoothExtensionUniqueStatement` | D; P (`smoothExtensionUnique`) |
| II.2.5 Theorem: `M_c(X)` is a nondegenerate `𝒟(X)`-module and `M ↦ M_c(X)` is an equivalence; the inverse `M ↦ (U ↦ χ_U·M)`, (II.2.5.1)–(II.2.5.2) | 39–40 / 45–46 | `CompactSectionTestModule`, `ProjectorVectorSheaf`, `SheafProjectorComparison`, `ModuleProjectorComparison` (constructions); `CompactSectionEquivalence.SheafComparisonIsIso`, `ModuleProjectorComparison.ModuleComparisonIsIso`, `CompactSectionEquivalence.CompactSectionFunctorIsEquivalence`, `CompactSectionEquivalence.ProjectorFunctorIsEquivalence` | D; P (`sheafComparisonIsIso`, `moduleComparisonIsIso`, `compactSectionFunctorIsEquivalence`, `projectorFunctorIsEquivalence`; Tasks 5508, 5533, 5534, 5535) |
| II.2.5 stalk of the sheaf of a module: `M_x = M / M(x)`, `M(x) = {m \| ∃ f, f(x) ≠ 0, f·m = 0}` | 40–41 / 46–47 | `ProjectorStalk.ProjectorStalkDescription`: literal annihilator submodule; additive quotient comparison with the actual basis stalk at independent universes, and canonical complex-linear all-open stalk comparison at a common space/carrier universe | P (`ProjectorStalk.projectorStalkDescription`, proof record `324b57a7-0088-440d-93c3-217a663a777b`, Task 6024 `a8201ec1-b34c-4d82-92d8-505edbb9d235`); published statement `9cc76587-21dc-4142-b7a1-44d6ba0b7e18`. This concerns the quotient of the original module, distinct from the compact-section stalk quotient below |
| II.2.5 original-module stalk kernel and its vanishing-test generated subgroup; the second clause is derived from the compact-section Remark | 40–42 / 46–48 | `Langlands.HarmonicAnalysis.PointwiseTestModule.NondegenerateStalkKernelStatement.{uX,uM}`: the literal test-annihilator condition is equivalent both to compact-clopen neighborhood-projector vanishing and to membership in the additive subgroup generated by `f • m'` with `f x = 0`, for a nondegenerate nonunital test action at independent space/module universes | S: exact proof Task 6922 (`de99dcc2-45dd-4e05-859b-a50d55157e35`). The published `ProjectorStalk.annihilatorDescription` supplies the first comparison, but its aggregate does not state the additive-closure clause; see the focused correction above |
| II.2.5 Example: `M = 𝒟(X)` gives `𝒞^∞_X` | 41 / 47 | [RegularProjectorSheaf](../../Langlands/Sheaf/Renard/RegularProjectorSheaf.md): `regularSheafIso`, `sectionScalarEquiv_smul` | D: published candidate `741c323b-249d-4ed0-ac4c-6728574d5b16`; actual sheaf isomorphism for locally profinite `X : Type u`, with proved compatibility for all locally constant scalars |
| II.2.5 Example: for continuous `q : X → Y`, nondegenerate `𝒟(X)`-modules are nondegenerate `𝒟(Y)`-modules; `𝒟(X)` is a nondegenerate `𝒟(Y)`-bimodule; forgetful and pseudo-forgetful functors (`q_!`, `q_*`) and their adjoints (`q^!`, `q^{-1}`) | 41 / 47 | the module structure through `q`: [CoinvariantTestModule](../../Langlands/Sheaf/Renard/CoinvariantTestModule.md) `pullbackModule q M` (`g · m = (g ∘ q) · m`, through the published extension of the action to `𝒞^∞(X)`, which agrees with `(g ∘ q) χ_U · m`) and its proved nondegeneracy `pullback_nondegenerate` for t.d. `Y`; they are stated for compatible test actions of an arbitrary group, and the trivial group gives the plain module. The bimodule `𝒟(X)` is the case `M = 𝒟(X)` (the algebras are commutative). The functors are I.2.3's `F_AB`, `ˇF_AB`, `I_AB`, `P_AB` for this bimodule, whose final Remark is `RenardForgetfulFunctor.ForgetfulFunctorRemarkStatement`, proved by `RenardForgetfulFunctor.forgetfulFunctorRemark` (see the [Chapter I ledger](item-ledger-i.md)) | D; P (nondegeneracy); C (the bimodule); X for the sheaf-theoretic names |
| II.2.5 restriction `F\|_Y` to a locally closed subset | 42 / 48 | [LocallyClosedRestriction](../../Langlands/Sheaf/Renard/LocallyClosedRestriction.md): `restrict F Y`, `restrictSection`, `stalkIso`, `restrictFunctor`; `closedCompactEquiv`, `closedCompactEquiv_restrictToClosed` | D: published candidate `b7a1e0fc-4e82-4893-a657-eef7891098e5`. Locally representable families of actual ambient germs construct the sheaf, its stalk isomorphism and functoriality for every subset of any topological `X : Type u`. The comparison with the existing closed compact sections, support and restriction map uses `X : Type` |
| II.2.5 Definition: distributions `F_c(X)^*` on `F` and their `𝒞^∞(X)`-module structure | 42 / 48 | [Distributions](../../Langlands/Sheaf/Renard/Distributions.md): `Distribution F`, `compactSectionModule`, `distributionModule`, `smul_apply`, `transpose`, `functor` | D: published candidate `03df3d64-b66d-4277-81fd-71fc6577a961`. Full complex algebraic dual, with `(f • T)(s) = T(f • s)`, complex compatibility and same-base equivariant transpose functor. Any topological `X : Type u`, with section universe `u`; no continuity, compactness or finite-dimensionality assumption |
| II.2.5 Proposition: `0 → F_c(U) → F_c(X) → F_c(Z) → 0` and its dual, for `Z = X ∖ U` | 42 / 48 | `ClosedRestriction.ClosedRestrictionExactStatement` in [ClosedRestrictionExactStatements](../../Langlands/Sheaf/Renard/ClosedRestrictionExactStatements.md); actual compact sections over closed `Z`, restriction map and extension-by-zero relation | P: `ClosedRestriction.closedRestrictionExact` in [ClosedRestrictionExactProof](../../Langlands/Sheaf/Renard/ClosedRestrictionExactProof.md), Task 5960. All six clauses are proved for locally profinite `X : Type`, with full algebraic duals and no finite-dimensionality hypothesis. The separately published `closedCompactEquiv` identifies the closed compact-section model with that of the full restriction sheaf |
| II.2.5 Remark: `F_x = F_c(X)/⟨f·φ, f(x) = 0⟩` | 42 / 48 | `CompactSectionStalks.StalkQuotientComparison` (with the map `stalkQuotientMap`) | P: `CompactSectionStalks.stalkQuotientComparison` in [CompactSectionStalksProof](../../Langlands/Sheaf/Renard/CompactSectionStalksProof.md), former Task 5507 |
| II.2.5 isomorphisms of sheaves over a homeomorphism; induced isomorphisms of stalks and transposes | 42–43 / 48–49 | [HomeomorphSheafIso](../../Langlands/Sheaf/Renard/HomeomorphSheafIso.md): test-ring equivalence, original-module transport, compact-section and stalk equivalences, and dual transpose; [DistributionHomeomorph](../../Langlands/Sheaf/Renard/DistributionHomeomorph.md): comparisons with the `Distributions` model, `sectionEquiv` and `transpose`, with full locally constant scalar compatibility | D: both constructions are public. Candidate `3e24fe18-e97f-449b-b572-cccfb21f1eb6` proves the derived comparison and equivariance laws for `X Y : Type` and a locally profinite source. Its scalar pullback alone retains independent base-space universes. No compactness, countability or finite-dimensionality hypothesis is added |

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
| II.3.3 orbit quotient; warning that it need not be Hausdorff | 44 / 50 | Mathlib's orbit quotient; `RQ.NonHausdorffOrbitQuotientStatement` | D; P (`RQ.nonHausdorffOrbitQuotient`, Task 5538) |
| II.3.3 Lemma: the projection is open; images of invariant closed and locally closed sets | 44 / 50 | `MulAction.isOpenQuotientMap_quotientMk`; `RQ.InvariantQuotientImagesStatement` | P (Mathlib; `RQ.Statements`) |
| II.3.3 a Hausdorff orbit quotient is t.d.; Corollary: `G/G_x ≃ X` for a transitive action | 44–45 / 50–51 | `RQ.HausdorffOrbitQuotientStatement`, `RQ.TransitiveQuotientHomeomorphismStatement` | P (`RQ.Statements`) |
| II.3.4 Lemma: `G/N` is t.d. for closed `N`; a t.d. group if `N` is normal | 45 / 51 | `RQ.ClosedSubgroupQuotientStatement` with Mathlib's quotient group topology | P (`RQ.Statements`) |
| II.3.5 fixed and uniformly fixed spaces; Lemma (i)–(ii): double-coset and coset expansions | 45–46 / 51–52 | `GF.*`; `TD.DoubleCosetExpansionStatement`, `TD.LeftInvariantExpansionStatement`, `TD.RightInvariantExpansionStatement` | D; P (`TD.Statements`) |
| II.3.5 Corollary: `𝒟(G)` lies in the uniformly bi-invariant functions; the uniform test unions equal `𝒟(G)` | 46 / 52 | composition of published theorems listed in the map | C |
| II.3.6 Proposition: Haar distributions, uniqueness up to a scalar; densities | 46–47 / 52–53 | `RH.Statements` | P (`RH.statements`; former Task 5392, not among the current tasks) |
| II.3.7 modular character, Proposition (i)–(ii), Definition of unimodularity, Examples 1–3, automorphism module (II.3.7.1) | 47–48 / 53–54 | `D.renardModular`; `RM.Statements` | D; P (`RM.Statements`) |
| II.3.8 computation of the modular function, (II.3.8.1) | 48 / 54 | `RM.IndexFormulaStatement` | P (`RM.Statements`) |
| II.3.9 invariant measures on homogeneous spaces: warning, relative modular character, Theorem, averaging map, Remark | 48–50 / 54–56 | `HF.*`; `HR.Statements`; `HR.NonexistenceStatement` | D; P (`HR.statements`, `HR.nonexistence`; Tasks 5524, 5539) |
| II.3.10 convolution of distributions; Proposition (i)–(v); algebra structure; Lemma (Dirac formulas) | 50–51 / 56–57 | `D.convolution` (support clause proved intrinsically); `RC.Statements` | D; P (`RC.statements`; former Task 5394, not among the current tasks) |
| II.3.11 Haar distribution of a compact subgroup; Lemma; Proposition (i)–(ii) | 51 / 57 | `D.compactSubgroupHaar`; `RK.Statements` | D; P (`RK.statements`, Task 5525) |
| II.3.12 Lemma: `𝒟(G) ≅` uniformly invariant `ℰ′(G)`; `H(G)`; Remarks 1–3; Proposition: `H(G)` has idempotents, inversion; corner Remarks | 51–53 / 57–59 | `RU.Statements`, `HE.Statements`; function-side results `HA.normalizedIndicator_idempotent`, `HA.finiteFamilyLocalUnits`, `HA.Corner` | P (`RU.statements`, `HE.statements`; Tasks 5526, 5527); P (function side). Source clarification S3 |
| II.3.13 Definitions `T*h`, `h*T`; Remark; essentially compact distributions | 53–54 / 59–60 | `D.rightHeckeConvolution`, `D.leftHeckeConvolution`, `D.rightEssentiallyCompact`; `FH.Statements` | D; P (`FH.statements`, Task 5528) |
| II.3.13 Lemma: `𝒟′(G)_{r.e.c.}` is a unital algebra extending `ℰ′(G)` | 54 / 60 | `EP.Statements` | P (`EP.statements`, Task 5529) |
| II.3.13 Theorem: `𝒟′(G)_{r.e.c.}` is the completion of `H(G)` | 55 / 61 | `CO.Statements` | P (`CO.statements`, Task 5530) |
| II.3.13 Corollary: the centre of `M(H(G))` is the conjugation-invariant essentially compact distributions; (II.3.13.2)–(II.3.13.3) | 55–56 / 61–62 | `CZ.Statements` | P (`CZ.statements`, Task 5531) |
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
`CompactVectorSheafModuleEquivalence` (candidate `b461191a`). The
II.2.4 Proposition and Example (Task 5779), the
four II.2.5 Theorem statements (Tasks 5508, 5533–5535), the original-module
`ProjectorStalkDescription` (Task 6024) and all II.3 aggregates are proved.
The older `NondegenerateStalkKernelStatement` retains an exact proof
obligation, owned by Task 6922, including its additional additive-closure
clause; see the focused correction. The former
exact-sequence gap is closed by the exact proof from Task 5960. The
regular-module Example is a published construction with its intrinsic laws
proved. The separate compact-section stalk Remark is proved.

## Publication evidence for the further focused update

- `3e24fe18-e97f-449b-b572-cccfb21f1eb6`, Worker 1222, independently approved
  by Reviewer 1132 without unresolved qualifications and published at
  `7f43c3c930ff92f76dae6589da1678ad729017e5`, supplies the
  `DistributionHomeomorph` pair. The actual section map is the published
  compact-section equivalence; its algebraic dual is identified with the
  existing homeomorphism transpose. Nondegeneracy of compact sections
  extends test-linearity to every locally constant multiplier.
- `f9d6b9c7-bbbc-4443-9267-356747c8d0db`, Worker 337, Task 5960,
  independently approved by Reviewer 1163 without unresolved qualifications
  and published at the same commit, proves exactly
  `Langlands.Sheaf.Renard.ClosedRestriction.ClosedRestrictionExactStatement`.
  The `lean.proof@1` receipt passes Lake build, exact target, unchanged
  statement and frozen inputs. The proof uses actual sheaf gluing and
  finite disjoint compact-open refinements, then algebraic duality.
  Construction of the full restriction sheaf is the separate published
  `LocallyClosedRestriction` result above.

For both entry pairs, the frozen candidate hashes match the workspace and
the public files at the checked Library commit. The original-module stalk
task `a8201ec1-b34c-4d82-92d8-505edbb9d235` (Task 6024) was inspected
separately: it had no proof artifact at that check (its proof is now
published; see the proof-status update). These focused checks do not update
the status of every other task in this ledger.

## Pending

The exact proof of
`Langlands.HarmonicAnalysis.PointwiseTestModule.NondegenerateStalkKernelStatement`
remains open under Task 6922 (`de99dcc2-45dd-4e05-859b-a50d55157e35`).
The proof tasks formerly listed here (`7d487b2c`, 5751, 5779, 5508,
5533–5535, 6024, 5392, 5394, 5524–5531, 5538, 5539) all have proved
targets; see the proof-status update and its focused correction above. The
full locally constant distribution/homeomorphism comparison and the explicit
base-`T_c` equivalence are public.
