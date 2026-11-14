# Renard 2026, Chapter V: item-by-item coverage ledger

Worker 1222, executor of the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`, revision 1. This note is the Chapter V
part of the item ledger that the task contract requires, in the format of the published
[Chapter VI](item-ledger-vi.md) and [Chapter VII](item-ledger-vii.md) ledgers. Chapter V
has few headed items: most of its assertions sit in numbered paragraphs. The rows therefore
follow the numbered paragraphs V.1–V.5.5 and the headed items inside them. The note declares
no section complete. A published statement is not a proof; every row keeps the proof status
explicit.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. Printed page
numbers are given first and PDF page numbers second; PDF = printed + 6. Library facts
refer to commit `9951a27f5fd8ebbdc4bbe68eb6be65b1d0c2eb4a` unless stated otherwise.
The V.2.2 and V.3.1–V.3.24 rows have focused 13 November 2026 updates against Library
`430cc03fe803c5dbf74bc3baf91e8f7a2c26ea9c`. The V.5.3 module-form row has a
separate 13 November update against Library
`a0627c91621a99df78a1079f47cfb76995f077fa`, verified below. A further
13 November update of V.3.24 and V.4.2 uses Library
`dad81bc65e375153a3adcb2748ee7261d4444dab`: it records the published
finite-generation statement, actual nonnegative quotient construction, integral
strict faces, actual strict-image statement and closed-root-subset unit.
Other rows retain their earlier audit status. These updates distinguish
statements, exact proofs and candidates awaiting integration.

Chapter V is mostly a recall of algebraic-group and Bruhat–Tits theory with section-level
references. The published
[Chapter V structural-inputs ledger](chapter-v-structural-inputs.md) (Worker 164) classifies
those recalled assertions (rows S01–S23) and the book's own deductions (rows D01–D08). This
note gives, for each paragraph, the Library declarations that now state or prove it.

## How the rows were checked

Worker 1222 read Chapter V in the text extraction and checked the displayed formulas with
overlines in the rendered PDF. For each paragraph the Library Markdown files citing it were
listed, and their declarations were read. Proof status comes from a scan of the Library for
theorems whose type is exactly the statement (`proved by`). A `task` entry is a
`lean.proof@1` task whose contract names the statement. Task identifiers are abbreviated to
their first eight hexadecimal digits, or given by task number.

Namespace abbreviations: `GS` = `Langlands.GroupScheme`, `PL` = `Langlands.Plancherel`,
`RC` = `Langlands.Plancherel.RenardCartan`, `RP` = `Langlands.Aubert.General.RepresentedParabolic`,
`RPF` = `Langlands.Aubert.General.RationalPointFamily`, `SC` = `Langlands.BruhatTits.SpecialCompact`.

Status codes, as in the Chapter VI ledger:

- **P**: proved; the named theorem has exactly the statement's type.
- **S**: statement published; its proof remains an obligation, with the exact task given where assigned.
- **D**: definition or construction.
- **C**: covered by published statements that are stronger or equivalent, or derived from
  them; the row says which.
- **St**: a step of the proof of a stated result.
- **X**: expository, convention or attribution.
- **Rec**: an assertion recalled from the literature with a section-level reference (a row
  S.. of the structural-inputs ledger). The row says whether the Library states it.
- **A**: candidate accepted by review, waiting for integration.
- **R**: candidate staged, under review.
- **G**: genuine gap.

## V.1 Nonarchimedean local fields (103–104 / 109–110)

| Item | Lean | Status |
| --- | --- | --- |
| Normalized valuation, `𝔒_F`, `𝔓_F`, units, uniformizer decomposition, finite residue field, `|x|_F = q^{-v_F(x)}` | Mathlib's `IsNonarchimedeanLocalField` with `ValuativeRel`; `Langlands.FML.ord` and its laws, `LocalField.ResidueField`, `residueCardinality`, `residueNormalizedAbsoluteValue` ([ResidueNormalization](../../Langlands/LocalField/ResidueNormalization.md)); `PL.fieldNormUnits`, `PL.fieldOrderUnits` | Rec (ref. [21]); D |
| Additive Haar measure and `∫ f(ax) dx = |a|_F^{-1} ∫ f(x) dx` | `Langlands.HarmonicAnalysis.GeneralScalarHaarScalingStatement` | P: `generalScalarHaarScalingStatement` |
| Topology of `F`, of `GL_n(F)` and the subgroups `K_n` | Mathlib local-field topology; `rationalPointTopology` and `rationalPoint_isTopologicalGroup`, `rationalPoint_locallyCompactSpace` | Rec; D |

## V.2 Reductive p-adic groups (104–109 / 110–115)

| Item | Lean | Status |
| --- | --- | --- |
| V.2.1 radicals, reductive groups, derived group, centre, maximal tori, conjugacy of maximal split tori | `IsConnectedReductive`, derived subgroup representability, `GS.MaximalSplitTorusConjugacyStatement` | Rec (S02–S03); conjugacy P: `maximalSplitTorusConjugacy` |
| V.2.1 split component and its uniqueness | `GS.IsSplitComponent`; `GS.SplitComponentStatement` (existence, uniqueness up to isomorphism over `G`) | D; P: `splitComponentStatement` |
| V.2.1 topology independent of the embedding; `G` unimodular | `rationalPointTopology`; unimodularity is V.5.4 below | Rec (S04); D |
| V.2.2 `X^*(G)`, triviality on `𝒟G`, finite-rank lattice, duals | `GroupScheme.rationalCharacters`; `GS.RationalCharacterLatticeStatement` | D; P: `rationalCharacterLattice` |
| V.2.2 Remarks (tori): cocharacter pairing `χ(φ(t)) = t^{⟨χ,φ⟩}`, coordinate algebra `F[X^*(T)]`, anisotropic and split tori, maximal split and anisotropic subtori, almost direct product | `latticePairing`, `rationalCharacterEval_cocharacterPoints`; `IsSplitTorus` (isomorphic to `splitTorus S I`); largest split subtorus (`Rational.TorusSplitPart`); `GS.TorusAnisotropicPartStatement` ([statement](../../Langlands/GroupScheme/Rational/TorusAnisotropicPartStatement.md)) | Rec (S05). D for the listed constructions; P for the named pairing laws and largest split subtorus; S for the maximal anisotropic subtorus and finite surjective multiplication `A × T_an → T`, exact proof Task 6398 (`55194693-d01d-4220-9427-fa92990f27d6`) |
| V.2.3 (V.2.3.1) `H_G`, `⁰G`, `Λ(G)`, exact sequence; `⁰G = ⋂ ker |χ|_F` | `PL.rationalCharacterValuation`, `PL.rationalCommonNormKernel`, `PL.rationalCharacterValuationImage`, `PL.rationalNormKernelQuotientEquiv`; `rationalCharacterValuation_ker` | D; P |
| V.2.3 Lemma: `|χ|_F` smooth, kernel contains every compact subgroup | `isLocallyConstant_rationalNormCharacter`, `compactSubgroup_le_rationalCommonNormKernel`; generic `PL.CommonNormKernelTopologyStatement` | P (`commonNormKernelTopology`) |
| V.2.3 Proposition: `⁰G` open, closed, normal; compact subgroups and `𝒟G` in `⁰G` | `isOpen_rationalCommonNormKernel`, `isClosed_rationalCommonNormKernel`, instance `rationalCommonNormKernel_normal`, `derivedPoints_le_rationalCommonNormKernel` | P |
| V.2.3 Proposition: `⁰G` unimodular | `PL.RationalNormKernelUnimodularStatement` | S: Task 5711 (candidate `51acec26`) |
| V.2.3 Definition: unramified characters | `PL.unramifiedCharacters` of the rational norm characters: continuous characters trivial on `⁰G`, which are all characters trivial on `⁰G` since `⁰G` is open | D |
| V.2.4 `X(G) ≃ Hom(Λ(G), ℂ^×)`, `Λ(G)` free of finite rank, `ℂ[Λ(G)]`, `ev_g`, `χ_un`, (V.2.4.1)–(V.2.4.2) | `PL.rationalImageCharacters`, [RationalImageLattice](../../Langlands/Representation/Plancherel/RationalImageLattice.md), [RationalUnramifiedCharacterCoordinates](../../Langlands/Representation/Plancherel/RationalUnramifiedCharacterCoordinates.md), [RationalUnramifiedCoordinateAlgebra](../../Langlands/Representation/Plancherel/RationalUnramifiedCoordinateAlgebra.md) (evaluation algebra ≅ `ℂ[Λ(G)]` ≅ Laurent polynomials), `universalUnramifiedRepresentation` | D. The complex-torus structure is given by its coordinate algebra; no complex variety is constructed |
| V.2.5 tori: `C_A`, section of `H_A`, `Λ(A) = X_*(A)` | `GS.CocharacterUniformizer.SplitTorusUniformizerSectionStatement`, `RC.uniformizerSection` | P: `splitTorusUniformizerSection` |
| V.2.5 `⁰A` is the maximal compact subgroup of a split torus `A` | `PL.TorusNormKernelCompactnessStatement` (every torus) and `compactSubgroup_le_rationalCommonNormKernel` | P: `torusNormKernelCompactness` |
| V.2.5 `A₁ ⊂ A₂` split: `⁰A₁ = A₁ ∩ ⁰A₂`, `Λ(A₁) ⊂ Λ(A₂)`, `C_{A₁} ⊂ C_{A₂}` | `PL.RationalNormKernelRestrictionStatement`; `RC.uniformizerSection_naturality` | S: Task 5711; D |
| V.2.6 Lemma: `⁰A_G = ⁰G ∩ A_G` | `RC.SplitComponentKernelStatement` | S: Task 5679 |
| V.2.6 Lemma: `Λ(A_G) ↪ Λ(G)` with finite index | `RC.SplitComponentLatticeStatement`; `GS.CharacterRestrictionStatement` | P: `splitComponentLattice`, `characterRestriction` |
| V.2.6 Proposition: `G/⁰G A_G` finite; `⁰G ∩ Z(G)` compact | `PL.finite_rationalCentralQuotient` with `splitComponentLattice`; `PL.isCompact_rationalCommonNormKernel_inf_center` | P |
| V.2.6 Proposition: `Z(G)` compact implies `⁰G = G` | `PL.RationalNormKernelCompactCenterStatement` | S: Task 5711 |
| V.2.7 action of `X(G)` on `Irr(G)`, stabilizers | [RationalInertia](../../Langlands/Representation/CuspidalSupport/RationalInertia.md) | D |
| V.2.7 Lemma: `X(G)(π)` finite | `Langlands.CuspidalSupport.RationalTwistStabilizerFiniteStatement` | P: `rationalTwistStabilizerFinite` |
| V.2.7 Corollary and Notations: inertia orbits are complex tori; polynomial and rational functions on `D` | `Langlands.CuspidalSupport.RationalInertiaOrbitTorusStatement` | S: task `f5aebf51` |

The anisotropic-part entry corrects the previous ledger's claim that the assertion
was unstated. At Library `430cc03fe803c5dbf74bc3baf91e8f7a2c26ea9c`, the public
`TorusAnisotropicPartStatement` pair agrees with this workspace. It quantifies over
every field and actual torus, asserts a closed anisotropic subtorus through which
every closed anisotropic subtorus factors, and asserts finite surjective
multiplication with every largest split subtorus. This expresses uniqueness up to
isomorphism over the ambient torus and the scheme-level almost direct product.
Check `4a9eab52-4b7d-4d1e-a3a7-edd2383e4719` compiled and inspected the existing
declaration as `Prop` with zero errors and warnings. No proof was found in the
public Lean files or focused task records; Task 6398 supplies its exact proof
obligation. The source was reread at V.2.2 Remark 2 and V.2.5, printed pp.105, 107 /
PDF pp.111, 113. Compilation of the statement supplies no proof evidence.

## V.3 Parabolic subgroups (109–117 / 115–123)

The section refers to [7] (Borel–Tits) or [42] (Springer) for its recalled assertions.

| Item | Lean | Status |
| --- | --- | --- |
| V.3 opening: parabolic subgroups, rational radicals | `IsParabolicSubgroup` | D; Rec |
| V.3.1 Levi decomposition `P = M ⋉ N`; `N` acts simply transitively on the Levi factors | `GS.ParabolicRadicalTorusLeviStatement` and `GS.ParabolicRadicalTorusCentralizerLeviStatement` (a Levi factor is the centralizer of a maximal torus of the radical of `P`), `GS.RationalLeviConjugacyStatement` (two rational Levis are conjugate by a unique rational point of the unipotent radical), `GS.ParabolicRootPresentationExistenceStatement` | P (each has its proof) |
| V.3.1 `M = Z(G, A)` for a split component `A` of `P`, `A = A_M`; Levi subgroups are the centralizers of split tori `A` with `A = A_M` | `GS.LeviSplitComponentCentralizerStatement` states `Z_G(A_M) = M` as subgroup functors for every rational Levi of a rational parabolic. Related: `GS.DynamicLeviCocharacterRealizationStatement`, `GS.MinimalParabolicLeviCentralizerStatement`. The full relation with the split component of `P` is Worker 4's separate parabolic split-component unit | Rec (S08); S for the arbitrary-Levi split-component centralizer; P for the related statements; see the V.3.5 row |
| V.3.1 opposite parabolic: the unique `Q ∈ P(M)` with `P ∩ Q = M` | `GS.OppositeDynamicParabolicUniquenessStatement` | P |
| V.3.1 `P(M)` is finite | `GS.LeviParabolicFiniteStatement`, in [LeviSplitComponentRecallStatements](../../Langlands/GroupScheme/Rational/LeviSplitComponentRecallStatements.md): a uniform bound on finite families with distinct parabolic images and the same embedded rational Levi | Rec (S07); S. `GS.MaximalLeviParabolicCountStatement` covers maximal `M` (at most two) |
| V.3.2 minimal parabolics; conjugacy of maximal split tori and of minimal parabolics | `GS.MinimalParabolicLeviCentralizerStatement`, `GS.MaximalSplitTorusConjugacyStatement`, `GS.MinimalParabolicConjugacyStatement` | P |
| V.3.3 `𝔞`, `𝔞^*` | `RealTorusSpace.Vstar` | D |
| V.3.4 `Σ'(A)`, `Σ(A)`, `Σ'(P)`, `Σ(P)` | `relativeRoots`, `RelativeRoot.indivisibleRoots`, `positiveRelativeRoots`, `reducedPositiveRelativeRoots`, `RelativeRoot.subgroupRelativeRoots`; `GS.RenardRootConventionStatement` | D; P: `renardRootConvention` |
| V.3.5 `W(A) = N_G(A)/Z_G(A) = N_G(M)/M`, acting faithfully | `relativeWeylGroup` (minimal case); `RP.LeviNormalizerWeylGroupStatements` (`N_G(M)/M` finite, faithful through the norms on the centre); `GS.LeviSplitComponentCentralizerStatement` and `GS.LeviSplitComponentNormalizerStatement` | D; P: `leviNormalizerWeylGroupStatements`; S for `Z_G(A_M) = M` as subgroup functors and `N_G(A_M) = N_G(M)` on rational points for arbitrary rational Levis. The normalizer equality is not asserted as equality of subgroup schemes; see the public pair's Weil-restriction counterexample to that stronger assertion |
| V.3.6 `𝔞^*_M = 𝔞^*_G ⊕ (𝔞^G_M)^*` and `𝔞_M = 𝔞_G ⊕ 𝔞^G_M`, for the minimal Levi `M_∅` (a maximal split torus `T`) | `GS.RelativeCentralDirectionsStatement` (conjunction of `RelativeCharacterRootComplementStatement` and `RelativeSplitCentralDirectionsStatement`): the root span and the restricted characters of `G` are complementary in `X^*(T) ⊗ ℝ`, and the split component of `G` embeds with image the common root annihilator | P (both conjuncts) |
| V.3.6 the same decompositions for an arbitrary Levi `M` | `GS.RenardLeviCentralDecompositionStatement` ([statement and scope](../../Langlands/GroupScheme/Rational/RenardLeviCentralDecompositionStatement.md)): over every field, for connected reductive `G`, `M` and actual split components with the compatible morphism diagram, both real restriction bijections, the canonical central-character inclusion, its complement with the literal restriction kernel, and the dual cocharacter complement with the pairing annihilator; both product equivalences have the specified addition formulas | S: published candidate `92aa130e-c278-47d0-8647-615541ba61c5`; exact proof Task 6224 (`423ad442-9268-4104-a37f-3f1d8eb63388`). Realizing the compatible component diagram for every source Levi is separate |
| V.3.7 `Σ(A_∅)` is a root system and `W` its Weyl group | `GS.RelativeRootSystemStatement` (a Mathlib root system on the rational span of the relative roots, Weyl group = the image of `W`), `GS.RelativeWeylCoxeterStatement`, `GS.RelativeTitsSystemStatement`; `GS.RelativeRealCorootStatement` adds existence of invariant scalar products on the actual real character and cocharacter spaces and real root-system realizations | P for the rational system and Weyl identification; S for the real statement, exact proof task `09d6ceb8-fc92-458a-b568-273bd5b8a48b` |
| V.3.7 coroots `α̌ ∈ 𝔞_M`, the coroot system `Σ^∨(A_M)` in `𝔞_M`, and the spans `(𝔞^G_M)^*`, `𝔞^G_M` | `GS.RelativeRealCorootStatement`: the real image of each integral coroot from `RelativeRootReflectionData`, independence from those data, the formula and uniqueness for every invariant scalar product, the coroot span as the annihilator of restricted group characters, and crystallographic real root pairings for all roots and for the indivisible roots; minimal Levi only | S: exact proof task `09d6ceb8-fc92-458a-b568-273bd5b8a48b`. For the projected generators for non-minimal standard Levis, see its V.3.13 component below |
| V.3.8 standard and semistandard parabolics; unique Levi factor containing `A_∅` | `GS.standardParabolic`, `GS.standardLevi`; `GS.StandardParabolicEndpointsStatement`, `GS.StandardLeviSplitComponentStatement` | D; P |
| V.3.9 every parabolic is conjugate to a standard one | `GS.StandardParabolicClassificationStatement` | P |
| V.3.10 semistandard intersections | `GS.DynamicSemistandardIntersectionStatement`, `GS.RepresentedParabolicLeviIntersectionStatement`, `GS.StandardLeviIntersectionStatement` | P |
| V.3.11 parabolics of `M` and parabolics of `G` contained in `P` | `GS.DynamicLeviParabolicCorrespondenceStatement`, `GS.DynamicNestedParabolicDecompositionStatement` | P |
| V.3.12 the simple roots form a basis of the root span; rank identities | `GS.RelativeRankStatement` (conjunction of `RelativeSimpleRootBasisStatement`: the simple relative roots form a basis of the rational span `relativeRootSpan` of the relative roots, and `RelativeRankIdentityStatement`: the rank identities and the rational character restriction) | P (both conjuncts) |
| V.3.12 the real form: `Δ_∅` is a basis of `(𝔞^G_∅)^*`, the kernel of restriction to `A_G` | `GS.RelativeSplitCentralDirectionsStatement` gives, for every split component `a : A_G → G`, an embedding `f : A_G → T` with `(rationalCharacterRestrictReal f).ker = relativeRootSpanReal i` (and the rational analogue). `GS.RelativeCharacterRootComplementStatement` gives the real complement. `GS.RelativeRealSimpleRootBasisStatement` states a real basis of `relativeRootSpanReal i` indexed by the actual simple roots, vector by vector `α ↦ 1 ⊗ α` | P (kernel identification and complement); S for the real basis, exact proof task `58a10059-5876-401d-930a-684c14d11445` |
| V.3.12 `Δ_∅^∨` is a basis of `𝔞^G_∅`; fundamental weights and coweights | `GS.RelativeFundamentalWeightStatement`: the actual simple real coroot basis, bases dual to the simple coroots and simple roots, and uniqueness of each fundamental weight and coweight in its specified relative subspace | S: exact proof task `6642885b-1a93-4f8c-8fdf-ebfc7c70b54a` |
| V.3.13 `𝔞_G ⊂ 𝔞_L ⊂ 𝔞_M ⊂ 𝔞_∅`, with `𝔞_M` the annihilator of `Δ^M_∅` | `GS.StandardLeviCentralDirectionsStatement`: for every standard Levi, the split component embeds into `A_∅` with real cocharacter image the annihilator of the selected simple roots, with the ranks | P (`standardLeviCentralDirections`) |
| V.3.13 `𝔞^*_∅ = 𝔞^*_G ⊕ (𝔞^G_∅)^*`, with `(𝔞^G_∅)^*` the span of `Δ_∅` | the real part of `GS.RelativeCharacterRootComplementStatement` (the real root span and the restricted characters of `G` are complementary) | P |
| V.3.13 `𝔞^*_M` as the annihilator of the coroots of `M`; `𝔞_∅ = 𝔞_G ⊕ 𝔞^G_∅` with `𝔞^G_∅` the coroot span; `𝔞^*_M = 𝔞^*_L ⊕ (𝔞^L_M)^*` and its dual; orthogonality; projections `p^L_M` | `GS.StandardLeviRealDecompositionStatement`: for `J ⊆ K ⊆ Δ_∅`, root and coroot annihilator models, their perfect restricted pairing, the direct sums and projected spanning sets, and orthogonality for every invariant scalar product. The relative character space is the intersection of the coroot annihilator of `J` with the span of `K`, correcting I4; dually for cocharacters. The direct sums determine the projections | S: exact proof task `ff6de4a1-1e68-4560-9e61-a69bc0ec5d4b`. Proofs and the actual split-component character-space comparison remain separate; no named `p^L_M` map is added by this statement. The printed unprojected span remains false (I4) |
| V.3.14 `Δ(P)`, `Δ̂(P)`, `Δ^∨(P)`, `β̌` | [RestrictedSimpleRootCones](../../Langlands/GroupScheme/Rational/RestrictedSimpleRootCones.md) (`restrictedSimpleRoots`), `GS.ParabolicRootPresentation` | D. `Δ̂(P)`, `Δ^∨(P)` and `β̌` are not constructed |
| V.3.15 cones `+[𝔞^*]_P^G`, its closure, chambers `_P^G[𝔞^*]^+` and closure | `restrictedRootPositiveCone`, `restrictedRootNonnegCone`; `restrictedCorootChamber`, `restrictedClosedCorootChamber` ([LanglandsTriplet](../../Langlands/Representation/LanglandsClassification/LanglandsTriplet.md), defined by lifting to `𝔞^*_∅`) | D |
| V.3.16 cone decompositions and the cellular decomposition over `Q ⊇ P` | none | G (see V.3.18) |
| V.3.17 Lemma | `GS.CorootChamberUnipotentRootsStatement` | S: task `e341f206` |
| V.3.18 Langlands' combinatorial lemma | none | G, owned by Task 5474 (`9abd0e5e`, statement task, no executor yet). The Euclidean projection theorem of V.5.5 is stated and proved (`Langlands.Renard.ConeProjectionStatements`) |
| V.3.19 `𝔞^* = Hom_lisse(M, ℝ)`, `ln |χ| ∈ 𝔞^*` | `PL.RationalSmoothRealDescentStatement` (smooth, that is open-kernel, homomorphisms) | P: `rationalSmoothRealDescent`. A step of the source argument says "tout morphisme" but uses smoothness; without it the descent fails (`M = 𝔾_m` over `ℚ_p`), as the statement's [Markdown](../../Langlands/Representation/Plancherel/RationalSmoothRealDescentStatement.md) records |
| V.3.20 `𝔞^*_ℂ = Hom(Λ(M), ℂ) → X(M)` via `q^{-s}`: surjectivity, kernel `(2iπ/ln q)ℛ`, real part `ℜ(χ)` independent of the lift, unitary characters are those with `ℜ(χ) = 0` | `PL.RationalComplexParameterStatement` (on the actual valuation image `Λ(M)`), `RationalImageComplexExponential`, `RationalImageRealPart` | P: `rationalComplexParameter` |
| V.3.20 `𝔞^*_ℂ = Hom_ℤ(Λ(M), ℂ)` identified with `X^*(M) ⊗_ℤ ℂ` | `PL.RationalCharacterTensorParameterStatement`: the canonical map `ℂ ⊗_ℤ X^*(G) → Hom_ℤ(Λ(G), ℂ)`, `s ⊗ χ ↦ (a ↦ s a(χ))`, is bijective for every connected reductive `G` over a nonarchimedean local field, so for every Levi `M` (on the actual valuation image `Λ(G)`, with Mathlib's scalar-first tensor order) | P: `rationalCharacterTensorParameterBijective` |
| V.3.20 the surjection `X^*(M) ⊗ ℂ → X(M)` is `χ ⊗ s ↦ [g ↦ |χ(g)|_F^s]` | `PL.rationalCanonicalCharacterTensorExponential_tmul_val` ([RationalCharacterTensorParameter](../../Langlands/Representation/Plancherel/RationalCharacterTensorParameter.md)), on actual rational points, with the normalized absolute value | P (a theorem about the published construction) |
| V.3.20 the kernel `(2iπ/ln q)ℛ` is a lattice; `Im X(M)` is the image of `i𝔞^*` and a compact torus isomorphic to `i𝔞^*/(2iπ/ln q)ℛ` | `PL.RationalImaginaryParameterQuotientStatement`: the periods are discrete and closed (in `𝔞^*_ℂ` and in `i𝔞^*`), the quotient of `i𝔞^*` by them is compact, and the imaginary exponential is an open quotient map inducing a homeomorphism, with the prescribed values, onto the unitary characters of `Λ(M)` and onto the unitary unramified characters of `M(F)` | P: `rationalImaginaryParameterQuotient` (topological formulation; its Markdown keeps the algebraic and manifold assertions separate) |
| V.3.20 "on retrouve ainsi la structure de tore algébrique de `X(M)`"; `Im X(M)` is a real submanifold of the complex torus `X(M)` | Partial. The Library gives `X(M)` its coordinate algebra `ℂ[Λ(M)]` (V.2.4 above) and basis-dependent isomorphisms of topological groups `X(M) ≃ (ℂ^×)^r` and `Im X(M) ≃ (S¹)^r`, `r` the rank of `Λ(M)` (`PL.rationalCanonicalUnramifiedCharacterCoordinates`, `PL.rationalCanonicalUnitaryUnramifiedCharacterCoordinates`, definitions, in [RationalUnramifiedCharacterCoordinates](../../Langlands/Representation/Plancherel/RationalUnramifiedCharacterCoordinates.md)). It constructs no variety or manifold structure on `X(M)` itself, and no statement compares the exponential with the algebraic structure. The two published statement files of the previous rows list these assertions as separate obligations | D (coordinates); G (small) for the algebraic and submanifold assertions. See also remark R2 |
| V.3.21 `M^+`, `M^{++}` (inverse images under `H_M` of the chambers) and the full cones `A^+_M`, `A^{++}_M` (all `a ∈ A_M` with `|α(a)|_F ≤ 1`, resp. `< 1`, for `α ∈ Δ(P)`) | For the minimal Levi, `Langlands.BruhatTits.Cartan.dominantCentralizer` is `M_∅^+` on the actual centralizer points (see [RenardDominantValuation](../../Langlands/Representation/Plancherel/RenardDominantValuation.md)). The full `A`-cones appear only inline, as `CocharacterUniformizer.characterNorm` conditions on all points of `A(F)`, for example the hypotheses `characterNorm F S α x ≤ 1` for the simple roots in `StandardCasselmanUniformAsymptotics.lean`. There is no named definition of `M^+`, `M^{++}` for non-minimal `M` or of `A^+_M`, `A^{++}_M`. `CocharacterUniformizer.CAplus` and `CAstrict` are the lattice cuts `C_A^+ = C_A ∩ M^+` and `C_A^{++}` of V.3.23, not these full cones | D: minimal-Levi `M^+`; full cones inline only |
| V.3.21 (V.3.21.1) `A^+_M = ⊔_Q A^{++}_L` | none | Source issue I1 below |
| V.3.22 `A^+(ε)` (all `a ∈ A_M` with `|α(a)|_F < ε`) | Inline: the condition on every `t ∈ A(F)` in `RP.GeneralizedJacquetContractingRangeStatement` (GeneralizedJacquetRemarksStatements.lean, lines 134–149), and `standardCone` in `StandardCasselmanConstantTerm.lean` for standard parabolics. `CocharacterUniformizer.CAepsilon` is the lattice cut `C_A^+(ε) = C_A ∩ A^+(ε)` of V.3.23 | D (inline) |
| V.3.23 `C_A`, `F_M`, `C̃_A = C_A F_M`, `F_M ⊂ M^+`, `C_A^+`, `C_A^{++}`, `C_A^+(ε)` | `CocharacterUniformizer.CA`, `CAplus`, `CAstrict`, `CAepsilon`; `RC.FullLatticeRepresentativeStatement`, `RC.RenardDominantComparisonStatement`, `RC.IsChamberCompatibleTransversal` | D; S: Task 5679 (representatives); P: `renardDominantComparison` |
| V.3.24 the nonnegative integral model and quotient by the common annihilator | `GS.CocharacterCone.nonnegative`, `quotient`, `mkQ_mem_quotient_iff`, `latticeSection_mem_CAplus_iff` ([construction](../../Langlands/GroupScheme/Rational/CocharacterCone.md)) | D/P for the construction and intrinsic laws; published candidate `6d296d7f-cdc6-4d8a-bbb7-580fab06a4b9` |
| V.3.24 the integral kernel of the split-central quotient | `GS.SimpleRootSplitCentralImageStatement`: for every supplied compatible `f : A_G → A_∅`, the simple-root integral annihilator equals the integral cocharacter image of `f` | S: candidate `dc66d64a-3cac-4f23-868b-62c6c8270f89`; exact proof Task 6390 (`ded1c8b7-84b7-4c10-a243-eb0395d509d7`) |
| V.3.24 the common-uniformizer group quotient and its representative map | `GS.CocharacterUniformizer.QuotientComparisonStatement`: for split `T` and every commutative `A` and `f : A → T`, the integral quotient by `range(cocharacterMapInt f)` is multiplicatively equivalent to the image of `C_T` in `T(F)/f(C_A)`, by evaluation at the common uniformizer | S: candidate `ad918cde-8ea6-485b-a90b-88fdf44dc8c6`; exact proof Task 6391 (`ee278654-01f1-4cf6-a3f5-a11da91904f3`) |
| V.3.24 finite-generation replacement for the false `S ≅ ℕ^d` assertion | `GS.CocharacterConeFiniteGenerationStatement`: for every field, actual commutative group scheme `T` and finite set `R` of actual characters, `(CocharacterCone.quotient T R).FG` | S: published candidate `84ddf0c4-2efe-474c-87de-8461db6189e1`; exact proof Task 6429 (`7e019df7-e7ba-40e6-ac54-7fbd3d1b0dec`). No public proof or freeness assertion |
| V.3.24 actual nonnegative quotient `C^+_∅/C_{A_G}` | `GS.CocharacterUniformizer.CAplusMonoid`, `CAplusQuotient`, `mem_CAplusMonoid`, `mem_CAplusQuotient` ([construction](../../Langlands/Geometry/Building/CocharacterUniformizerCone.md)) | D/P for the construction and its representative laws; published candidate `e3a3c275-d6f7-4814-bc70-0a438466c38a` |
| V.3.24 comparison of the integral nonnegative quotient with that actual quotient | `GS.CocharacterUniformizer.ConeQuotientComparisonStatement`: a monoid equivalence prescribed by common-uniformizer evaluation on every nonnegative representative, for every supplied compatible split-component map | A: candidate `e577f809-f957-4f53-bbdd-fe5bf315fba8`, independently approved, not public at this update; no proof counted |
| V.3.24 strict faces of the integral quotient | `GS.CocharacterCone.strictFace`, `mkQ_mem_strictFace_iff`, `strictFace_subset_quotient`, `existsUnique_strictFace`, `iUnion_strictFace`, `strictFace_disjoint` ([construction](../../Langlands/GroupScheme/Rational/CocharacterConeFaces.md)) | D/P: published candidate `fd6d0153-2b3d-4684-8b3a-8fd00e1f3822`; these are integral faces, before comparison with actual Levi split components |
| V.3.24 strict uniformizer image of each actual standard Levi split component | `GS.CocharacterUniformizer.StandardLeviStrictImageStatement`: under every supplied compatible map, the strict section image equals the uniformizer image of `IsStandardCocharacter` | S: published candidate `55bbe167-ba81-42e2-8ce6-ac00610fdfc1`; exact proof Task 6472 (`f221e1b4-bd46-4391-9832-8df952b39f94`) |
| V.3.24 actual strict quotient pieces and `S = ⊔ S^{++}_L` | `GS.CocharacterUniformizer.standardLeviStrictQuotientFace` takes the quotient images over all actual compatible standard-Levi representatives | A for the piece definition: candidate `ccf31197-027a-486f-9b24-978b709baf46`, independently approved, not public at this update. The actual partition remains an obligation; source issue I2 prevents the printed free-monoid conclusion |
| V.3.25 `C_A/C_{A_G}(C_A ∩ ⁰G)` finite; `C^{++}_A ∩ ⁰G ≠ ∅` | not stated separately | St: step of VI.3.5 (`RPF.RationalCompactRestrictionCuspidalStatement`, proved) |

## Evidence for the focused V.3.6–V.3.13 update

Candidate `92aa130e-c278-47d0-8647-615541ba61c5` was independently approved by
Reviewer 1171 without qualifications and published at Library
`7f43c3c930ff92f76dae6589da1678ad729017e5`. Its exact Lean/Markdown pair agrees
with the current Library and this workspace. Recovery check
`152d5695-5c49-46e5-9551-acde4a9ba2ac` compiles the module and inspects
`Langlands.GroupScheme.RenardLeviCentralDecompositionStatement` as a
`Prop`-valued definition with universe parameter `u` and only standard axioms.
This is statement evidence. Task 6224 has no submitted proof as inspected on
13 November 2026.

Worker 4's candidate `89ad3e08-f0ca-4e7e-b9fb-5a257e4a4616` contains the
four component statements above and their conjunction
`Langlands.GroupScheme.RelativeRealCorootLinearAlgebraStatement` in module
`Langlands.GroupScheme.Rational.RelativeRealCorootStatements`. Reviewer 1315
independently approved it without qualifications. It is now public at Library
`0c3f30c24701c74d5474fca3fbb5324a99aa1d58`, integration
`dd40eb81b26d4460b63752e9161dcc49`. At the base used for this update its frozen,
public and workspace pairs agree exactly. The four exact proof-successor tasks
are listed in the rows above; their publication as tasks supplies no proof
acceptance. Worker 4 retains ownership of this linear-algebra unit.

Its statements are over arbitrary fields, on the shared actual torus spaces,
and universally quantify over supplied integral reflection data. Existence of
those data is a separate published statement; no new existence proof is
claimed here. The standard-Levi spaces are ambient root/coroot annihilators.
Their identification with the character and cocharacter spaces of actual split
components needs the existing standard-Levi comparisons and any remaining
comparison proof. Neither this candidate nor the compatible-diagram V.3.6
statement settles every geometric realization. The corrected projected-root
form of V.3.13 preserves source issue I4 below.

## Evidence for the focused V.3.24 update

The following three candidates are independently accepted and published at
Library `430cc03fe803c5dbf74bc3baf91e8f7a2c26ea9c`. Their frozen, public and
workspace Lean/Markdown pairs were compared byte for byte on 13 November 2026:

| Candidate | Public unit | Independent reviewer | Integration |
| --- | --- | --- | --- |
| `6d296d7f-cdc6-4d8a-bbb7-580fab06a4b9` | `Langlands.GroupScheme.Rational.CocharacterCone` | Reviewer 1452 | `cb4564b08521488b999d6e30590be06e` |
| `dc66d64a-3cac-4f23-868b-62c6c8270f89` | `Langlands.GroupScheme.SimpleRootSplitCentralImageStatement` | Reviewer 1487 | `164d5d383c0b49dcb2b9bb966ac39dda` |
| `ad918cde-8ea6-485b-a90b-88fdf44dc8c6` | `Langlands.GroupScheme.CocharacterUniformizer.QuotientComparisonStatement` | Reviewer 1521 | `92bfb6d3987a4709ac65ff67c1aec9a0` |

The cone uses actual integral cocharacters and actual character pairings. Its
quotient is the image in the integral lattice modulo the existing common
annihilator. Its intrinsic laws identify the invertible directions and
nonnegative representatives and compare their common-uniformizer evaluations
with the existing `CAplus`. It imposes no torus or reductivity assumption.

The central-image statement is over arbitrary fields, actual connected
reductive groups, a maximal split torus and a generic cocharacter. For every
actual split component and supplied compatible morphism into that torus it
states an integral equality of submodules. The uniformizer statement is over
nonarchimedean local fields with no characteristic restriction. Only its target
torus must be split; its commutative source and morphism are arbitrary. It
specifies the equivalence on every cocharacter representative. Both are derived
prerequisites motivated by V.2.5 and V.3.23–V.3.24, rather than literal statements
of the book.

Exact proof Tasks 6390 and 6391, respectively, have complete proof-only shared
drafts at revision 1. Recovery checks
`729710d5-8bc5-411c-9d98-7b18d65e36c3` and
`8ff97a1b-440a-4772-b14b-c586da42724d` compiled these drafts with zero errors
and warnings. The first uses simple-root generation, reductive root negation,
root-annihilator centrality and integral split-component factorization. The
second uses common-uniformizer naturality, injectivity of the split target
section, its exact quotient kernel and the first isomorphism theorem. These
private compilation results supply no independent proof acceptance.

Finite-generation statement candidate `84ddf0c4-2efe-474c-87de-8461db6189e1`
passed machine validation `56b81cb6-f4ca-4d43-b9dc-6565d7d43524`. Reviewer 1621
independently approved it without qualifications in review task
`e27bda22-25ae-41e3-961f-f02394a22182`. It is now published at
`85c2fe719cf62e96f22aaf4ca03961c5814d086b`, integration
`1e1aa3dbaa0a4c8aaaa045fe99db1307`. Its frozen, current Library and workspace
pairs agree exactly. The sole finiteness premise is finiteness of the selected actual
character set. No finite-generation hypothesis on the full cocharacter lattice
is added. The complete private proof evaluates into a finite product of
integers, identifies its nonnegative image with the casts of a subtractive
submonoid of a finite product of naturals, and applies Mathlib's
`AddSubmonoid.fg_of_subtractive`. Check
`af8c8573-398f-427b-a832-7016872e0be0` compiles that private proof and inspects
the statement as `Prop`, with zero errors and warnings. Exact proof Task 6429
has the complete proof-only shared draft at revision 1. It is ready with no
executor or submitted artifact as inspected for this update. The published
statement and unreviewed draft supply no accepted finite-generation proof.

Three further units are independently accepted and published at commit
`db8d6b3d466f2fd453a4df4624ce6c90db8eed46`, and their frozen pairs agree
with the current Library and workspace:

| Candidate | Public unit | Integration |
| --- | --- | --- |
| `e3a3c275-d6f7-4814-bc70-0a438466c38a` | `CocharacterUniformizerCone` | `c6310eb1e746456989e79a0f3fa4a65c` |
| `fd6d0153-2b3d-4684-8b3a-8fd00e1f3822` | `CocharacterConeFaces` | `aba2535876504065bc185d4fce49cdcc` |
| `55bbe167-ba81-42e2-8ce6-ac00610fdfc1` | `StandardLeviStrictUniformizerStatement` | `3e190bdd6ff6460f9c47d94e64a71c21` |

The first constructs the actual submonoid image in `T(F)/f(C_A)` for arbitrary
commutative group schemes and character sets, and identifies its representatives
with the existing `CAplus`. The second partitions the integral nonnegative
quotient by the existing standard-cocharacter predicate: standardness is
invariant under the exact common annihilator, and each class has a unique
vanishing-root index. Neither uses a reductivity, genericity or positive-rank
premise. The third states the strict image comparison for connected reductive
groups over all nonarchimedean local fields, with maximal split torus, generic
cocharacter, actual closed standard-Levi representative, split component and
every compatible map. It retains integral factorization and allows non-split
groups, nonreduced relative roots and rank zero.

Task 6472 has a complete proof-only shared draft at revision 1; it is ready
with no executor or submitted artifact as inspected for this update. Its
development compilation is not proof acceptance. The nonnegative comparison
candidate `e577f809-f957-4f53-bbdd-fe5bf315fba8` and actual strict-piece
definition candidate `ccf31197-027a-486f-9b24-978b709baf46` have successful
machine validation and independent approvals by Reviewers 1857 and 1873,
respectively, but remain unpublished. The comparison replaces rejected
`49565914-009b-4bf1-a02a-98bbf4877a9f`, whose construction dependency was then
unpublished. No result from either pending candidate is counted as public.

The source was reread at V.3.23–V.3.24, printed p.117 / PDF p.123. The correction
of the free-monoid assertion remains issue I2 below. Proofs of the integral and
nonnegative comparisons, finite generation after transport to the actual
quotient, and the strict-face decomposition over actual standard Levi split
components remain explicit obligations. Worker 4 retains the chamber,
parabolic split-component and closed-root-subset units. The nine
closed-root-subset proofs remain open obligations; this update counts no
published proof-successor tasks for them.

## V.4 Weyl groups (118–122 / 124–128)

| Item | Lean | Status |
| --- | --- | --- |
| V.4 opening: root subgroups `U_γ` | root-subgroup constructions under `Langlands.GroupScheme.Rational` | D |
| V.4.1 `W_G`, `S_∅`; Proposition ([7]): Tits system and Bruhat decomposition | `relativeWeylGroup`; `GS.RelativeTitsSystemStatement`, `GS.TitsStandardParabolicStatement` | P |
| V.4.2 closed, convex, symmetric and unipotent subsets; `G(T)`, `U(T)`; Proposition ([7] 3.22) | `GS.ClosedRootSubsetStatements` and its nine components ([statements and scope](../../Langlands/GroupScheme/Rational/ClosedRootSubsetStatements.md)); generated groups use closed minimality on all test schemes, with existence stated separately | Rec (S14); D for the notions and elementary laws, S for the nine targets: published candidate `cf347b48-66a3-4452-b3d4-0cbc3917dca8`. Intersection targets use reduced test schemes, and (ii) uses all relative roots; see I5 |
| V.4.2 Proposition ([7] 5.12–5.18): standard parabolics and subsets `Θ ⊂ Δ_∅` | `GS.StandardParabolicClassificationStatement`, `GS.StandardCocharacterStatement`, `GS.StandardParabolicPointsStatement`; new `GS.StandardParabolicRootTripleStatement` and `GS.StandardParabolicRootSubsetGroupStatement` give the generated root triples and their groups | P for the existing classification and points statements; S for the new root-triple and generated-group comparisons, in `ClosedRootSubsetStatements` |
| V.4.3 `W_M ↪ W_G`, `w·M`, `W(L, M)`, `W_M W(L,M) W_L = W(L,M)` | `standardRelativeWeylGroup`, [RelativeWeylConjugation](../../Langlands/Group/RelativeWeylConjugation.md), `GS.StandardLeviConjugationStatement` | D; P |
| V.4.3 (V.4.3.3) `W(M, M)/W_M ≃ W(A)` | `GS.StandardLeviNormalizerQuotientStatement`; finiteness consequence `RP.LeviNormalizerFiniteQuotientStatement` | S: Task 5688 (candidate `4d34998c`); P (finiteness) |
| V.4.4 `W(*, M)`, `W(M, *)`, `l(M)` | inline sets in `GS.StandardWeylElementaryChainStatement` and `GS.StandardMaximalLeviWeylStatement` | X/D (no named definition) |
| V.4.5 Lemma: `Q`-orbits on `P\G` and `W_M\W_G/W_L`; Bruhat order and a finer total order | `GS.StandardParabolicPointsStatement` (double-coset bijections, for standard `P` and `Q`); [RationalGeometricOrbitOrdering](../../Langlands/Representation/Aubert/General/RationalGeometricOrbitOrdering.md) | P for standard `P`, `Q`; D |
| V.4.5 Corollary: finitely many orbits for arbitrary `P`, `Q` | `GS.RepresentedParabolicDoubleCosetStatement` | P: `representedParabolicDoubleCoset` |
| V.4.6 Lemma | `GS.StandardWeylMinimalRepresentativesStatement` | S: Task 5649 |
| V.4.7 representatives `W^{Q,P}` for arbitrary `P`, `Q` | `RP.RepresentedGeometricLemmaGeometryStatement` | P: `representedGeometricLemmaGeometry` |
| V.4.8 maximal standard Levis and `Δ_∅ ∖ {α}`; `M` maximal iff `l(M) = 2`; `w·P = P̄′` | `GS.StandardMaximalLeviWeylStatement`; related `GS.MaximalLeviParabolicCountStatement`, `GS.MaximalLeviParabolicFamilyStatement`, `GS.MaximalLeviContainmentStatement` | S: Task 5688; P (related). See remark R1 |

Worker 4's closed-root-subset candidate
`cf347b48-66a3-4452-b3d4-0cbc3917dca8` was independently approved by
Reviewer 1683 and published at
`db8d6b3d466f2fd453a4df4624ce6c90db8eed46`, integration
`1b9ef7e8c26d404e8d16743bf3179597`. Its frozen, current Library and workspace
pairs match exactly. Its nine proposition targets remain unproved in this unit.
Their proofs remain open obligations; this update counts no published
proof-successor tasks for them. The arbitrary-field
statements distinguish the indivisible and possibly nonreduced ambient root
sets. They do not identify scheme-theoretic intersections on arbitrary test
schemes, and the symmetric-subset target gives integral reflections and their
preservation of the subset rather than constructing a Mathlib root-system
object. The separate proof obligations and source correction I5 are retained.

## V.5 Compact subgroups (122–129 / 128–135)

The section refers to [14] (Bruhat–Tits).

| Item | Lean | Status |
| --- | --- | --- |
| V.5.1 Theorem: `K_0` with (1)–(5) | `SC.IsCompactOpenMaximal`, `SC.SpecialCompactProperties`, `SC.SpecialLeviInheritance`, `RPF.FiniteCartanCovering`; predicates `SC.HasParabolicFactorization`, `SC.HasWeylRepresentatives` | S: tasks `5e9b97bd`, `8c39faa0`, `8d4643b8`, `7f9ba483`, `cdf027c8` |
| V.5.1 Corollary: `G/P` compact | `RP.ArbitraryParabolicQuotientCompactStatement` | P: `arbitraryParabolicQuotientCompact` |
| V.5.1 Corollary: every parabolic is `K_0`-conjugate to a standard one | `Langlands.BruhatTits.SpecialCompactParabolicConjugacyStatement` (hypothesis: property (1) of the Theorem) | R: candidate `3e44f4be` (before it, not stated, as [QuotientCompactProof](../../Langlands/BruhatTits/Parabolic/QuotientCompactProof.md) says) |
| V.5.2 Theorem ([24] 2.1) | `SC.AvailableSimultaneousStandardBasisStatement`; `RP.PresentationConeContractionStatement` | S: tasks `44b8e3a8`, `8d4643b8`; P: `presentationConeContraction` (the contraction parts on root presentations) |
| V.5.3 `H_0`, the two Lemmas, the Corollary, the finiteness Lemma in module form, the Theorem and the Remark | `Langlands.Hecke.IwahoriHeckeDecompositionStatement` | P: `Langlands.Hecke.iwahoriHeckeDecomposition`, exact proof from Task 5575 (`de85c579-484b-43a2-bba9-043299101602`), verified below. Renard writes that `A` is generated by the `a_z`, `z ∈ C_∅`; the statement uses the dominant generators `z ∈ C_∅^+`, which is what the second Lemma and all later uses concern (see the statement's [Markdown](../../Langlands/Representation/Hecke/IwahoriHeckeDecompositionStatement.md), "Formal choices") |
| V.5.3 finiteness Lemma for the generated subalgebra `M`: "L'algèbre `M` est un `A`-module de type fini" | none | G: not stated. The published statement states only the module form and keeps this assertion as an outstanding source obligation (its Markdown, "Not stated"): the generated subalgebra can be larger than the module span (`G_m` over `ℚ_3`, `K = 1 + 3ℤ_3`, `F_0 = {-1}`: the span is `Aε` and the algebra is `A ⊕ Aε`), and the source proof treats only products `a_{z₁} a_{z₂ f}` |
| V.5.4 Proposition: `G` unimodular | `RPF.RationalReductiveUnimodularityStatement` | P: `rationalReductiveUnimodularity` |
| V.5.4 Lemma: `δ_{P\G}(m) = δ_G(m)/δ_P(m) = δ_P(m)^{-1} = δ_N(m)^{-1} = δ_{N̄}(m)` on `M`, and the root-product formula on `A` | `RPF.RationalParabolicModulusStatement` (`G` unimodular and the modular character of a standard `P` is the Haar modulus of `N`), `RPF.RationalOppositeHaarReciprocityStatement` (the moduli of `N` and `N̄` are reciprocal), `RPF.DynamicUnipotentHaarDeterminantStatement` (Haar modulus = normalized absolute value of `det(Ad m | Lie N)`), `GS.DynamicAdjointDeterminantFormulaStatement` and `GS.Dynamic.AdjointDeterminantTorusRestrictionStatement` (that determinant as a product of roots with multiplicities) | C: derived from these proved statements for standard `P`; no single statement states the Lemma, and Renard's modulus orientation (inverse to Mathlib's `modularCharacter`) must be tracked as in the cited Markdown |
| V.5.5 Proposition (127 / 133): nearest point on the closure of an open cone `C` and its characterizations (i)–(iii); Corollary (128 / 134): the decomposition along a basis and its dual basis | `Langlands.Renard.ConeProjectionStatements`, in a corrected formulation: `C` is a nonempty convex open cone, and the equivalence with (iii) is asserted only for `C ≠ E` (for `C = E` the strict dual cone `Č` is empty and (iii) fails, although the projection is `v` itself). The Corollary has no extra hypothesis | P: `coneProjectionStatements` (Task 5418). See source issue I3 |
| V.5.5, display before the Corollary (128 / 134): for the cone of the Corollary, `Č = {∑ sᵢ αᵢ, sᵢ > 0}` | not stated (the statement's Markdown explains why) | Source issue I3: false as printed |
| V.5.5 end: proof of V.3.18 | none | G (with V.3.18) |

### Verified V.5.3 module-form proof

Worker 127's [proof and explanation](../../Langlands/Representation/Hecke/IwahoriHeckeDecompositionProof.md)
prove the unchanged seven-clause statement, including both left and right finite
generation of the specified module and both sandwich spanning formulas. Its
hypotheses retain the actual connected reductive group over a nonarchimedean
local field, available corrected building data, the special vertex, the compact
open subgroup normal in `K_0` with the supplied simultaneous standard-parabolic
basis properties, and an arbitrary finite lattice transversal. These structural
and topological premises are not discharged by the proof.

The finite-generation argument uses `IwahoriHeckeCore`: root-pairing floor
coordinates, finite tests for invariant subsets of a compact set, and Dickson's
lemma with finite labels. It uses neither the false free-monoid assertion of
V.3.24 nor a Gordan-lemma prerequisite. Commutation for the right-handed argument
is proved for the actual split-component images and centralizer representatives.
The source was rechecked at V.3.24 and V.5.3, printed pp.117, 123–125 / PDF
pp.123, 129–131. This alternate proof does not establish the generated-subalgebra
finiteness claim in the separate table row or correct the V.3.24 assertion.

Proof artifact `89acef8f-5eea-4013-8b16-98c6155a7ac4` is independently accepted
and public at commit `cc5aa77fa8dbdc6e723091c7b710ab0d81162c4e`.
Its `lean.proof@1` validation accepts the Lake build, exact target
`Langlands.Hecke.IwahoriHeckeDecompositionStatement`, unchanged statement and
frozen inputs. Reviewer 313 approved it without qualifications. At the Library
commit used for this update, the proof pair and both helper pairs
(`IwahoriHeckeCore`, `MassIndicatorProducts`) match their frozen accepted bytes.
This evidence supplies proof coverage for that exact conditional statement,
not whole-section or whole-book completion.

## Remarks and source issues

- **R1. V.4.8, `w · P = P̄′` (printed p.122 / PDF p.128).** The rendered page has the
  overline; text extraction loses it. Without it the assertion fails: in `GL_2` with `M` the
  diagonal torus and `w = s`, `s · B` is the lower triangular Borel subgroup. The candidate
  `4d34998c` states the version with the overline.
- **R2. V.3.20, the real part (printed p.116 / PDF p.122).** Renard first defines `ℜ(χ)` by
  lifting through the `q^{-s}` exponential, then writes `ℜ(χ) = ln |χ|`. Under the fixed
  positive valuation the two differ by the negative factor `−ln q`. The Library uses the
  first (normalized) convention throughout and records the discrepancy in
  [ArbitraryParabolicTempered](../../Langlands/Representation/Exponents/ArbitraryParabolicTempered.md)
  ("Parameter convention and retained source discrepancy") and in
  [LanglandsTriplet](../../Langlands/Representation/LanglandsClassification/LanglandsTriplet.md).
- **I1. (V.3.21.1) (printed p.116 / PDF p.122).** The book writes `A^+_M = ⊔_Q A^{++}_L` over
  the standard `Q = LU ⊇ P`, with `A^{++}_L ⊂ A_L`. As an equality of subsets of `A_M` it
  fails. In `GL_2` with `P = B`, `M` the diagonal torus and `u ∈ 𝔒_F^×`, `u ≠ 1`, the
  element `diag(1, u)` satisfies `|α(diag(1, u))|_F = 1`. It therefore lies in `A^+_M` but
  not in `A^{++}_M`, and it is not central, so it is not in `A_G`. The decomposition holds on
  the valuation side, for the chambers in `𝔞_M` (V.3.16), and for the lattice parts `C_A`.
  It also holds modulo `⁰A_M`. V.3.24 uses it in the lattice form
  `S = ⊔ C^{++}_{A_L}/C_{A_G}`.
- **I2. V.3.24 (printed p.117 / PDF p.123).** The claim `S = C^+_∅/C_{A_G} ≅ ℕ^d` with
  `d = |Δ_∅|` is false in general. The published
  [IwahoriHeckeDecompositionStatement](../../Langlands/Representation/Hecke/IwahoriHeckeDecompositionStatement.md)
  records this source issue (Reviewer 1385): for the diagonal torus of `SL_3`, `C^+_∅` in
  simple-root coordinates is `{(p, q) ∈ ℕ² | p ≡ q mod 3}`, and `(3,0) + (0,3) = 3·(1,1)`.

- **I3. V.5.5 (printed pp.127–128 / PDF pp.133–134).** Two points, recorded in the Markdown of
  the published
  [RenardConeProjectionStatements](../../Langlands/Analysis/RenardConeProjectionStatements.md).
  First, the Proposition's characterization (iii) needs `C ≠ E`: for `C = E` the strict dual
  cone `Č = {u | ∀ w ∈ C, 0 < ⟨u, w⟩}` is empty (take `w = 0`), so (iii) fails although
  `p_C(v) = v`. The Lean statement also makes explicit that `C` is nonempty and convex.
  Second, the display `Č = {∑ sᵢ αᵢ, sᵢ > 0}` before the Corollary is false as an equality
  of sets. The exact set is `{∑ sᵢ αᵢ | sᵢ ≥ 0, not all zero}`. For the standard basis of
  `ℝ²` and `C = (0, ∞)²`, the vector `(1, 0)` pairs strictly positively with every point of
  `C` but has a zero second coefficient. In positive dimension both sets have the same
  closure `{∑ sᵢ αᵢ | sᵢ ≥ 0}`, which is all the proof uses. In dimension zero `Č` and its
  closure are empty, and the Corollary holds directly. The display is not stated; the
  proved Corollary does not depend on it.

- **I4. V.3.13 (printed pp.112–113 / PDF pp.118–119).** The book defines `(𝔞^L_M)^*` as the
  subspace of `𝔞^*_∅` spanned by the `α ∈ Δ^L_∅ ∖ Δ^M_∅` and writes `𝔞^*_M = 𝔞^*_L ⊕ (𝔞^L_M)^*`,
  in particular `𝔞^*_M = 𝔞^*_G ⊕ (𝔞^G_M)^*`. With `𝔞^*_M ⊂ 𝔞^*_∅` the annihilator of the coroots
  of `M`, this fails: for `G = L = GL_3` and `M = GL_2 × GL_1` standard, `𝔞^*_M = {(x, x, y)}`,
  while `α_2 = (0, 1, −1)` pairs with `α̌_1 = (1, −1, 0)` to `−1`, so `α_2 ∉ 𝔞^*_M`. The
  decomposition holds with the roots projected to `𝔞^*_M` (equivalently restricted to `𝔞_M`), as in
  the definition of `Δ(P)` in V.3.14. Reviewer 2262 found this point.

- **I5. V.4.2 (printed p.118 / PDF p.124).** The published
  [closed-root-subset statement Markdown](../../Langlands/GroupScheme/Rational/ClosedRootSubsetStatements.md)
  records a counterexample to (ii) when closedness is read in Renard's
  indivisible root set. For a quasi-split unitary group in five variables with
  relative system `BC₂`, put `S = {e₁}` and
  `T = {e₁ − e₂, e₁ + e₂}`. Both are closed among the indivisible roots, and
  `T` is unipotent. The commutator of its two root groups gives a nontrivial
  subgroup of `U_{2e₁} ⊆ G(S)`, although `S ∩ T` is empty. Thus
  `G(S) ∩ U(T) = U(S ∩ T)` fails in that reading. The published target uses
  all relative roots, as in Borel–Tits 3.22 c); there `T` is not closed.
  The same example prevents the more general closed-subset intersection
  assertion with only convex intersection from being transferred to the
  indivisible ambient set. The convex version (i) has a separate target in
  that set. All three intersection targets concern reduced test schemes,
  consistent with the original variety statements; none asserts arbitrary
  scheme-theoretic intersection equality. This source correction is documented
  by the published statement unit, not proved as a Lean counterexample here.

## Genuine gaps of Chapter V

1. V.3.16 cone decompositions and V.3.18 Langlands' combinatorial lemma, with the
   constructions they need (fundamental weights and coweights, `Δ̂(P)`, `β̌`, the
   `W`-invariant inner product and the projections `p^L_M`). Task 5474 owns V.3.18.
2. V.3.6–V.3.13 linear algebra and its realization: the compatible-diagram
   decompositions for arbitrary Levis are now stated, with exact proof Task 6224
   (`423ad442-9268-4104-a37f-3f1d8eb63388`) open. The four real-coroot, real-basis,
   fundamental-weight and corrected standard-Levi statements in candidate
   `89ad3e08-f0ca-4e7e-b9fb-5a257e4a4616` are now public; the four focused
   proof tasks above retain the proof obligations. The geometric
   compatible-component realization and actual split-component/ambient-annihilator
   comparisons remain distinct obligations; their necessary published inputs do
   not alone establish every source-Levi instance.
3. V.5.1 Corollary: `K_0`-conjugacy of every parabolic to a standard one (now stated by the
   candidate `3e44f4be`, under review).
4. V.5.3, the finiteness Lemma for the generated subalgebra `M`. It is retained as an
   outstanding source obligation by the published `IwahoriHeckeDecompositionStatement`,
   which states the module form. The source proof covers only the module form.
5. V.3.20: the algebraic-torus structure of `X(M)` recovered through the exponential, and
   `Im X(M)` as a real submanifold of `X(M)`. The tensor identification, the pure-tensor
   formula and the compact imaginary quotient are proved (rows above).
6. Recalled assertions with remaining proofs: `P(M)` finite (V.3.1),
   `N_G(A_M) = N_G(M)` on rational points and `Z_G(A_M) = M` for arbitrary
   rational Levis (V.3.5) are stated in the public
   `LeviSplitComponentRecallStatements`; the maximal anisotropic subtorus and
   almost direct product (V.2.2 Remark 2) are stated in the public
   `TorusAnisotropicPartStatement`, with exact proof Task 6398. The general
   closed-subset assertions of V.4.2 are now stated by Worker 4's public
   `ClosedRootSubsetStatements`, with the ambient-root and reduced-test
   distinctions and source correction I5 above. Their nine proof targets
   remain open obligations.
7. V.3.24: the nonnegative comparison with the actual split-central
   uniformizer quotient, finite generation after its identification and the
   strict-face decomposition with actual standard Levi split components.
   The public integral and actual quotient constructions, integral strict-face
   laws, three public comparison statements and public finite-generation
   statement are partial progress. Tasks 6390, 6391, 6429 and 6472 retain the
   exact public proof targets. The nonnegative comparison and actual-piece
   definition remain approved candidates awaiting publication; no actual
   quotient partition has been published. None establishes freeness.

## Proof tasks of Worker 1222's Chapter V statements

`51acec26` (V.2.3, V.2.5, V.2.6: unimodularity of `⁰G`, `⁰A₁ = A₁ ∩ ⁰A₂`, compact centre) is
published; its proof task is Task 5711. `4d34998c` (V.4.3.3 and V.4.8) is published; its proof
task is Task 5688. Task 5679 is the proof task for the published `SplitComponentKernelStatement`
(V.2.6 Lemma) and `FullLatticeRepresentativeStatement` (V.3.23), which had none.

The compatible-component V.3.6 statement
`92aa130e-c278-47d0-8647-615541ba61c5` is published and has exact proof Task 6224
(`423ad442-9268-4104-a37f-3f1d8eb63388`). Its arbitrary-field scope, literal
restriction kernel and actual pairing annihilator are retained. The real-coroot unit now has
four focused proof-successor tasks, listed in its rows. For V.3.24, exact proof
Tasks 6390 and 6391 have complete unreviewed shared drafts at revision 1.
Task 6398 is the exact proof task for the already public anisotropic-part
statement. Task 6429 is the exact proof successor for the now-public
finite-generation statement; Task 6472 is the exact successor for the
now-public strict-image statement. Each has a complete unreviewed shared
proof-only draft at revision 1, with no proof artifact submitted as inspected
for this update. Neither draft supplies accepted proof coverage.
