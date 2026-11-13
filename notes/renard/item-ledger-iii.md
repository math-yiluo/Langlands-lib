# Renard 2026, Chapter III: item-by-item coverage ledger

Worker 1222, executor of the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`, revision 1. This note is the Chapter III part of
the item ledger that the task contract requires, in the format of the
[Chapter IV](item-ledger-iv.md), [Chapter V](item-ledger-v.md),
[Chapter VI](item-ledger-vi.md) and [Chapter VII](item-ledger-vii.md) ledgers. It lists the
headed items of Chapter III and the unheaded assertions found in its paragraphs, with
printed / PDF pages (PDF = printed + 6), Lean declarations and proof status at Library
commit `a54dda0d7c7c0fd4f76308fad8525ba13d9b4ce8`. The review state of Worker 1222's candidates
(**A** accepted, **R** under review) is as of 12 November 2026, Library
`ccc573af3771ecd25c84c65c2d366ae1333f156b`, where none of them is yet integrated. A published
statement is not a proof; every row keeps the proof status explicit.

Focused update, 13 November 2026: the III.1.6 compact-distribution/non-open
compact-subgroup Lemma and III.1.14 algebra Scholium now have independently
accepted, published exact proofs from Tasks 5961 and 5801. Their publication
receipts and entry pairs were checked against Library
`451cce4ca176c34856be86a36801b7a3b585ae77`. Those two rows, the evidence and
the gap summary below supersede the earlier statement-only snapshot; other
candidate statuses retain the 12 November audit date.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. Chapter III is printed
pp.57–85 / PDF pp.63–91.

## How the rows were checked

Worker 1222 read III.1 paragraph by paragraph in the text extraction and listed the Library
Markdown files that cite each subsection. For III.2 and III.3 the rows follow the published
source maps [iii2-hecke-induction](iii2-hecke-induction.md) (Task 5296) and
[iii3-sheaf-sections](iii3-sheaf-sections.md) (Task 5297), updated for later publications and
proofs. For each row the declarations named were read in their Lean file and Markdown.
Proof status comes from a scan of the Library for theorems whose type is exactly the
statement. A `Task` entry is a `lean.proof@1` task whose contract names the statement.

Abbreviations: `RS` is `Langlands.Renard.Smooth`, `HK` is `Langlands.Hecke`, `HH` is
`Langlands.Hecke.Homomorphism`, `I` is `Langlands.Induction`, `J` is `Langlands.Jacquet`,
`JL` is `Langlands.Jacquet.Localization`, `SR` is `Langlands.Sheaf.Renard`. Other names are
in `Langlands`.

Status codes, as in the other ledgers:

- **P**: proved; the named theorem has exactly the statement's type.
- **S**: statement published; a proof task is open.
- **D**: definition or construction (with the laws proved in its module, where stated).
- **C**: covered by published statements that are stronger or equivalent, or derived from
  them; the row says which.
- **St**: a step of the proof of a stated result.
- **X**: expository, convention or attribution.
- **Rec**: an assertion recalled from the literature.
- **A**: candidate accepted by review, waiting for integration.
- **R**: candidate staged, under review.
- **G**: genuine gap.

## III.1 Smooth representations (58–70 / 64–76)

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| III.1.1 representations, unitary representations, subrepresentations, quotients, subquotients, characters | 58 / 64 | Mathlib's `Representation`, `Subrepresentation` and quotients; `InvariantPositiveForm` and `IsUnitarizable` ([Unitary/Basic](../../Langlands/Representation/Unitary/Basic.md)) | D |
| III.1.1 Definition: smooth representations; the smooth part `V₀` | 58 / 64 | `IsSmooth`, `smoothVectors`, `smoothPart` | D |
| III.1.1 Remark: smooth iff every orbit map is continuous for the discrete topology on `V` | 58 / 64 | `SmoothDiscreteOrbitStatement` | P: `smoothDiscreteOrbit` |
| III.1.2 Proposition: `l` and `r` preserve `𝒞^∞_unif(G)` and `𝒟(G)` and are smooth there | 58–59 / 64–65 | `RS.RegularRepresentationSmoothStatement` | P: `regularRepresentationSmooth` |
| III.1.3 intertwining operators; the category `M(G)`; `Irr(G)` | 59 / 65 | `SmoothRep` and its morphisms | D |
| III.1.3 `M(G)` is abelian | 59 / 65 | the instance `SmoothRep.abelian` ([Category/Abelian](../../Langlands/Representation/Category/Abelian.md)) | P |
| III.1.3 the operators `π(T)` for `T ∈ H(G)`, `π(T₁ ∗ T₂) = π(T₁)π(T₂)`, and the Remark `π(f) = ∫ f(g) π(g) dμ_G(g)` | 59 / 65 | `HK.heckeAction`, the integrated action, and the module structure of [NondegenerateModuleFunctor](../../Langlands/Representation/Hecke/NondegenerateModuleFunctor.md) | D |
| III.1.3 the same for compactly supported distributions `T ∈ ℰ′(G)`, with `π(δ_g) = π(g)`, and the Example `l(T) f = T ∗ f` for `T ∈ ℰ′(G)` | 59 / 65 | Example for `T ∈ H(G)`: `RS.LeftRegularHeckeActionStatement`; for `ℰ′(G)`: `CompactDistributionActionStatement`, `LeftRegularCompactDistributionStatement` | P (`leftRegularHeckeAction`) for `H(G)`; R: candidate `614c7482` for `ℰ′(G)` |
| III.1.4 Theorem: `M(G) ≃ M(H(G))` | 59–60 / 65–66 | `HK.HeckeNondegenerateModuleEquivalenceStatement` | P: `heckeNondegenerateModuleEquivalence` |
| III.1.4 Remark: notation `T · v` | 60 / 66 | — | X |
| III.1.4 every smooth representation has an irreducible subquotient; finite type gives an irreducible quotient; finite length gives an irreducible subrepresentation | 60 / 66 | `SmoothRep.RenardIrreducibleExistenceStatement` | P: `renardIrreducibleExistence` |
| III.1.5 Proposition (i)–(iv) and Theorem (i)–(iii): `K`-fixed vectors and `H(G, K)`-modules | 60–61 / 66–67 | `HK.FixedVectorCornerStatements` (five statements) | P: `fixedVectorCorner` and the five component proofs |
| III.1.6 the dual action `π*`, the contragredient `(π̃, Ṽ)` | 61 / 67 | `Representation.dual`, `smoothContragredient`, `SmoothDual`, `smoothDualPairing` | D |
| III.1.6 under III.1.4 the contragredient corresponds to the I.4.1 dual module, with right and left modules identified through `T ↦ Ť` | 61 / 67 | `HK.ContragredientHeckeDualStatement` (for every t.d. group, with the weighted inversion `haarInversion`) | A: candidate `a5167755` |
| III.1.6 Lemma: `(π̃(Ť) λ)(v) = λ(π(T) v)` for `T ∈ ℰ′(G)`; the case `e_K` for compact `K`; `(V*)^K ≃ (V^K)*`; `Ṽ^K = (V*)^K ≃ (V^K)*` for compact open `K` | 61 / 67 | `ContragredientDistributionLemmaStatement` in [CompactDistributionTransposeStatements](../../Langlands/Representation/Smooth/Contragredient/CompactDistributionTransposeStatements.md): transpose for actions characterized by scalar pairings, compact-subgroup Haar formulas and bijectivity of restriction `(V*)^K → (V^K)*`, with no openness assumption on compact `K` | P: `contragredientDistributionLemma` in [CompactDistributionTransposeProof](../../Langlands/Representation/Smooth/Contragredient/CompactDistributionTransposeProof.md), Task 5961, with independent group/carrier universes. The first two clauses use supplied distribution actions satisfying the scalar-pairing characterization; the full-dual restriction bijection has no action premise. No admissibility or finite-dimensionality hypothesis. P (`smoothDualCompactFixedDuality`) for compact open `K`. Existence of the full distribution action remains the separate III.1.3 obligation |
| III.1.6 Corollary: canonical injection `V ↪ Ṽ̃` | 62 / 68 | `SmoothAdmissibleDualityStatement`, first clause (under compact-open cofinality, which holds for t.d. groups) | P: `smoothAdmissibleDuality` |
| III.1.7 Definition: admissible representations | 62 / 68 | `IsAdmissible` (all open subgroups, as in the source) | D |
| III.1.7 compact open subgroups suffice; `V` admissible iff the `H(G)`-module is admissible in the sense of I.5.1 | 62 / 68 | `HK.AdmissibleIffHeckeAdmissibleStatement` | A: candidate `ce923198` |
| III.1.7 Proposition: admissible iff `V ≃ Ṽ̃` | 62 / 68 | `RS.AdmissibleBidualStatement` | P: `admissibleBidual` |
| III.1.7 the I.5.1 Corollary for representations: `Ṽ` admissible; `V` irreducible iff `Ṽ` irreducible | 62 / 68 | `SmoothAdmissibleDualityStatement` (second clause); `isIrreducible_smoothContragredient_iff_of_bidual` with bidual bijectivity | P |
| III.1.8 Proposition: Schur's lemma for `G` countable at infinity | 62 / 68 | `RS.SigmaCompactSchurStatement` | P: `sigmaCompactSchur` |
| III.1.8 Remark: for admissible `π` a countable basis at `1` suffices | 62 / 68 | `AdmissibleSchurStatement` (admissible, no countability) | P (`admissibleSchur`); covers the Remark |
| III.1.9 Proposition: invariant pairings `V × Ṽ → ℂ` are multiples of the canonical one | 63 / 69 | `RS.InvariantContragredientPairingStatement` | P: `invariantContragredientPairing` |
| III.1.10 central characters; the Lemma; the Remark on `ℨ(G)` | 63–64 / 69–70 | `RS.CentralCharacterStatement` | P: `centralCharacter` |
| III.1.10 Proposition: `V = ⊕_χ V_χ` for `Z ⊂ Z(G)`, `V` admissible or of finite length; finitely many `V_χ ≠ 0` for finite length | 64 / 70 | admissible `V`, `Z = Z(G)`: `CentralCharacterDecompositionStatement` (its decomposition clause assumes `IsCenterFinite`, proved for admissible `V`). A subgroup `Z ⊂ Z(G)` is obtained by grouping the characters of `Z(G)` by restriction | P (`centralCharacterDecomposition`) for admissible `V`, C for `Z ⊂ Z(G)`; finite length: `FiniteLengthCharacteristicDecompositionStatement`, A: candidate `532e02d1` (it would also follow from the published statement once finite length is shown to imply `IsCenterFinite`, which is not stated) |
| III.1.11 Theorem: for `T ≠ 0` some irreducible `π` has `π(T) ≠ 0` | 64–65 / 70–71 | `RS.HeckeCompletenessStatement` | P: `heckeCompleteness` |
| III.1.11 Remark: `H(G)` satisfies (Sep) of I.1.8 | 65 / 71 | the Theorem, through III.1.4 | C. The suggestion to determine `ℨ(G)` through (I.1.8.1) is X |
| III.1.12 the character `Tr π = Θ_π` of an admissible representation | 65 / 71 | `Character.distribution` ([Character/Basic](../../Langlands/Representation/Character/Basic.md)) | D |
| III.1.12 Lemma: `Int(g₀) · Tr π = δ_G(g₀) Tr π` | 65 / 71 | `CharacterAutomorphismStatement`, for automorphisms preserving the Haar measure. Inner automorphisms preserve it when `G` is unimodular | P (`characterTransport`) for unimodular `G`; general `G`: `CharacterConjugationModularStatement`, R: candidate `71f85af7` |
| III.1.12 Example: `Θ_π̃(f) = Θ_π(f̌ δ_G⁻¹)` | 65 / 71 | `CharacterSmoothDualStatement`, for an inversion-invariant measure | P (`characterTransport`) for unimodular `G`; general `G`: `CharacterContragredientModularStatement`, R: candidate `71f85af7` |
| III.1.13 Proposition: characters of inequivalent irreducible admissibles are linearly independent | 65–66 / 71–72 | `Character.FiniteFamilyLinearIndependenceStatement` | P: `finiteFamilyLinearIndependence` |
| III.1.13 Corollary: equal characters iff equivalent | 66 / 72 | `CharacterSeparationStatement` | P: `characterSeparation` |
| III.1.14 `⊠_i π_i` and the diagonal `⊗_i π_i` | 66 / 72 | `Representation.tprod` with the projections; `RS.TensorProductSmoothStatement` (smoothness of the diagonal tensor) | D; P (`tensorProductSmooth`) |
| III.1.14 Proposition: `⊠` of admissibles is admissible, irreducible if the factors are; every irreducible admissible of `∏ G_i` is such a product, uniquely | 66 / 72 | `FlathTwoFactorStatement` (two factors, as in the source's proof) | S: Task 5771 |
| III.1.14 Proposition, second assertion: `(⊠_i π_i)^∼ = ⊠_i π̃_i` | 66 / 72 | `AdmissibleExternalTensorContragredientStatement` (two factors) | A: candidate `b47b8223` |
| III.1.14 Scholium (cited from [16]): for unital algebras `A₁`, `A₂` and finite-dimensional irreducible representations `τ₁`, `τ₂`, the representation `τ₁ ⊠ τ₂` on `V₁ ⊗ V₂` is irreducible; conversely every finite-dimensional irreducible representation is of this form, uniquely up to isomorphism | 66–67 / 72–73 | `AlgebraTensorScholiumStatement` in [AlgebraTensorSimpleModuleStatements](../../Langlands/Algebra/AlgebraTensorSimpleModuleStatements.md): external simplicity, existence of factors and uniqueness, over `A₁ ⊗[ℂ] A₂` (source issue S2) | P: `algebraTensorScholium` in [AlgebraTensorSimpleModuleProof](../../Langlands/Algebra/AlgebraTensorSimpleModuleProof.md), Task 5801, with all seven universe parameters independent. This proves the finite-dimensional unital complex algebra-module Scholium; the smooth group-representation Proposition and its contragredient assertion remain separate rows |
| III.1.14 Lemma: `πω` admissible for admissible `π` and a smooth character `ω` | 67 / 73 | `isAdmissible_twist_iff` ([Twist/AdmissibilityProof](../../Langlands/Representation/Twist/AdmissibilityProof.md)) | P |
| III.1.15 the functors `• ⊗ V`, `Hom(W, •)₀`, `Hom(•, V)₀` | 67 / 73 | the smooth tensor and smooth Hom objects of [RenardTensorHomStatements](../../Langlands/Representation/Smooth/RenardTensorHomStatements.md) | D |
| III.1.15 Example: `Hom(•, ℂ)₀` is the contragredient | 67 / 73 | `smoothContragredient` is by definition the smooth part of the dual action, which is `π_ρ` for trivial `π` | C (definitional; no separate comparison declaration) |
| III.1.15 Proposition, Lemma and Corollary: `Hom(V₁ ⊗ V₂, V₃)₀ ≃ Hom(V₁, Hom(V₂, V₃)₀)₀` | 67–68 / 73–74 | `RS.TensorHomAdjunctionStatement` | P: `tensorHomAdjunction` |
| III.1.15 Remarks 1–2: the adjunction `• ⊗ V₂ ⊣ Hom(V₂, •)₀`; preservation of colimits and limits | 68 / 74 | the Corollary read as an adjunction; preservation is a formal consequence (the statement's Markdown says so) | C |
| III.1.15 Remark 3: twisting by a character is an equivalence and adjoint on both sides | 68 / 74 | `RS.TwistEquivalenceStatement` | P: `twistEquivalence` |
| III.1.15 `(V₁ ⊗ V₂)_G ≃ V₁ ⊗_{H(G)} V₂` (right module through `T ↦ Ť`) and (III.1.15.1) | 69 / 75 | `RS.CheckRightActionExistsStatement`, `RS.CoinvariantHeckeTensorStatement`, `RS.HeckeTensorAssociativityStatement` | P: `checkRightActionExists`, `coinvariantHeckeTensor`, `heckeTensorAssociativity` |
| III.1.15 Theorem (i)–(iii): exactness of the three functors, preservation of projectives and injectives | 69–70 / 75–76 | `RS.TensorHomExactnessStatement` | P: `tensorHomExactness`. Source issue S1 (a typo in the proof) |
| III.1.15 proof: `M(K)` is semisimple for compact `K` | 70 / 76 | IV.1.1 Corollary, `CompactGroupIsotypicDecompositionStatement` (see the Chapter IV ledger) | St; P |

## III.2 Induction and restriction (70–83 / 76–89)

Rows follow the published [III.2 map](iii2-hecke-induction.md); "map" below refers to it.

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| III.2.1 pullback along `φ : H → G`; the bimodule structure of `H(G)`; the functors `F`, pseudo-`F`, `I`, `P` | 70–71 / 76–77 | `HH.restriction`, `HH.leftModule`, `HH.rightModule`, `HH.bimodule`, `HH.F`, `HH.pseudoF`, `HH.I`, `HH.P` and their smooth transports | D |
| III.2.1 `Fφ ≅ F`, `F ⊣ I`, `P ⊣ pseudo-F` | 70–71 / 76–77 | `HH.ContinuousHomomorphismStatements` | P: `continuousHomomorphismStatements` |
| III.2.1 Example: transport by an isomorphism; `π^g(ghg⁻¹) = π(h)` (III.2.1.2) | 71 / 77 | `HH.restriction` along an isomorphism; the conjugation adapters below take `τ ∘ e = σ` as data | C |
| III.2.2 Definition: `Ind_H^G` and `ind_H^G` | 71 / 77 | `I.SmoothFunctions`, `I.smoothInduced`, `I.CompactFunctions`, `I.compactInduced` | D |
| III.2.2 Lemma: fixed vectors as functions on a double-coset transversal `Ω` | 71–72 / 77–78 | finite `Ω`: `I.fixedEvaluationEquiv`; compact induction with the representatives `q.out`: `I.compactFixedEvaluationEquiv`; arbitrary `Ω`: `I.InducedFixedVectorTransversalStatement` | D (proved constructions) for the special cases; A: candidate `576e9e04` for the Lemma |
| III.2.2 Proposition: functoriality and exactness of both inductions | 72 / 78 | `I.smoothInductionFunctor`, `I.compactInductionFunctor`; exactness `I.InductionExactnessClause` in `I.StructuralStatement`; surjectivity halves `I.smoothInductionSurjectivity`, `I.compactInductionSurjectivity` | D; S: Task 5753 (the surjectivity halves are proved) |
| III.2.3 Lemma: compact `H\G` gives `Ind = ind` and preserves admissibility | 72 / 78 | `I.CompactQuotientClause` | P: `compactQuotientClause_holds` |
| III.2.4 Lemma: conjugation by a normalizing element, smooth induction | 73 / 79 | `I.conjugateSmoothInducedEquiv` with its evaluation formula | D (proved construction) |
| III.2.4 Lemma: the same for compact induction | 73 / 79 | `I.CompactConjugateInducedStatement` | A: candidate `576e9e04` |
| III.2.5 Theorem: Frobenius reciprocity `Ind ⊣`-right of `Res` | 73–74 / 79–80 | `I.SmoothFrobeniusClause` in `I.StructuralStatement`; the Hecke transport `HH.SmoothInductionAdjunctionStatement` (proved) | S: Task 5753 |
| III.2.5 Remark, (III.2.5.1)–(III.2.5.5): explicit identification of `Ind` with the Hecke Hom induction | 74–75 / 80–81 | `HH.ClosedInductionHomStatement` | S: Task 5402 (a proof candidate is under verification) |
| III.2.6 the right module formula (III.2.6.1), the tensor model, (III.2.6.2) and the Theorem `P(W) ≅ ind(W ⊗ δ_{H\G})` | 75–76 / 81–82 | `HH.CompactInductionHeckeStatement` | P: `compactInductionHeckeStatement_proof` |
| III.2.6 proof models (III.2.6.3)–(III.2.6.4) | 76–77 / 82–83 | steps of the proved Theorem | St |
| III.2.6 final Remark: open `H`, the inclusion `H(H) ↪ H(G)`, pseudo-`F ≅ F`, `δ_{H\G} = 1` | 77 / 83 | `HH.OpenSubgroupHeckeInclusionStatement` | A: candidate `755a1381` |
| III.2.6 (III.2.6.5): `ind_H^G ⊣ Res` for open `H` | 77 / 83 | `I.compactInductionAdjunction` ([OpenAdjunction](../../Langlands/Representation/Induction/OpenAdjunction.md)) | D (proved adjunction) |
| III.2.7 Theorem: `Ind_H^G(W̃) ≃ ind_H^G(W ⊗ δ_{H\G})^∼` with the integral pairing | 78 / 84 | `I.ClosedInductionSmoothDualityStatement`; restricted proved case `I.exists_integralDualEquiv_of_section` (compact quotient with a section) | A: candidate `db304a88` |
| III.2.8 Proposition: induction by stages | 78 / 84 | `I.smoothStagesEquiv`, `smoothStagesEquiv_natural`; `I.compactStagesEquiv`, `compactInductionTransitivity`; the clause `I.InductionTransitivityClause` of `I.StructuralStatement` | D (proved); the clause is S: Task 5753 |
| III.2.9 `E(H, τ)`, `E_{H,τ}`; the dual of the coinvariants | 78 / 84 | `J.relations`, `J.Coinvariants`; `J.coinvariantsDualEquiv` | D; P |
| III.2.9 Example: `dim 𝒟(G)_{G,l} = 1` | 78 / 84 | `J.HaarCoinvariantsDimensionStatement` | A: candidate `05269380` |
| III.2.9 Remarks 1–2: action of a normalizing subgroup; the functor `j_H` | 78–79 / 84–85 | `J.action`, `J.map`, `J.isSmooth_action`; `JL.smoothFunctor` | D |
| III.2.9 Lemma (i)–(ii): coinvariants in stages | 79 / 85 | the general `JL.TowerDatum.equiv` and `JL.TowerDatum.smoothIso` (map) | C (specialization to `H = H₁H₂` not packaged) |
| III.2.9 Definition (filtered increasing union) and Remark (compact subsets lie in compact subgroups) | 79 / 85 | `J.CompactSubgroupFilteredUnionStatement` (the Definition is written out in its hypotheses) | A: candidate `05269380` |
| III.2.9 Proposition: `E(H, τ) = {v \| τ(e_K) v = 0 for some compact subgroup K}` | 79 / 85 | `J.CompactAveragingRelationStatement`; the relation detection `JL.mem_relations_iff_compact` is proved | A: candidate `05269380` |
| III.2.9 Corollary: `E′(H) = E(H) ∩ E′` | 80 / 86 | `J.CoinvariantSubrepresentationRelationsStatement` | A: candidate `05269380` |
| III.2.9 Corollary: exactness of coinvariants and of `j_H` | 80 / 86 | `JL.CharacterLocalizationExactnessStatement` at the trivial character, under `JL.IsLimitOfCompactSubgroups` | P: `characterLocalizationExactness`. Clarification C1 |
| III.2.10 the quotient by a closed normal `N`, the action on coinvariants, (III.2.10.1), pseudo-`F = F`, the Proposition with (III.2.10.2) and its inverse, the adjunction and the Corollary | 80–82 / 86–88 | `HH.NormalQuotientStatements` (`NormalQuotientHeckeStatement`, `NormalQuotientAdjunctionStatement`, `NormalQuotientInductionAdjunctionStatement`) and the models of [NormalQuotientModels](../../Langlands/Representation/Hecke/NormalQuotientModels.md) | P: `normalQuotientStatements` |
| III.2.11 Theorem: the Hom and tensor Mackey isomorphisms | 82–83 / 88–89 | `HH.MackeyIsomorphismStatements` (the tensor isomorphism conditional on pseudo-`F ≅ F`, as in the source) | P: `mackeyIsomorphismStatements` |
| III.2.11 proof displays (III.2.11.1)–(III.2.11.10) | 82–83 / 88–89 | steps of the proved Theorem | St |

## III.3 Representations on sections of sheaves (83–85 / 89–91)

Rows follow the published [III.3 map](iii3-sheaf-sections.md), whose "Status and meaning"
column describes each construction.

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| III.3.1 Definition: actions on sheaves, the representation on compact sections, compatible test modules, smooth actions, invariant distributions | 83 / 89 | `SR.SectionActions` (`ActionSheaf`, `compactRepresentation`, `IsSmoothAction`, `Distribution`, `IsInvariantDistribution`), `SR.CompatibleTestActions`, `SR.CompactSectionActions`, `SR.ProjectorActionSheaf` | D |
| III.3.1 the correspondence between equivariant sheaves and compatible modules, and its smooth form | 83 / 89 | `SR.EquivariantModuleStatements.AlgebraicStatement`, `SR.EquivariantModuleStatements.SmoothStatement` | S: Task `56f3a24b` |
| III.3.1 the coinvariant module and the sheaf `F′`; `F_c(X)_G ≅ F′_c(Y)` | 83–84 / 89–90 | `SR.CoinvariantTestModule`, `SR.CoinvariantSheaf`; `SR.CoinvariantStatements.CompactComparisonStatement` | D; S: Task `d1d4a953` |
| III.3.1 Proposition: `F′_y ≅ F_c(q⁻¹{y})_G` | 84 / 90 | `SR.CoinvariantStatements.FibreCoinvariantStatement` | S: Task `d109c703` |
| III.3.1 Corollary: no invariant fibre distributions implies no invariant distributions | 84 / 90 | `SR.CoinvariantStatements.NoInvariantDistributionsStatement` | S: Task `77302ee3`. Clarification C2 |
| III.3.2 the categories of smooth equivariant sheaves; the singleton case is `M(G)` | 84 / 90 | `SR.SectionActions.SmoothActionSheaf`; `SR.SingletonEquivalence.Statement` | D; S: Task `6f50ec94` |
| III.3.2 compact sections, restriction to closed subgroups and invariant locally closed subspaces, point restriction | 84 / 90 | `SR.SectionActions.gammaC`, `subgroupRestriction`, `subgroupSpaceRestriction`, `smoothFixedStalkFunctor`, `PointRestrictionComparison.smoothIso` | D (proved comparisons) |
| III.3.2 a transitive t.d. space with `G` countable at infinity is `G/H` | 84 / 90 | `Topology.RenardOrbitQuotient.TransitiveQuotientHomeomorphismStatement` | P: `transitiveQuotientHomeomorphism` |
| III.3.2 the induction sheaf `F^τ` and `I_H^G`; its identity-coset fibre | 84–85 / 90–91 | `SR.InductionSheaf.functor`; `SR.HomogeneousEquivalence.OriginStalkStatement` | D; S: it follows from `SR.HomogeneousEquivalence.Statement` (`e.functor ⋙ e.inverse ≅ 𝟭`), whose proof is Task `8b9f125d` |
| III.3.2 compact sections are `ind_H^G` of the stalk, and the smooth part of all sections is `Ind_H^G`, with the displayed `α`, `β` | 85 / 91 | `SR.HomogeneousSections.alphaCompact`, `alphaSmoothGlobal`; `SR.HomogeneousSectionStatements.CompactAlphaBetaStatement`, `SmoothGlobalAlphaBetaStatement` | D; S: Tasks `831479b2` (compact) and `5e056b49` (smooth global) |
| III.3.2 Theorem: induction and point restriction are inverse equivalences | 85 / 91 | `SR.HomogeneousEquivalence.Statement` | S: Task `8b9f125d` |

## III.4 Notes (85 / 91)

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| III.4: sources of the chapter ([4], [35], [5]) and the viewpoint of induction and Jacquet functors as forgetful and induction functors of algebras with idempotents | 85 / 91 | — | X |

## Source issues and clarifications

- **S1 (III.1.15, proof of Theorem (iii)).** "Supposons `(ρ, V)` injectif dans `M(G)`. Il
  s'agit de montrer que `Hom(V, W)₀` est injectif" should read "`(ρ, W)` injectif": the
  assertion is that `Hom(V, •)₀` preserves injective objects, and the argument uses
  injectivity of `W`. The published statement has the correct hypothesis.
- **S2 (III.1.14 Scholium).** The Scholium speaks of "la représentation `(τ₁ ⊠ τ₂, V₁ ⊗ V₂)` de
  `A₁ × A₂`". The algebra acting on `V₁ ⊗ V₂` by `a₁ ⊗ a₂ ↦ τ₁(a₁) ⊗ τ₂(a₂)` is the tensor
  product `A₁ ⊗ A₂`; the direct product `A₁ × A₂` does not act this way. The Scholium is read
  with `A₁ ⊗ A₂`, which is how it enters the proof of the Proposition through
  `H(G, K) = H(G₁, K₁) ⊗ H(G₂, K₂)`.
- **C1 (III.2.9 Corollary, last sentence).** "Dès que `H` est réunion de ses sous-groupes
  ouverts compacts" is read with the hypotheses of the Corollary ("avec les hypothèses de la
  proposition ci-dessus"): a filtered increasing union. The published exactness theorem uses
  `IsLimitOfCompactSubgroups`, which the Remark statement (candidate `05269380`) derives from
  the filtered union.
- **C2 (III.3.1 Corollary).** The printed proof restricts an arbitrary algebraic distribution
  to a point stalk. The III.3 map explains why such a restriction is not available in general
  and records a proof route through the Proposition instead. The statement is unaffected.

## Gaps of Chapter III

The accepted and staged candidates of Worker 1222 (`576e9e04`, `755a1381`, `db304a88`,
`05269380`, `b47b8223`, `532e02d1`, `71f85af7`, `ce923198`, `a5167755`, `614c7482`) state the
III.2 gaps of the map, the III.1.3 action of `ℰ′(G)`, the III.1.14 contragredient, the
finite-length case of the III.1.10 Proposition, the non-unimodular III.1.12 Lemma and
Example, the III.1.7 admissibility translation and the III.1.6 comparison of the
contragredient with the I.4.1 dual. These candidate statuses retain their
12 November snapshot.

Both previously listed statement gaps now have published exact proofs:

1. III.1.6: `contragredientDistributionLemma` proves the full
   compact-distribution transpose and compact, possibly non-open, subgroup
   conclusions of `ContragredientDistributionLemmaStatement`. The two
   transpose clauses retain their scalar-pairing action premises;
   distribution-action existence is a separate III.1.3 assertion.
2. III.1.14: `algebraTensorScholium` proves irreducibility,
   factorization and uniqueness for finite-dimensional simple modules over
   `A₁ ⊗[ℂ] A₂`. The tensor-product correction of
   source issue S2 is retained.

No genuine statement gap remains in the audited inventory. This does not
claim proofs or publication of the other pending candidates, or chapter completion.

## Publication evidence for the focused update

- `6e2afa46-1af6-41eb-b945-0581a35a8807`, Worker 338, Task 5961,
  independently approved by Reviewer 1156 without unresolved qualifications
  and published at `7f43c3c930ff92f76dae6589da1678ad729017e5`, proves exactly
  `Langlands.ContragredientDistributionLemmaStatement.{u,v}`. The proof
  computes transposes by the scalar pairing, uses normalized Haar on compact
  subgroups, and constructs the full fixed-dual restriction inverse by finite
  orbit averaging. The last argument requires no distribution action.
- `b6fa5d21-e784-4ba4-a8b8-cb3ff9df7759`, Worker 276, Task 5801,
  independently approved by Reviewer 1094 without unresolved qualifications
  and published at `73b1430a339b037d27e9096762b0400adb4fbd19`, proves exactly
  `Langlands.AlgebraTensorScholiumStatement.{u₁,u₂,v,v₁,v₂,w₁,w₂}`. Its
  three helper proofs use Burnside for external simplicity, evaluation
  from a simple first-factor submodule for factorization, and coefficient
  extraction with Schur's lemma for factor uniqueness.

Each `lean.proof@1` receipt passes Lake build, exact target, unchanged
statement and frozen inputs. Each frozen entry Lean/Markdown pair matches
the workspace and the public files at the checked Library commit. These
checks update only the two named results.

## Summary

Every headed item of Chapter III and every unheaded assertion found is stated, under review,
or covered by the two published proofs above. III.1 is proved except the
`FlathTwoFactorStatement` (Task 5771), the III.1.14 contragredient (candidate `b47b8223`), the
finite-length III.1.10 decomposition (candidate `532e02d1`), the non-unimodular III.1.12
identities (candidate `71f85af7`), the III.1.7 translation (candidate `ce923198`), the
III.1.6 dual comparison (candidate `a5167755`), the III.1.3 `ℰ′(G)` action (candidate
`614c7482`). III.2 is proved except `I.StructuralStatement` (Task 5753,
covering exactness, Frobenius reciprocity and the transitivity clause), `HH.ClosedInductionHomStatement`
(Task 5402) and Worker 1222's four III.2 candidates. The III.3 main assertions are
statements with open proof tasks; the transitive-quotient statement is proved.
