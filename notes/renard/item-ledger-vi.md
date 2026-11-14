# Renard 2026, Chapter VI: item-by-item coverage ledger

Worker 1222, executor of the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`, revision 1. This note is the Chapter VI
part of the item ledger that the task contract requires. It lists every headed
item of Chapter VI and the unheaded assertions found so far. For each row it gives
the printed and PDF pages, the Lean declarations, and the implementation status
with its evidence. It declares no section or chapter complete. A published
statement is not a proof; every row keeps the proof status explicit.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. Printed page
numbers are given first and PDF page numbers second; PDF = printed + 6. Library
facts refer to commit `16c60abdc019c1181a2734d3052305ec3d6e7b85` unless stated
otherwise.

The F3 update of 14 November 2026 checks the VI.6.1 Proposition, VI.6.3 Corollary
and VI.9.4 rows against Library `757a67934ac7327ca3de64f9c869f76ea240ec44`.
Worker 4's
[`StandardIwahoriDecompositionStatements`](../../Langlands/Representation/Jacquet/StandardIwahoriDecompositionStatements.lean)
and its [paired Markdown](../../Langlands/Representation/Jacquet/StandardIwahoriDecompositionStatements.md)
were published as candidate `3c7e8531-2766-4ff7-ae8b-10e9e12b64cb`, independently
approved by Reviewer 1820 and integrated by receipt
`b7827ff04f8c493fa12fcd662df919af` at Library
`410c79471b79f65a02fb0f6070da7f2800793ff3`. Both files at the checked Library commit
match the frozen candidate hashes. The three statements have open proofs; their
comparison implications are proved. Other rows retain their earlier dated status.

## How the rows were checked

Worker 1222 matched each headed item with the declarations whose docstring or
Markdown cites that section, and read the source passage where the match was not
obvious. An earlier tool matched items by Markdown mentions alone. It over-reported
coverage: VI.2.2 Corollary, VI.2.3–VI.2.4 and VI.3.1 had no statement. These items
were stated afterwards (rows below). Proof status comes from a scan of the Library
for theorems whose type is exactly the statement (`proved by`). A `task` entry is a
`lean.proof@1` task whose contract names the statement. Task identifiers are
abbreviated to their first eight hexadecimal digits.

Many Chapter VI statements are **derived formulations**: they use the
represented-parabolic interface (all actual rational parabolics) or the standard-family
interface (`BernsteinStandardFamily`, `BernsteinCuspidalDatum`), and each statement's
Markdown documents its departures from the printed text. A row marks a departure when it
restricts the scope of the source assertion; the comparisons it needs are collected under
"Framework comparisons" below.

Namespace abbreviations: `CS` = `Langlands.CuspidalSupport`,
`RP` = `Langlands.Aubert.General.RepresentedParabolic`,
`RPF` = `Langlands.Aubert.General.RationalPointFamily`,
`AG` = `Langlands.Aubert.General`, `J` = `Langlands.Jacquet`,
`AF` = `Langlands.Renard.AlgebraicFamily`, `PN` = `Langlands.Plancherel.RationalNormalized`.

Status codes:

- **P**: proved; the named theorem has exactly the statement's type.
- **S**: statement published; its proof is open (a proof task is named when verified).
- **D**: definition or construction.
- **C**: covered by a published statement that is stronger or equivalent, or
  derived from published statements; the row says which.
- **Restricted scope**: the published statement covers the item only under extra
  hypotheses, which the row names; the full source scope is a gap.
- **St**: a step of the proof of a stated result, covered by that result or by a
  proved construction.
- **X**: expository, convention or attribution.
- **A**: candidate accepted by review, waiting for integration.
- **R**: candidate staged, under review.
- **G**: genuine gap, with its blocker.

## VI.1 Parabolic induction and restriction

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| VI.1.1 Theorem | 135 / 141 | `RP.LeviUnnormalizedFrobeniusReciprocityStatement`, `RP.LeviUnnormalizedFunctorsExactStatement` | P: `leviUnnormalizedFrobeniusReciprocity`, `leviUnnormalizedFunctorsExact` |
| VI.1.1 Corollary | 135 / 141 | `RP.LeviUnnormalizedFunctorsPreserveLimitsStatement` | P: `leviUnnormalizedFunctorsPreserveLimits` |
| VI.1.1 Remark, conclusion (`Ind_P^G` preserves colimits) | 135 / 141 | `RP.LeviUnnormalizedFunctorsPreserveLimitsStatement`, `RP.LeviUnnormalizedParabolicStatements` | P: `leviUnnormalizedFunctorsPreserveLimits` |
| VI.1.1 Remark, first sentence (`Ind_P^G` has a right adjoint) | 135 / 141 | none | G: the adjoint is built from `I_M^P`, the pseudo-forgetful functor and a twist, which are not published functors of the represented interface (see `LeviUnnormalizedParabolicStatements.md`) |
| VI.1.2 normalizations (VI.1.2.1)–(VI.1.2.2) | 135 / 141 | normalized functors of the represented-parabolic interface (`Langlands/Representation/Aubert/General/Parabolic`) | D |
| VI.1.2 Remark (convention for `δ_P`) | 136 / 142 | modulus conventions recorded in `Aubert/General/Parabolic.md` | X |
| VI.1.2 Proposition | 136 / 142 | `RP.LeviFrobeniusReciprocityStatement`, `RP.LeviParabolicFunctorsExactStatement` | P: `leviFrobeniusReciprocity`, `leviParabolicFunctorsExact` |
| VI.1.2 Corollary | 136 / 142 | `RP.LeviParabolicFunctorsPreserveLimitsStatement` | P: `leviParabolicFunctorsPreserveLimits` |
| VI.1.2 Remarks (`δ_P` trivial on compact subgroups and on `N`; (VI.1.2.3)) | 136 / 142 | `isUnimodularModulus_of_isLimitOfCompactSubgroups`, `closedHalfCharacter_unipotent`, `normalizedInductionFunctor_covariant` (`Aubert/General/Parabolic`) | P (proved lemmas) |
| VI.1.3 Proposition | 136 / 142 | `RP.LeviJacquetFiniteTypeStatement` | P: `leviJacquetFiniteType` |
| VI.1.4 Lemma | 137 / 143 | `RP.LeviParabolicTransitivityStatement`; dynamic form `AG.DynamicNestedParabolicTransitivityStatement` | P: `leviParabolicTransitivity` |

## VI.2 Supercuspidal representations

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| VI.2.1 Definition | 137 / 143 | `RP.IsSupercuspidal` (`Exponents/LeviSupercuspidalInductionSupport`) | D |
| VI.2.1 Remark 1, first block (standard parabolics suffice) | 137 / 143 | none | G: comparison of the represented predicate with the standard-family one; needs conjugacy of parabolics to standard ones (Chapter V framework) |
| VI.2.1 Remark 2, first block (subquotients) | 137 / 143 | `RP.IsSupercuspidal.of_isSubquotient`; conjunct of `RP.SupercuspidalRemarksStatements` | P (theorem); S: task 63db6d7b for the conjunction |
| VI.2.1 Theorem, (a) ⇔ (c) | 137 / 143 | `RPF.RationalCuspidalCompactRestrictionStatement`, `RPF.RationalCompactRestrictionCuspidalStatement` (standard-family cuspidality, `rationalPointTopology`) | P: `rationalCuspidalCompactRestriction`, `rationalCompactRestrictionCuspidal` |
| VI.2.1 Theorem, (a) ⇔ (b) | 137 / 143 | `RP.SupercuspidalCoefficientCriterionStatement`; unitary irreducible case `RP.SupercuspidalUnitaryCoefficientCompactSupportStatement` | S: tasks ebdfeaa3, 1aa60759 |
| VI.2.1 Remarks, second block (compact centre; `f_{K,v}` criterion) | 139 / 145 | `RP.SupercuspidalRemarksStatements` | S: task 63db6d7b |
| VI.2.1 Corollary | 139 / 145 | `RPF.RationalCuspidalEmbeddingStatement`, `RP.LeviCuspidalEmbeddingStatement`, `RPF.RationalCuspidalSeriesExistenceStatement` | P: `rationalCuspidalEmbedding`, `leviCuspidalEmbedding`, `rationalCuspidalSeriesExistence` |
| VI.2.2 Theorem | 140 / 146 | `AG.RationalPointsIrreducibleAdmissibleStatement` | S: task 173e44ba |
| VI.2.2 Corollary | 140 / 146 | `CS.ContragredientIrreducibilityStatement` | S: task 33346af6 |
| VI.2.3 Theorem and Remark | 140–141 / 146–147 | `CS.RationalPointsUniformAdmissibilityStatement`, `CS.RationalNormKernelUniformAdmissibilityStatement` (in `CS.UniformAdmissibilityStatements`) | S: task 8e40225b |
| VI.2.4 Proposition | 141 / 147 | `CS.SupercuspidalUniformCoefficientSupportStatement` (in `CS.UniformAdmissibilityStatements`) | S: task 8e40225b |

## VI.3 The cuspidal part of the category

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| VI.3.1 Lemma | 142–143 / 148–149 | `CS.RationalNormKernelConjugationLemmaStatement` | S: task 6665e450 |
| VI.3.2 Proposition (i)–(iii) | 143 / 149 | `CS.RationalNormKernelOrbitStatement`, `CS.RationalNormKernelFiniteRestrictionStatement`, `CS.RationalNormKernelTwistEquivalenceStatement` | P: `rationalNormKernelOrbit`, `rationalNormKernelFiniteRestriction`, `rationalNormKernelTwistEquivalence` |
| VI.3.3 Proposition (`W'` is `G`-invariant; `π(g) ∘ π(e_{σ_i}) = π(e_{σ_i^g}) ∘ π(g)`) | 145 / 151 | VI.3.1 (ii) above, `CompactIsotypicComplementStatement` (IV.1.5), and the covariance lemma `pointwiseFiniteSum_isotypic_covariant` (`CompactCoefficient/AmbientProjector`) | C: derived from these |
| (VI.3.3.1) decomposition | 145 / 151 | `CS.RationalCuspidalInertiaDecompositionStatement`; compact-restriction form `CS.RationalCompactRestrictionInertiaDecompositionStatement` | S: task 5c59bed4; compact-restriction form P |
| VI.3.3 Remarks 1–2 | 145 / 151 | `CS.RationalInertiaOrbitTorusStatement`, `CS.RationalTwistStabilizerKernelStatement`; Remark 2 from VI.3.2 (i), (iii) and VI.2.1 | S: tasks f5aebf51, e383bb3b; Remark 2 C |
| VI.3.4 Theorem | 146 / 152 | `CS.RationalNormKernelCategoryDecompositionStatement` (with `CS.RationalNormKernelUniformSupportStatement`, `CS.RationalNormKernelFixedLevelFinitenessStatement`) | S: tasks 29860e9c, b69ca612, f0509729 |
| VI.3.4 Remark | 146 / 152 | `CS.RationalCuspidalInertiaFinitenessStatement` | S: task 61b5cb94 |
| VI.3.5 Theorem | 146 / 152 | `CS.RationalWholeCuspidalCategoryDecompositionStatement`, `CS.RationalCuspidalInertiaProductDecompositionStatement`, `RP.RepresentedCuspidalRemainderSplittingStatement` | S: tasks 4bee987a, b1a82b53, 660fd8c7 |
| VI.3.6 Lemma | 147 / 153 | `RP.RepresentedSupercuspidalSubquotientRealizationStatement` | S: task 42051bc6 |
| VI.3.6 Proposition | 148 / 154 | `RP.RepresentedSupercuspidalCentralProjectivityStatement` | S: task 96d326f0 |

## VI.4 The category `M(G)[π]` and its centre

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| VI.4.1 Proposition | 149 / 155 | `CS.RationalSummandSmallProgeneratorStatement` | S: task ca5fea74 |
| VI.4.1 Remark | 149–150 / 155–156 | `CS.RationalUniversalSmallProgeneratorStatement`; comparison `CS.RationalUniversalProgeneratorComparisonStatement` | S: task 0ba788d6; comparison P |
| VI.4.1 Theorem | 150 / 156 | `CS.RationalSummandHomEquivalenceStatement`; quasi-inverse `CS.RationalSummandTensorQuasiInverseStatement` | S: tasks ca5fea74, 23aefeba |
| VI.4.2 Proposition | 152 / 158 | `CS.RationalNormKernelHeckeStatement`; right-module paragraphs `CS.RationalNormKernelHeckeModuleStatement` | P: `rationalNormKernelHecke_equiv`; modules S: task 31647676 |
| VI.4.3 structure (VI.4.3.1)–(VI.4.3.3) | 154–155 / 160–161 | `CS.RationalNormKernelHeckeStructureStatement` | S: task 7e3489cf |
| VI.4.3 Lemma | 154 / 160 | `CS.RationalNormKernelEndSeparationStatement` | P: `rationalNormKernelEnd_separation` |
| VI.4.3 Corollary (i)–(ii) | 155 / 161 | `CS.RationalNormKernelEndDomainStatement`, `CS.RationalSummandEndCommutativeStatement` | P: `rationalNormKernelEnd_isDomain`, `rationalSummandEnd_commutative` |
| VI.4.4 Remark (the group `T`) | 157 / 163 | `CS.RationalTwistStabilizerKernelStatement` | S: task e383bb3b |
| VI.4.4 Lemma | 157 / 163 | `CS.RationalSummandStabilizerLemmaStatement` | S: task c6f40f07 |
| VI.4.4 Theorem | 158 / 164 | `CS.RationalSummandEndCenterStatement` | P: `rationalSummandEndCenter` |
| VI.4.4 Corollary | 159 / 165 | `CS.RationalSummandEndNoetherianStatement`; remark on modules `CS.RationalInertiaBlockNoetherianModulesStatement` | P: `rationalSummandEndNoetherian`; remark S: task cf9475ff |
| VI.4.4 Proposition | 159 / 165 | `CS.RationalSummandCenterGroupAlgebraStatement`, `CS.RationalSummandCenterVarietyStatement` | P: `rationalSummandCenterGroupAlgebra`; variety S: task 1347deec |
| VI.4.5 Proposition | 160 / 166 | `CS.RationalInertiaBlockCenterEvaluationStatement`, `CS.RationalSummandBlockCenterStatement` | S: task 6b7a3e50 |
| VI.4.5 Corollary | 160 / 166 | `CS.RationalInertiaBlockIndecomposableStatement` | S: task 6b7a3e50 |

## VI.5 The geometric lemma and composition series of induced supercuspidals

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| VI.5.1 Theorem and its reformulation | 161–162 / 167–168 | `RP.RepresentedGeometricLemmaStatement`, `RP.RepresentedGeometricLemmaGeometryStatement` | P: `representedGeometricLemma`, `representedGeometricLemmaGeometry` |
| VI.5.1 Remarks (representatives `W_{Q,P}`; notation for the conjugation functor) | 161 / 167 | `RP.RepresentedGeometricLemmaGeometryStatement`; conjugation functors in `Aubert/General/ConjugationComposition` | P / D |
| VI.5.1 Proposition (support filtration lattice) | 162 / 168 | support filtration construction `Aubert/General/ParabolicSupportFiltration` | St: step of the proved VI.5.1 Theorem |
| (VI.5.1.3) injectivity (proof replaced in the 2026 edition) | 167 / 173 | step of the proved VI.5.1 Theorem | St |
| VI.5.2 Definition (cuspidal datum) | 172 / 178 | `BernsteinCuspidalDatum` (standard family, `CuspidalSupport/BernsteinData`); represented cuspidal-support predicates (`Exponents/LeviSupercuspidalInductionSupport`) | D |
| VI.5.2 Lemma | 173 / 179 | `RP.LeviInductionNoSupercuspidalSubquotientStatement` | S: task fc21c11d |
| VI.5.3 Proposition (i) | 173 / 179 | `RP.LeviJacquetInductionVanishingStatement` | P: `leviJacquetInductionVanishing` |
| VI.5.3 Proposition (ii) | 173 / 179 | `RP.LeviJacquetInductionNoSupercuspidalStatement` | S: task fc21c11d |
| VI.5.3 Proposition (iii) | 173 / 179 | `RP.LeviJacquetInductionSupercuspidalFiltrationStatement` | P: `leviJacquetInductionSupercuspidalFiltration` |
| VI.5.4 Theorem | 173–175 / 179–181 | `RP.LeviSupercuspidalInductionAssociationStatement`, `CS.BernsteinSupercuspidalInductionBoundsStatement`, `RPF.RationalSupercuspidalInductionFiniteLengthStatement`, `RPF.RationalCuspidalSupportAssociationStatement` | S: tasks fc21c11d, c43511c5, 59ee1ed5, fc414cb1 |
| VI.5.4 definition of elementary elements | 175 / 181 | inline in `Langlands.GroupScheme.StandardWeylElementaryChainStatement` | D (inline, see next row) |
| VI.5.4 Lemma (Bernstein–Zelevinsky, Lemma 2.17) | 175 / 181 | `Langlands.GroupScheme.StandardWeylElementaryChainStatement` (hypothesis `L ≠ G` added: the literal lemma fails for `L = M = G`, `w ≠ 1`) | S: task 011068fd. `W(L, M)` and `l_S(M)` are written inline on the actual relative Weyl group; Worker 176, asked on 12 November 2026, has no named version and knows of none planned |
| VI.5.4 Corollary (i)–(iii) | 175 / 181 | `RP.LeviSupercuspidalInductionSameLeviStatement` | S: task fc21c11d |

## VI.6 Finiteness theorems

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| VI.6.1 Theorem (Jacquet lemma, admissible `V`) | 176 / 182 | `RPF.GeneralizedJacquetLemmaStatement` (VI.9.1 form: all smooth `V`, but only dynamic parabolics and compact open `K` admitting an `M`-central `g` with `IsIwahoriContraction`); generic admissible form `Langlands.Jacquet.fixedJacquetMap_surjective_of_iwahoriContraction` (`Jacquet/IwahoriContractionAdmissibility`), given one explicit contraction | Restricted scope: the VI.9.1 statement is S (task cac6f709); the admissible form is P under its explicit contraction hypothesis. G: the source's scope (every `K` with an Iwahori decomposition along an arbitrary parabolic) is not stated; it needs a contracting element for such `K` and transport from dynamic to arbitrary parabolics (framework comparison F2 below) |
| VI.6.1 Corollary | 176 / 182 | `RP.ArbitraryParabolicJacquetAdmissibilityStatement` | P: `arbitraryParabolicJacquetAdmissibility` |
| VI.6.1 Proposition and (VI.6.1.2) | 177 / 183 | `J.StandardIwahoriCanonicalSectionStatement` (standard parabolics; every compact open `K` with the ordered Iwahori decomposition); earlier `J.StandardCanonicalSectionStatement` | S: the Iwahori-only statement has an open proof. The earlier basis-member special case is P: `standardCanonicalSection`. F3 is stated for standard parabolics; the arbitrary-parabolic scope remains separate |
| VI.6.2 Lemma | 178 / 184 | `AG.DynamicInductionIrreducibleFiniteLengthStatement`; main assertion `RP.LeviInductionFiniteLengthStatement`, `AG.DynamicInductionFiniteLengthStatement` | S: tasks 02257068, 9b0a1303, 174d2de0 |
| VI.6.3 Theorem (Howe) | 178 / 184 | `AG.RationalPointsFiniteLengthAdmissibleStatement`, `Langlands.SmoothRep.RationalPointsFinitelyGeneratedAdmissibleFiniteLengthStatement` | S: tasks 96949545, 03a0d235; finite length ⇒ finite type is immediate (a finite-length object is Noetherian) |
| VI.6.3 Lemma | 178 / 184 | `Langlands.Jacquet.FixedVectorsGenerationStatement` (theorem `fixedVectorsGeneration`), `NormalizedJacquetBridge.normalized_generation` | P |
| VI.6.3 Proposition | 178 / 184 | `CS.SupercuspidalSubquotientFixedVectorsStatement` (every compact open `K`) | S: task e0efe074 |
| VI.6.3 Corollary | 179 / 185 | the VI.9.4 Corollary statement `J.StandardIwahoriFixedVectorSubquotientGenerationStatement` (no admissibility; `K` normal in `K₀` with Iwahori decompositions along every standard parabolic) | C: the admissible special case of this published statement, whose proof is open. The earlier basis-member version `J.StandardFixedVectorSubquotientGenerationStatement` remains S: task e8bd5ada |
| VI.6.4 (finite length of Jacquet modules) | 179 / 185 | `RP.LeviJacquetFiniteLengthStatement`, `AG.DynamicJacquetFiniteLengthStatement` | S: tasks 9b0a1303, 73e60be8 |

## VI.7 The Bernstein decomposition

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| VI.7.1 Lemma | 180 / 186 | `RP.LeviCuspidalSupportAssociationStatement` | S: task 9b0a1303 |
| VI.7.1 Proposition | 180 / 186 | `RP.LeviCuspidalSupportSurjectiveStatement`; finite fibres `CS.BernsteinCuspidalSupportFiniteFibreStatement` | S: tasks 9b0a1303, a955226a |
| VI.7.1 Example | 181 / 187 | variety part is the V.2.7 Corollary `CS.RationalInertiaOrbitTorusStatement` | C; S: task f5aebf51 |
| VI.7.1 Theorem | 181 / 187 | `CS.BernsteinCuspidalDataVarietyStatements`, `CS.BernsteinComponentVarietyStatement` | S: task a955226a |
| VI.7.2 Theorem | 182 / 188 | `CS.BernsteinDecompositionStatement`; abelian blocks `CS.BernsteinBlockAbelianStatement` | S: tasks 42ad56a2, 03088b22; abelian blocks P: `bernsteinBlockAbelian` |
| VI.7.2 first Lemma | 182 / 188 | `CS.BernsteinSplitSubrepresentationStatement` | S: tasks 42ad56a2, 03088b22 |
| VI.7.2 second Lemma | 182–183 / 188–189 | `CS.BernsteinCuspAdjunctionStatement` | S: task 03198d2e |
| VI.7.2 Proposition | 184 / 190 | `CS.BernsteinBlockCharacterizationStatement` | S: task 2a804ec7 |
| VI.7.3 Proposition | 185 / 191 | `CS.BernsteinInductionRestrictionStatement`, `RPF.RationalSupportCategoryInductionJacquetStatement` | S: tasks 064bce40, 09268952 |
| VI.7.4 idempotents and Hecke ideals | 185–186 / 191–192 | `CS.BernsteinCentralIdempotentStatements`, `CS.BernsteinHeckeIdealDecompositionStatement` | S: tasks 289835fa, 31433303 |
| VI.7.4 Remark | 186 / 192 | none | X: false as printed in general; recorded as a source issue in `coverage-update-2026-11-11.md` |
| VI.7.5 Proposition | 186 / 192 | `RP.SmoothRepNoetherianCategoryStatement` | S: task ea93fe45 |
| VI.7.5 Theorem | 187 / 193 | `RP.LeviInductionFiniteTypeStatement` | S: task ea93fe45 |

## VI.8 Algebraic families

The [VI.8 assertion map](algebraic-families-progress.md) by other workers maps the
printed VI.8 assertions to their units; this table gives the headed items.

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| VI.8.1 Definition (`(G, B)`-modules) | 187 / 193 | category `M(G, B)` of flat smooth families (definition unit `e21322ee`); hypotheses of the `AF` statements | D |
| VI.8.1 Proposition | 187 / 193 | `AF.AdmissibilityCriterionStatement` (with `AF.FixedTensorComparisonStatement`) | P (proof task eb5ee8fa) |
| VI.8.1 Remark | 188 / 194 | `AF.FlatnessCriterionStatement` | P (proof task eb5ee8fa) |
| VI.8.1 Lemma | 189 / 195 | `AF.SpecializationAdmissibilityStatement` | P (proof task eb5ee8fa) |
| VI.8.1 Example | 189 / 195 | `PN.RationalUniversalTensorFinitenessStatement`, `AF.UniversalSpecializationStatement` | P |
| VI.8.2 Lemma (induction preserves admissibility) | 190 / 196 | `AF.InductionAdmissibleStatement`; flatness `AF.InductionFlatStatement` | P (proof task 9631258e) |
| VI.8.2 Proposition | 190 / 196 | `AF.InductionBaseChangeStatement` | P (proof task 4df85a84) |
| VI.8.2 Corollary | 191 / 197 | special case `E = ℂ_χ` of `AF.InductionBaseChangeStatement`; universal family `PN.RationalNormalizedInducedSpecializationStatement` | C; universal family P |
| VI.8.3 Proposition | 191 / 197 | `AF.JacquetFlatStatement`, `AF.ParabolicStatements` | P (proof tasks 9631258e, 4df85a84) |
| VI.8.4 Theorem | 191 / 197 | `AF.LocalFreeCoverStatement` | P (proof task eb5ee8fa) |
| VI.8.4 Proposition | 192 / 198 | `AF.InducedIrreducibilityOpenStatement` | S: task 2113598c |
| VI.8.5 Theorem | 193 / 199 | `AF.GenericInducedIrreducibilityStatement` | S: task 822bbd74 |
| VI.8.5 Lemma | 194 / 200 | `AF.CentralCharacterSplittingStatement` | P (proof task 5c0deaf5) |
| VI.8.6 Proposition | 195 / 201 | `AF.EndomorphismScalarStatement` | P |
| VI.8.6 Example | 195 / 201 | `AF.SupercuspidalFamilyEndomorphismStatement` | S: task 8ed6fa75 |

## VI.9 The second adjointness theorem

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| VI.9.1 Theorem (generalized Jacquet lemma) | 195 / 201 | `RPF.GeneralizedJacquetLemmaStatement` (dynamic parabolics; `K` admitting an `M`-central `g` with `IsIwahoriContraction`) | Restricted scope: S (task cac6f709). G: every `K` with an Iwahori decomposition along an arbitrary parabolic (F2) |
| VI.9.1 first Lemma (`V(N) ∩ V^K = ⋃ ker A^i`) | 196 / 202 | `powerKernelSup_eq_ker_of_iwahoriContraction` (`Jacquet/IwahoriContractionAdmissibility`), `fixedJacquetMap_kernel_locally_nilpotent` (`Jacquet/CompressionLocalization`) | P |
| VI.9.1 second Lemma (localization) | 196 / 202 | `compressionJacquetLocalizationEquiv`, `localizationEquivOfKernelExhaustion` | D / P (proved construction) |
| VI.9.1 Proposition (uniform stabilization) | 197 / 203 | `RPF.UniformCompressionStabilizationStatement` (same setting; `b` chosen after `χ`, `K` and `g`) | Restricted scope: S (task 47e556e6). The source's `b = b(G, K)` follows from the bound clause of candidate `a6dc47dd` together with VI.2.3, within the same setting. G: the source's class of `K` (F2) |
| VI.9.1 Proposition, localization at `A` is `(V^K_*, A)` | 197 / 203 | the proved C.II theorem `Langlands.Renard.EndomorphismLocalization.stablePowerImageStatement` (`Algebra/RenardLocalizationStabilityProof`), for any endomorphism with a stable power | C: derived from that theorem and the Proposition's stable power `A^b`; the application to `compressedAction` is not published as a separate statement |
| VI.9.1 Proposition, `b ≤ c(G, K)`; Remarks 1–3 | 197–198 / 203–204 | `RPF.GeneralizedJacquetRemarksStatement`, `RP.GeneralizedJacquetContractingRangeStatement` | R: candidate `a6dc47dd` |
| VI.9.2 (VI.9.2.2) stability for the universal induced family | 198–199 / 204–205 | `Langlands.Plancherel.RationalSupercuspidalJacquetFamilyFiniteStatement` and the VI.9.1–VI.9.3 map (`uniform-compression-progress.md`) | St: step of the VI.9.1 Proposition; Jacquet-family finiteness P |
| VI.9.3 extension to all smooth representations | 200 / 206 | conditional helpers in the VI.9.1–VI.9.3 map | St |
| VI.9.4 Corollary | 201 / 207 | `J.StandardIwahoriFixedVectorSubquotientGenerationStatement`; earlier `J.StandardFixedVectorSubquotientGenerationStatement` | S: the Iwahori-only statement has an open proof and uses the source's conditions on `K`. Task e8bd5ada concerns the earlier basis-member version |
| VI.9.4 Proposition | 201 / 207 | `J.StandardIwahoriFixedVectorHeckeEquivalenceStatement`; earlier `J.StandardFixedVectorHeckeEquivalenceStatement` (modules over the measure-free `LevelHeckeAlgebra ℂ K`) | S: the Iwahori-only statement has an open proof; task e8bd5ada concerns the earlier basis-member version. G: the comparison with the Haar-measure `H(G, K)` (`Hecke.HeckeAlgebra.Corner`) and identification of the inverse functor remain unstated |
| VI.9.5 (`r_P^G` preserves `B`-admissibility) | 201 / 207 | `AF.JacquetAdmissibleStatement`; reduction `AF.JacquetAdmissibleReductionStatement` | S: task 8057266d; reduction P |
| VI.9.6 first Theorem (second adjointness) | 201 / 207 | `RP.LeviSecondAdjointnessStatement` | S: tasks c0fa1878, eac5190f |
| VI.9.6 second Theorem (`r_{P̄}^G π̃ ≅ (r_P^G π)~`) and the equivalence of the two | 201–202 / 207–208 | `RP.LeviJacquetContragredientStatement`, `RP.LeviSecondAdjointnessContragredientEquivalenceStatement` | S: tasks c0fa1878, 3ec57776 |
| VI.9.6 Proposition (pairing) | 202 / 208 | `RP.LeviJacquetOppositePairingStatement` | S: task 56c26504 |
| VI.9.7 Theorem | 205 / 211 | `RP.LeviCompletionOppositeJacquetStatement` | S: task 56c26504 |

## VI.10 The Bernstein centre

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| VI.10.1 Lemma, Proposition, Corollary, Theorem | 207–208 / 213–214 | `RP.InducedProgeneratorIndependenceStatement`, `CS.BernsteinInducedProgeneratorStatement` | S: task 2174cd68 |
| VI.10.2 Theorem, `Hom_G(Π_Ω, ·)` is an equivalence | 208 / 214 | `CS.BernsteinBlockHomEquivalenceStatement` (on the published block, see F1) | S: task 2174cd68 |
| VI.10.2 Theorem, the quasi-inverse is `M ↦ M ⊗_{R_Ω} Π_Ω` | 208 / 214 | `CS.BernsteinBlockTensorQuasiInverseStatement` (candidate `a4b157d0`, published at Library `79de65ce`; the VI.4.1 analogue is `CS.RationalSummandTensorQuasiInverseStatement`) | S: Task 5686 |
| VI.10.3 Proposition, Corollary | 209 / 215 | `CS.BernsteinBlockJacquetFaithfulStatement`, `RP.SupercuspidalInductionLengthStatement` | S: task 2174cd68 |
| VI.10.4 (VI.10.4.1)–(VI.10.4.2): induction of modules corresponds to `i_P^G` | 209–210 / 215–216 | none | St: step of the VI.10.4 Theorem (task c4d4541b) |
| VI.10.4 first Lemma (`R_Ω` free of rank `|W(D)|` over `R_D`) | 210 / 216 | `RP.InducedProgeneratorEndFreeStatement` | S: task 03c64afa |
| VI.10.4 second Lemma (`ℨ_Ω ⊂ ℨ_D`) | 211 / 217 | `RP.InducedProgeneratorCenterInclusionStatement` | S: task 03c64afa |
| VI.10.4 `ℨ_Ω ⊂ ℨ_D^{W(D)}`, `ℨ_Ω = ℨ_D^{W(D)}` | 211–212 / 217–218 | none | St: steps of the VI.10.4 Theorem |
| VI.10.4 third Lemma (centralizer for filtered bimodules) | 211–212 / 217–218 | `Langlands.Algebra.RenardBimoduleFiltrationCentralizerStatement` | S: task 74deb29a |
| VI.10.4 Theorem | 212 / 218 | `CS.BernsteinCenterFunctionsStatements` (with `CS.BernsteinBlockCenterFunctionsStatement`, `CS.BernsteinCentralIdempotentFunctionStatement`) | S: task c4d4541b |
| VI.10.4 Corollary, Remarks 1–3 | 212 / 218 | `CS.BernsteinBlockCenterNoetherianStatement`, `CS.BernsteinBlockIndecomposableStatement`; Remarks 1–2 in `CS.BernsteinCenterFunctionsStatements` | S: tasks 80d07293, c4d4541b |
| VI.10.5 Proposition | 213 / 219 | `RP.HarishChandraHomomorphismStatement` | S: task 03c64afa; finiteness of `i_{MG}` as a morphism of varieties is stated only through its consequence (finite generation) |
| VI.10.6 Theorem, Proposition | 213–214 / 219–220 | `CS.CompactOpenInertialFinitenessStatement`, `J.FixedVectorCategoryStatements` | S: tasks f504c0e1, 423c3289 |
| VI.10.6 Corollary (`B(M)_{K_M} = i_{MG}^{-1}(B(G)_K)`) | 215 / 221 | none | G: needs Bernstein data for a Levi subgroup `M` (Levi-scheme morphisms), not available in the standard-family framework |
| VI.10.7 Lemma, Theorem | 215 / 221 | `CS.FiniteTypeComponentCharacterizationStatement`, `RP.FiniteTypeCenterAdmissibleStatement` | S: task f504c0e1 |
| VI.10.7 Corollary | 216 / 222 | `RP.HeckeAlgebraCenterFiniteStatement` | S: task aea42eff |
| VI.10.7 Proposition | 216 / 222 | `CS.FiniteTypeComponentCharacterizationStatement` | S: task f504c0e1 |
| VI.10.7 Variant (`(G, B)`-modules) | 217 / 223 | none | G: needs the action of `ℨ(G)` on `(G, B)`-modules and the Bernstein components of families |
| VI.10.8 Theorem | 217 / 223 | `RP.CenterFiniteHoweStatement` | S: task f504c0e1 |

## VI.11 Notes on Chapter VI

| Item | Pages | Status |
| --- | --- | --- |
| VI.11 notes | 217–218 / 223–224 | X: attributions and references (Harish-Chandra, Jacquet, Bernstein, Bernstein–Zelevinsky [5], Casselman [20], DeBacker [23], notes [38]). The notes repeat that the second adjointness theorem is equivalent to a strong form of Casselman duality without admissibility; this is the VI.9.6 equivalence stated above. |

## Framework comparisons used above

These comparisons record the scope and proof obligations of the rows above.
F3 now has published targets for the source's class of `K` along standard
parabolics; their proofs remain open.

- **F1. Bernstein blocks.** The published blocks (`BernsteinBlock`,
  `BernsteinSaturatedBlock`) use the induction-occurrence support relation. The
  comparison targets are in `CuspidalSupport/BernsteinSupportComparison` (statements
  parametrized by the standard family): existence of an induction presentation,
  `CS.BernsteinCuspidalSupportExistenceStatement`, is proved
  (`bernsteinCuspidalSupportExistence`); association,
  `CS.BernsteinCuspidalSupportAssociationStatement`, is proved conditionally on the
  represented VI.5.4 association statement
  (`bernsteinCuspidalSupportAssociation_of_represented`); the comparison with Renard's
  Jacquet-defined support, `CS.BernsteinInductionJacquetSupportComparisonStatement`, and
  `CS.BernsteinAssociatedSupportInvarianceStatement` have no proof. The rows of VI.7 and
  VI.10 that use the published blocks depend on these comparisons.
- **F2. Iwahori decompositions and contracting elements.** The VI.9.1 statements and
  the VI.6.1 Theorem coverage use dynamic parabolics and a compact open `K` with an
  `M`-central contracting `g` (`IsIwahoriContraction`). The source allows every `K`
  with an Iwahori decomposition along an arbitrary parabolic. No statement asserts that
  such `K` admit a contracting element, and the transport to arbitrary parabolics is
  not stated.
- **F3. V.5.2 basis members: statement gap closed for standard parabolics.**
  The published `J.StandardIwahoriCanonicalSectionStatement`,
  `J.StandardIwahoriFixedVectorSubquotientGenerationStatement` and
  `J.StandardIwahoriFixedVectorHeckeEquivalenceStatement` assume only the ordered
  `HasIwahoriIntersectionDecomposition` on `K`, along one standard parabolic
  for VI.6.1 and every standard parabolic for VI.6.3 and VI.9.4. They retain the
  other data and conclusions of the earlier statements: the canonical section uses
  a supplied compatible split component; the VI.9.4 statements retain `K` contained
  and normal in a compact `K₀` with its Iwasawa factorization. The theorems
  `J.standardCanonicalSectionStatement_of_standardIwahori`,
  `J.standardFixedVectorSubquotientGenerationStatement_of_standardIwahori` and
  `J.standardFixedVectorHeckeEquivalenceStatement_of_standardIwahori` prove the
  implications to the earlier basis-member versions by extracting the Iwahori
  conjunct. These are conditional implications, not proofs of the three new
  statements, whose proofs are open. No successor task identifiers for these
  targets were verified for this update. The arbitrary-parabolic version of the
  VI.6.1 Proposition and the Haar-Hecke and inverse-functor comparisons are
  separate obligations.
- **F4. Represented versus standard parabolics.** See gap 2 below.

## Genuine gaps of Chapter VI

1. VI.1.1 Remark, first sentence: the right adjoint of `Ind_P^G` needs functors
   (`I_M^P`, the pseudo-forgetful functor) not published on the represented
   interface.
2. VI.2.1, first Remark of the first block: a framework comparison (represented
   versus standard parabolics) that needs conjugacy of parabolics to standard ones.
3. VI.10.2 Theorem: the quasi-inverse `M ↦ M ⊗_{R_Ω} Π_Ω` was not identified in the
   pinned Library. It is now stated by the published
   `BernsteinBlockTensorQuasiInverseStatement` (candidate `a4b157d0`, Library `79de65ce`),
   with proof Task 5686.
4. VI.10.6 Corollary: blocked on Bernstein data for Levi subgroups.
5. VI.10.7 Variant: needs `ℨ(G)` acting on `(G, B)`-modules.
6. VI.9.4 Proposition: the comparison of the measure-free level Hecke algebra with
   `H(G, K)` and the inverse functor.
7. The arbitrary-parabolic scope of VI.6.1 (Theorem and Proposition) and VI.9.1
   through F2, and the block comparison F1. The source's class of `K` for standard
   parabolics in VI.6.1 Proposition, VI.6.3 Corollary and VI.9.4 is now stated by
   the F3 targets above; their proofs remain open.

The VI.5.4 Lemma, unstated before this audit, is now the published
`StandardWeylElementaryChainStatement`. The pending candidate `a6dc47dd` (VI.9.1 bound
and Remarks) closes the remaining gap found by this audit, once published.
