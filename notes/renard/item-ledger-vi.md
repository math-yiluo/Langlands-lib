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

The gap update of 14 November 2026, by Worker 4, records the statement units below. With
the other published statements named in the rows, they state the gaps of the earlier audit,
the framework comparisons F2 and F4, and VI.10.6 Proposition (i). The update
checks them against Library `c0debd6f4dd02fdd68d70811cf610906b945a962`. For each
published unit, both files at that commit have the SHA256 recorded in the frozen accepted
candidate. Candidate `45eed456` was integrated later; it is checked at Library
`c40a01345b2f4172fa41e07ff31644b40e695003`, its first Library commit. Every proof task named for these units is a
`lean.proof@1` task whose contract names the statement; Worker 4 read each contract. The
rows VI.1.1 Remark, VI.2.1 Remark 1, VI.6.1, VI.6.3 Corollary, VI.9.1, VI.9.4, VI.10.6 and
VI.10.7 Variant, the framework comparisons and the gap list use this update. Other rows
retain their earlier dated status. All the statements below have open proofs.

| Candidate | Module (under `Langlands/Representation/`) | Reviewer | Integration ID | First Library commit |
| --- | --- | --- | --- | --- |
| `aadf29c9-3ff5-45ff-8565-36282798a9dd` | [`Exponents/RepresentedIwahoriDecompositionStatements`](../../Langlands/Representation/Exponents/RepresentedIwahoriDecompositionStatements.md) | Reviewer 1765 | `db1284245f144c769f6c16a66f4ead12` | `db8d6b3d466f2fd453a4df4624ce6c90db8eed46` |
| `c1490da2-cd40-4732-8284-a6b1b31431b1` | [`Exponents/RepresentedCanonicalSectionStatements`](../../Langlands/Representation/Exponents/RepresentedCanonicalSectionStatements.md) | Reviewer 2002 | `368599f74e7e4f90bed318216e545714` | `e5365902d74534dbf1622c06e695dffdc128d723` |
| `889e2368-901e-47b6-93ee-03f51b89180a` | [`Exponents/RepresentedParabolicRemarksStatements`](../../Langlands/Representation/Exponents/RepresentedParabolicRemarksStatements.md) | Reviewer 2080 | `7089ce5a5f504943a0dca545d54cff63` | `e5365902d74534dbf1622c06e695dffdc128d723` |
| `aa6b8d06-0bbe-4b38-82d1-e35150507892` | [`CuspidalSupport/StandardLeviFixedVectorSupportStatements`](../../Langlands/Representation/CuspidalSupport/StandardLeviFixedVectorSupportStatements.md) | Reviewer 2137 | `d8a96d6ca1684994863067355c87cbc8` | `4f6abf4c7e19610e4d89edc9bf64b34ba1db9ff2` |
| `356c910f-d5d1-4be1-99a1-8073d255fdce` | [`Families/RenardFamilyFiniteTypeStatements`](../../Langlands/Representation/Families/RenardFamilyFiniteTypeStatements.md) | Reviewer 2228 | `e942655c5c534a44b6e12278151a150c` | `4f6abf4c7e19610e4d89edc9bf64b34ba1db9ff2` |
| `dc8565f1-e14e-450f-9afd-37929a85a691` | [`Jacquet/StandardIwahoriCornerInductionStatement`](../../Langlands/Representation/Jacquet/StandardIwahoriCornerInductionStatement.md) | Reviewer 2280 | `9ffb9d4188de4a49ab5850526300d2b3` | `e5365902d74534dbf1622c06e695dffdc128d723` |
| `45eed456-ee20-436b-9a93-df8d774b1cc3` | [`Jacquet/StandardIwahoriFixedVectorCategoryStatements`](../../Langlands/Representation/Jacquet/StandardIwahoriFixedVectorCategoryStatements.md) | Reviewer 2414 | `41cb7aa5b5e44bb99620962416f0f728` | `c40a01345b2f4172fa41e07ff31644b40e695003` |

The proof tasks of these units are numbered TaskHub tasks. Their identifiers, abbreviated
to eight hexadecimal digits, are: Task 6533 `78abf4a9`, Task 6534 `8cbd22a6`, Task 6594
`709f54f5`, Task 6596 `014c664a`, Task 6597 `2f229b34`, Task 6598 `c6988497`, Task 6599
`0b142d03`, Tasks 6560–6562 `5306e1c1`, `cf4ed536`, `f0a0ac6b`, Tasks 6565–6567
`f4a2d17b`, `a074d39f`, `5eefc120`, and Tasks 6639 `97df9594` and 6640 `ee12132d`. The
F3 statements have the proof tasks Task 6530
`16c7f6c2`, Task 6535 `595f5cb5` and Task 6536 `00506a19`, published by Worker 1222. The
F1 targets have Task 6571 `fcd6981d`, published by Worker 4. Worker 1222's
`Langlands.Hecke.LevelHeckeCornerComparisonStatement` (VI.9.4 Proposition row) has the
proof task Task 6607 `49480f41`, published by Worker 4 at Worker 1222's request.

The proof-status update of 14 November 2026, by Worker 4, checks every row with
status S against Library `a163f87c7a46874f408deed853c10c83207e9f69`. Every statement
named in these rows was compared with the Library theorems whose type is exactly that
statement, with no hypotheses. A statement is marked proved (P) only when such a
theorem exists. For each one Worker 4 read the theorem line and found no `sorry` or
`admit` in its file. The table gives the published `lean.proof@1` record for each proof.
Its Lean and Markdown files at the checked commit have the SHA256 recorded in the
record; integration IDs and commits come from the publication receipts. Proof modules
named by bare paths in the rows are under `Langlands/Representation/`. For the
statements of the other S rows, no such theorem exists at that commit.

| Row | Theorem | Proof module | Proof record | Integration ID | First Library commit |
| --- | --- | --- | --- | --- | --- |
| VI.3.1 Lemma | `rationalNormKernelConjugationLemma` | [RationalNormKernelConjugationLemmaProof](../../Langlands/Representation/CuspidalSupport/RationalNormKernelConjugationLemmaProof.md) | `355d9659-82e1-4d56-9346-46e232bfa549` | `b428ab050bc24ab19f528b9d2c08e3e9` | `cfedefb6` |
| VI.3.3 Remarks 1–2, VI.4.4 Remark | `rationalTwistStabilizerKernel` | [RationalTwistStabilizerKernelProof](../../Langlands/Representation/CuspidalSupport/RationalTwistStabilizerKernelProof.md) | `f44a7ea9-c613-438e-a248-f51d9aeea5ff` | `2494ca7cb0da44bfa1cdd649899966e0` | `cfedefb6` |
| VI.3.3 Remarks 1–2, VI.7.1 Example | `rationalInertiaOrbitTorus` | [RationalInertiaOrbitTorusProof](../../Langlands/Representation/CuspidalSupport/RationalInertiaOrbitTorusProof.md) | none found | none found | present in `ed924aef`, the oldest available snapshot |
| VI.4.2 Proposition, right modules | `rationalNormKernelHeckeModule` | [RationalNormKernelHeckeModuleProof](../../Langlands/Representation/CuspidalSupport/RationalNormKernelHeckeModuleProof.md) | `c3e7b89e-c57d-4d12-b3ed-0ba6b11793f7` | `9954f71e4aa448db92a949efb7a354df` | `cfedefb6` |
| VI.4.3 structure | `rationalNormKernelHecke_structure` | [RationalNormKernelHeckeStructureProof](../../Langlands/Representation/CuspidalSupport/RationalNormKernelHeckeStructureProof.md) | `0e0f27a5-54ef-426b-80c8-5f999c823bfb` | `091580cc12ae4ff5b1d1cf79a9990ca7` | `cfedefb6` |
| VI.4.4 Lemma | `rationalSummandStabilizerLemma` | [RationalSummandStabilizerLemmaProof](../../Langlands/Representation/CuspidalSupport/RationalSummandStabilizerLemmaProof.md) | `5a385fa6-7659-4677-a2fa-4963d591d191` | `3e028fa3f4264ccf9003c443082b1305` | `cfedefb6` |
| VI.4.4 Proposition, variety | `rationalSummandCenterVariety` | [RationalSummandCenterVarietyProof](../../Langlands/Representation/CuspidalSupport/RationalSummandCenterVarietyProof.md) | `e2bcc515-4286-4fc6-811e-adca5f3f1430` | `bf8ed6e90465484991fac591556b0205` | `b128d289` |
| VI.4.5 Corollary | `rationalInertiaBlockIndecomposable` | [RationalInertiaBlockIndecomposableProof](../../Langlands/Representation/CuspidalSupport/RationalInertiaBlockIndecomposableProof.md) | `4c442d9b-0942-4d4b-98fb-3dd31b52aca0` | `4901050802a54b50ba41b6c1ff506ee3` | `cfedefb6` |
| VI.5.4 Lemma | `standardWeylElementaryChain` | [StandardWeylElementaryChainProof](../../Langlands/GroupScheme/Rational/StandardWeylElementaryChainProof.md) | `a66d0eef-405c-437a-a09e-b40212b1efc0` | `92fa409efe644443ba2e9b53fc1dbfe1` | `cc5aa77f` |
| VI.7.1 Theorem, component variety | `bernsteinComponentVariety` | [BernsteinComponentVarietyProof](../../Langlands/Representation/CuspidalSupport/BernsteinComponentVarietyProof.md) | `bbeecc60-1577-44b0-9069-8080c8d23a2e` | `2e60d9747f954996affecfd8a571411e` | `cc5aa77f` |
| VI.9.6, equivalence of the two Theorems | `leviSecondAdjointnessContragredientEquivalence` | [LeviSecondAdjointnessContragredientEquivalenceProof](../../Langlands/Representation/Exponents/LeviSecondAdjointnessContragredientEquivalenceProof.md) | `7cb47525-676a-43c9-a974-3b24a42b13ef` | `a425984c172e44bda1719089cc0a60dc` | `cfedefb6` |
| VI.10.4 second Lemma | `inducedProgeneratorCenterInclusion` | [InducedProgeneratorCenterInclusionProof](../../Langlands/Representation/CuspidalSupport/InducedProgeneratorCenterInclusionProof.md) | `ac0cb1c2-b9e0-4431-b1ca-bcce3c72f904` | `b3fcf5ccf0734fab80cd4d3aba70bd93` | `51e4d897` |
| VI.10.4 third Lemma | `renardBimoduleFiltrationCentralizer` | [RenardBimoduleFiltrationCentralizerProof](../../Langlands/Algebra/RenardBimoduleFiltrationCentralizerProof.md) | `05f1eac2-0bf9-4ada-b151-6c724f24e2ed` | `e6993c432cba4b85a48c549ae15d87c2` | `cfedefb6` |

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
| VI.1.1 Remark, first sentence (`Ind_P^G` has a right adjoint) | 135 / 141 | `RP.LeviUnnormalizedInductionRightAdjointStatement` (`Exponents/RepresentedParabolicRemarksStatements`): for every actual rational parabolic, `Ind_P^G` (pullback along the Levi-point equivalence, inflation, then smooth induction from `P(F)`, with no normalizing character) satisfies `IsLeftAdjoint` | S: Task 6597. The statement asserts existence of a right adjoint; it does not name the source's construction from `I_M^P`, the pseudo-forgetful functor and a twist |
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
| VI.2.1 Remark 1, first block (standard parabolics suffice) | 137 / 143 | `RP.SupercuspidalStandardParabolicCriterionStatement` (`Exponents/RepresentedParabolicRemarksStatements`): for a maximal split torus `i` and a generic cocharacter `ν`, `RP.IsSupercuspidal A` holds iff the normalized Jacquet module of `A` vanishes along every proper actual rational parabolic whose parabolic and Levi subgroup functors are `standardParabolic i ν J` and `standardLevi i ν J` for some `J ⊆ Δ` | S: Task 6598 |
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
| VI.3.1 Lemma | 142–143 / 148–149 | `CS.RationalNormKernelConjugationLemmaStatement` | P: `rationalNormKernelConjugationLemma` (`CuspidalSupport/RationalNormKernelConjugationLemmaProof`; task 6665e450) |
| VI.3.2 Proposition (i)–(iii) | 143 / 149 | `CS.RationalNormKernelOrbitStatement`, `CS.RationalNormKernelFiniteRestrictionStatement`, `CS.RationalNormKernelTwistEquivalenceStatement` | P: `rationalNormKernelOrbit`, `rationalNormKernelFiniteRestriction`, `rationalNormKernelTwistEquivalence` |
| VI.3.3 Proposition (`W'` is `G`-invariant; `π(g) ∘ π(e_{σ_i}) = π(e_{σ_i^g}) ∘ π(g)`) | 145 / 151 | VI.3.1 (ii) above, `CompactIsotypicComplementStatement` (IV.1.5), and the covariance lemma `pointwiseFiniteSum_isotypic_covariant` (`CompactCoefficient/AmbientProjector`) | C: derived from these |
| (VI.3.3.1) decomposition | 145 / 151 | `CS.RationalCuspidalInertiaDecompositionStatement`; compact-restriction form `CS.RationalCompactRestrictionInertiaDecompositionStatement` | S: task 5c59bed4; compact-restriction form P |
| VI.3.3 Remarks 1–2 | 145 / 151 | `CS.RationalInertiaOrbitTorusStatement`, `CS.RationalTwistStabilizerKernelStatement`; Remark 2 from VI.3.2 (i), (iii) and VI.2.1 | P: `rationalInertiaOrbitTorus` (`CuspidalSupport/RationalInertiaOrbitTorusProof`; task f5aebf51) and `rationalTwistStabilizerKernel` (`CuspidalSupport/RationalTwistStabilizerKernelProof`; task e383bb3b); Remark 2 C |
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
| VI.4.2 Proposition | 152 / 158 | `CS.RationalNormKernelHeckeStatement`; right-module paragraphs `CS.RationalNormKernelHeckeModuleStatement` | P: `rationalNormKernelHecke_equiv`; modules P: `rationalNormKernelHeckeModule` (`CuspidalSupport/RationalNormKernelHeckeModuleProof`; task 31647676) |
| VI.4.3 structure (VI.4.3.1)–(VI.4.3.3) | 154–155 / 160–161 | `CS.RationalNormKernelHeckeStructureStatement` | P: `rationalNormKernelHecke_structure` (`CuspidalSupport/RationalNormKernelHeckeStructureProof`; task 7e3489cf) |
| VI.4.3 Lemma | 154 / 160 | `CS.RationalNormKernelEndSeparationStatement` | P: `rationalNormKernelEnd_separation` |
| VI.4.3 Corollary (i)–(ii) | 155 / 161 | `CS.RationalNormKernelEndDomainStatement`, `CS.RationalSummandEndCommutativeStatement` | P: `rationalNormKernelEnd_isDomain`, `rationalSummandEnd_commutative` |
| VI.4.4 Remark (the group `T`) | 157 / 163 | `CS.RationalTwistStabilizerKernelStatement` | P: `rationalTwistStabilizerKernel` (`CuspidalSupport/RationalTwistStabilizerKernelProof`; task e383bb3b) |
| VI.4.4 Lemma | 157 / 163 | `CS.RationalSummandStabilizerLemmaStatement` | P: `rationalSummandStabilizerLemma` (`CuspidalSupport/RationalSummandStabilizerLemmaProof`; task c6f40f07) |
| VI.4.4 Theorem | 158 / 164 | `CS.RationalSummandEndCenterStatement` | P: `rationalSummandEndCenter` |
| VI.4.4 Corollary | 159 / 165 | `CS.RationalSummandEndNoetherianStatement`; remark on modules `CS.RationalInertiaBlockNoetherianModulesStatement` | P: `rationalSummandEndNoetherian`; remark S: task cf9475ff |
| VI.4.4 Proposition | 159 / 165 | `CS.RationalSummandCenterGroupAlgebraStatement`, `CS.RationalSummandCenterVarietyStatement` | P: `rationalSummandCenterGroupAlgebra`; variety P: `rationalSummandCenterVariety` (`CuspidalSupport/RationalSummandCenterVarietyProof`; task 1347deec) |
| VI.4.5 Proposition | 160 / 166 | `CS.RationalInertiaBlockCenterEvaluationStatement`, `CS.RationalSummandBlockCenterStatement` | S: task 6b7a3e50 |
| VI.4.5 Corollary | 160 / 166 | `CS.RationalInertiaBlockIndecomposableStatement` | P: `rationalInertiaBlockIndecomposable` (`CuspidalSupport/RationalInertiaBlockIndecomposableProof`; task 6b7a3e50) |

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
| VI.5.4 Lemma (Bernstein–Zelevinsky, Lemma 2.17) | 175 / 181 | `Langlands.GroupScheme.StandardWeylElementaryChainStatement` (hypothesis `L ≠ G` added: the literal lemma fails for `L = M = G`, `w ≠ 1`) | P: `standardWeylElementaryChain` (`Langlands/GroupScheme/Rational/StandardWeylElementaryChainProof`; task 011068fd). `W(L, M)` and `l_S(M)` are written inline on the actual relative Weyl group; Worker 176, asked on 12 November 2026, has no named version and knows of none planned |
| VI.5.4 Corollary (i)–(iii) | 175 / 181 | `RP.LeviSupercuspidalInductionSameLeviStatement` | S: task fc21c11d |

## VI.6 Finiteness theorems

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| VI.6.1 Theorem (Jacquet lemma, admissible `V`) | 176 / 182 | Source scope: `RP.RepresentedJacquetLemmaStatement` (`Exponents/RepresentedIwahoriDecompositionStatements`): actual rational parabolics `P = MN`, `P̄ = MN̄` with the same Levi and `P(F) ∩ P̄(F) = M(F)`, every compact open `K = (K ∩ N̄(F))(K ∩ M(F))(K ∩ N(F))`, every admissible `V`; with the derived `RP.RepresentedIwahoriContractionStatement` (large powers of an element of `A^{++}` satisfy `IsIwahoriContraction`). Earlier forms: `RPF.GeneralizedJacquetLemmaStatement` (all smooth `V`, dynamic parabolics, `K` admitting an `M`-central `g` with `IsIwahoriContraction`) and `Langlands.Jacquet.fixedJacquetMap_surjective_of_iwahoriContraction` (`Jacquet/IwahoriContractionAdmissibility`, given one explicit contraction) | S: Task 6533 for both represented statements. The dynamic statement is S (task cac6f709); the earlier admissible form is P under its explicit contraction hypothesis |
| VI.6.1 Corollary | 176 / 182 | `RP.ArbitraryParabolicJacquetAdmissibilityStatement` | P: `arbitraryParabolicJacquetAdmissibility` |
| VI.6.1 Proposition and (VI.6.1.2) | 177 / 183 | Arbitrary parabolics: `RP.RepresentedCanonicalSectionStatement` (`Exponents/RepresentedCanonicalSectionStatements`; the setting of the VI.6.1 Theorem row, admissible `V`, one `ε ≤ 1` and one section `s` for all `t ∈ A^+(ε)`), with the derived `RP.RepresentedChamberIwahoriContractionStatement` (every `t ∈ A^+(ε)` satisfies `IsIwahoriContraction`). Standard parabolics: `J.StandardIwahoriCanonicalSectionStatement` (every compact open `K` with the ordered Iwahori decomposition); earlier `J.StandardCanonicalSectionStatement` | S: Task 6594 for the two represented statements; Task 6530 for the standard Iwahori-only statement. The earlier basis-member special case is P: `standardCanonicalSection` |
| VI.6.2 Lemma | 178 / 184 | `AG.DynamicInductionIrreducibleFiniteLengthStatement`; main assertion `RP.LeviInductionFiniteLengthStatement`, `AG.DynamicInductionFiniteLengthStatement` | S: tasks 02257068, 9b0a1303, 174d2de0 |
| VI.6.3 Theorem (Howe) | 178 / 184 | `AG.RationalPointsFiniteLengthAdmissibleStatement`, `Langlands.SmoothRep.RationalPointsFinitelyGeneratedAdmissibleFiniteLengthStatement` | S: tasks 96949545, 03a0d235; finite length ⇒ finite type is immediate (a finite-length object is Noetherian) |
| VI.6.3 Lemma | 178 / 184 | `Langlands.Jacquet.FixedVectorsGenerationStatement` (theorem `fixedVectorsGeneration`), `NormalizedJacquetBridge.normalized_generation` | P |
| VI.6.3 Proposition | 178 / 184 | `CS.SupercuspidalSubquotientFixedVectorsStatement` (every compact open `K`) | S: task e0efe074 |
| VI.6.3 Corollary | 179 / 185 | the VI.9.4 Corollary statement `J.StandardIwahoriFixedVectorSubquotientGenerationStatement` (no admissibility; `K` normal in `K₀` with Iwahori decompositions along every standard parabolic) | C: the admissible special case of this published statement, whose proof is open (Task 6535). The earlier basis-member version `J.StandardFixedVectorSubquotientGenerationStatement` remains S: task e8bd5ada |
| VI.6.4 (finite length of Jacquet modules) | 179 / 185 | `RP.LeviJacquetFiniteLengthStatement`, `AG.DynamicJacquetFiniteLengthStatement` | S: tasks 9b0a1303, 73e60be8 |

## VI.7 The Bernstein decomposition

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| VI.7.1 Lemma | 180 / 186 | `RP.LeviCuspidalSupportAssociationStatement` | S: task 9b0a1303 |
| VI.7.1 Proposition | 180 / 186 | `RP.LeviCuspidalSupportSurjectiveStatement`; finite fibres `CS.BernsteinCuspidalSupportFiniteFibreStatement` | S: tasks 9b0a1303, a955226a |
| VI.7.1 Example | 181 / 187 | variety part is the V.2.7 Corollary `CS.RationalInertiaOrbitTorusStatement` | C; P: `rationalInertiaOrbitTorus` (`CuspidalSupport/RationalInertiaOrbitTorusProof`; task f5aebf51) |
| VI.7.1 Theorem | 181 / 187 | `CS.BernsteinCuspidalDataVarietyStatements`, `CS.BernsteinComponentVarietyStatement` | `CS.BernsteinComponentVarietyStatement` P: `bernsteinComponentVariety` (`CuspidalSupport/BernsteinComponentVarietyProof`; task a955226a). `CS.BernsteinCuspidalDataVarietyStatements` is its conjunction with the open `CS.BernsteinCuspidalSupportFiniteFibreStatement` (VI.7.1 Proposition row), the other target of task a955226a: S |
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
| VI.9.1 Theorem (generalized Jacquet lemma) | 195 / 201 | Source scope: `RP.RepresentedGeneralizedJacquetLemmaStatement` (`Exponents/RepresentedIwahoriDecompositionStatements`; the setting of the VI.6.1 Theorem row, every smooth `V`). Dynamic form: `RPF.GeneralizedJacquetLemmaStatement` (dynamic parabolics; `K` admitting an `M`-central `g` with `IsIwahoriContraction`) | S: Task 6534; dynamic form S (task cac6f709) |
| VI.9.1 first Lemma (`V(N) ∩ V^K = ⋃ ker A^i`) | 196 / 202 | `powerKernelSup_eq_ker_of_iwahoriContraction` (`Jacquet/IwahoriContractionAdmissibility`), `fixedJacquetMap_kernel_locally_nilpotent` (`Jacquet/CompressionLocalization`) | P |
| VI.9.1 second Lemma (localization) | 196 / 202 | `compressionJacquetLocalizationEquiv`, `localizationEquivOfKernelExhaustion` | D / P (proved construction) |
| VI.9.1 Proposition (uniform stabilization) | 197 / 203 | Arbitrary parabolics: `RP.RepresentedUniformCompressionStabilizationStatement` (`Exponents/RepresentedCanonicalSectionStatements`; every compact open `K` and every `M(F)`-central `g` with `IsIwahoriContraction`; `b` chosen after `K` and `g`, for all smooth `V`; it adds the conclusions `ker j = V_0^K` and `j` bijective on `V_*^K` drawn at the end of the proof of the Theorem). Dynamic form: `RPF.UniformCompressionStabilizationStatement` (`b` chosen after `χ`, `K` and `g`) | S: Task 6596; dynamic form S (task 47e556e6). C for the source's class of `K`: by `RP.RepresentedIwahoriContractionStatement`, every `K` with an Iwahori decomposition admits such a `g`. The source's `b = b(G, K)` follows from the bound clauses of the next row together with VI.2.3 |
| VI.9.1 Proposition, localization at `A` is `(V^K_*, A)` | 197 / 203 | the proved C.II theorem `Langlands.Renard.EndomorphismLocalization.stablePowerImageStatement` (`Algebra/RenardLocalizationStabilityProof`), for any endomorphism with a stable power | C: derived from that theorem and the Proposition's stable power `A^b`; the application to `compressedAction` is not published as a separate statement |
| VI.9.1 Proposition, `b ≤ c(G, K)`; Remarks 1–3 | 197–198 / 203–204 | `RPF.GeneralizedJacquetRemarksStatement` (bound, Remarks 1–2, dynamic parabolics), `RP.GeneralizedJacquetContractingRangeStatement` (Remark 3) (`Exponents/GeneralizedJacquetRemarksStatements`, published); bound and Remarks 1–2 along actual rational parabolics: `RP.RepresentedGeneralizedJacquetRemarksStatement` (`Exponents/RepresentedCanonicalSectionStatements`) | S: task 7a03c792 for the two published statements; Task 6596 for the represented statement |
| VI.9.2 (VI.9.2.2) stability for the universal induced family | 198–199 / 204–205 | `Langlands.Plancherel.RationalSupercuspidalJacquetFamilyFiniteStatement` and the VI.9.1–VI.9.3 map (`uniform-compression-progress.md`) | St: step of the VI.9.1 Proposition; Jacquet-family finiteness P |
| VI.9.3 extension to all smooth representations | 200 / 206 | conditional helpers in the VI.9.1–VI.9.3 map | St |
| VI.9.4 Corollary | 201 / 207 | `J.StandardIwahoriFixedVectorSubquotientGenerationStatement`; earlier `J.StandardFixedVectorSubquotientGenerationStatement` | S: Task 6535 for the Iwahori-only statement, which uses the source's conditions on `K`. Task e8bd5ada concerns the earlier basis-member version |
| VI.9.4 Proposition | 201 / 207 | Over the measure-free algebra: `J.StandardIwahoriFixedVectorHeckeEquivalenceStatement`; earlier `J.StandardFixedVectorHeckeEquivalenceStatement` (modules over the measure-free `LevelHeckeAlgebra ℂ K`). Comparison of algebras: `Langlands.Hecke.LevelHeckeCornerComparisonStatement` (`Hecke/LevelHeckeCornerComparisonStatement`, Worker 1222: a product-preserving linear bijection `LevelHeckeAlgebra ℂ K ≃ Corner μ K hK` with `e(a)(x) = μ(K)⁻¹ a(xK)`, compatible with the two actions on `V^K`). Over the Haar-measure `H(G, K)` with the inverse functor: `J.StandardIwahoriCornerInductionEquivalenceStatement` (`Jacquet/StandardIwahoriCornerInductionStatement`; see the VI.10.6 Proposition (ii) row) | S: Task 6536 for the Iwahori-only statement; task e8bd5ada concerns the earlier basis-member version. Task 6599 for the corner-induction statement. The comparison statement has an open proof: Task 6607 |
| VI.9.5 (`r_P^G` preserves `B`-admissibility) | 201 / 207 | `AF.JacquetAdmissibleStatement`; reduction `AF.JacquetAdmissibleReductionStatement` | S: task 8057266d; reduction P |
| VI.9.6 first Theorem (second adjointness) | 201 / 207 | `RP.LeviSecondAdjointnessStatement` | S: tasks c0fa1878, eac5190f |
| VI.9.6 second Theorem (`r_{P̄}^G π̃ ≅ (r_P^G π)~`) and the equivalence of the two | 201–202 / 207–208 | `RP.LeviJacquetContragredientStatement`, `RP.LeviSecondAdjointnessContragredientEquivalenceStatement` | `RP.LeviJacquetContragredientStatement` S: task c0fa1878; the equivalence P: `leviSecondAdjointnessContragredientEquivalence` (`Exponents/LeviSecondAdjointnessContragredientEquivalenceProof`; task 3ec57776) |
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
| VI.10.4 second Lemma (`ℨ_Ω ⊂ ℨ_D`) | 211 / 217 | `RP.InducedProgeneratorCenterInclusionStatement` | P: `inducedProgeneratorCenterInclusion` (`CuspidalSupport/InducedProgeneratorCenterInclusionProof`; task 03c64afa) |
| VI.10.4 `ℨ_Ω ⊂ ℨ_D^{W(D)}`, `ℨ_Ω = ℨ_D^{W(D)}` | 211–212 / 217–218 | none | St: steps of the VI.10.4 Theorem |
| VI.10.4 third Lemma (centralizer for filtered bimodules) | 211–212 / 217–218 | `Langlands.Algebra.RenardBimoduleFiltrationCentralizerStatement` | P: `renardBimoduleFiltrationCentralizer` (`Langlands/Algebra/RenardBimoduleFiltrationCentralizerProof`; task 74deb29a) |
| VI.10.4 Theorem | 212 / 218 | `CS.BernsteinCenterFunctionsStatements` (with `CS.BernsteinBlockCenterFunctionsStatement`, `CS.BernsteinCentralIdempotentFunctionStatement`) | S: task c4d4541b |
| VI.10.4 Corollary, Remarks 1–3 | 212 / 218 | `CS.BernsteinBlockCenterNoetherianStatement`, `CS.BernsteinBlockIndecomposableStatement`; Remarks 1–2 in `CS.BernsteinCenterFunctionsStatements` | S: tasks 80d07293, c4d4541b |
| VI.10.5 Proposition | 213 / 219 | `RP.HarishChandraHomomorphismStatement` | S: task 03c64afa; finiteness of `i_{MG}` as a morphism of varieties is stated only through its consequence (finite generation) |
| VI.10.6 Theorem, Proposition | 213–214 / 219–220 | `CS.CompactOpenInertialFinitenessStatement`, `J.FixedVectorCategoryStatements` | S: tasks f504c0e1, 423c3289 |
| VI.10.6 Proposition (i), the decomposition `M(G)_K = ∏_{s ∈ B(G)_K} M(G)_s`, and (iii)–(iv) for the source's class of `K` | 214 / 220 | `J.StandardIwahoriFixedVectorBlockDecompositionStatement` (a smooth representation is generated by its `K`-fixed vectors iff it is a coproduct of its components in the Bernstein blocks indexed by `B(G)_K`), `J.StandardIwahoriFixedVectorCategoryStatement` ((iii)–(iv) with only the ordered Iwahori decompositions on `K`), and the proved implication `J.fixedVectorCategoryStatements_of_standardIwahori` to the earlier basis-member conclusion (`Jacquet/StandardIwahoriFixedVectorCategoryStatements`) | S: published candidate `45eed456` (Reviewer 2414); Task 6639 for the block decomposition statement, Task 6640 for (iii)–(iv) |
| VI.10.6 Proposition (ii) (inverse `M ↦ H(G) ⊗_{H(G,K)} M`) | 214 / 220 | `J.StandardIwahoriCornerInductionEquivalenceStatement` (`Jacquet/StandardIwahoriCornerInductionStatement`; the Haar Hecke algebra `H(G)`, its corner `H(G, K) = e_K H(G) e_K`, the III.1.4 functor, the I.3.1 corner functor and the I.3.2 induction functor) | S: Task 6599 |
| VI.10.6 Corollary (`B(M)_{K_M} = i_{MG}^{-1}(B(G)_K)`) | 215 / 221 | `CS.StandardLeviCompactInheritanceStatement` (the hypotheses on `K` pass to `K ∩ M`), `CS.StandardRepresentativeFixedVectorCriterionStatement`, `CS.StandardLeviFixedVectorSupportStatement` (`CuspidalSupport/StandardLeviFixedVectorSupportStatements`; standard Levi subgroups `M_J`; `B(M)` and `i_{MG}` through representatives, as in `CS.BernsteinInductionRestrictionStatement`) | S: Tasks 6560, 6561, 6562. `B(M)` as a type and `i_{MG}` as a function are not defined |
| VI.10.7 Lemma, Theorem | 215 / 221 | `CS.FiniteTypeComponentCharacterizationStatement`, `RP.FiniteTypeCenterAdmissibleStatement` | S: task f504c0e1 |
| VI.10.7 Corollary | 216 / 222 | `RP.HeckeAlgebraCenterFiniteStatement` | S: task aea42eff |
| VI.10.7 Proposition | 216 / 222 | `CS.FiniteTypeComponentCharacterizationStatement` | S: task f504c0e1 |
| VI.10.7 Variant (`(G, B)`-modules) | 217 / 223 | `AF.FamilyFiniteTypeCenterAdmissibleStatement`, `AF.FamilyFiniteTypeComponentCharacterizationStatement`, `AF.FamilyLeviInductionFiniteTypeStatement` (`Families/RenardFamilyFiniteTypeStatements`; `ℨ(G)` is the published categorical centre acting on the underlying smooth complex representation; components enter through irreducible subquotients) | S: Tasks 6565, 6566, 6567. The components `E_𝔰` and the algebra `B ⊗_ℂ ℨ(G)` are not constructed |
| VI.10.8 Theorem | 217 / 223 | `RP.CenterFiniteHoweStatement` | S: task f504c0e1 |

## VI.11 Notes on Chapter VI

| Item | Pages | Status |
| --- | --- | --- |
| VI.11 notes | 217–218 / 223–224 | X: attributions and references (Harish-Chandra, Jacquet, Bernstein, Bernstein–Zelevinsky [5], Casselman [20], DeBacker [23], notes [38]). The notes repeat that the second adjointness theorem is equivalent to a strong form of Casselman duality without admissibility; this is the VI.9.6 equivalence stated above. |

## Framework comparisons used above

These comparisons record the scope and proof obligations of the rows above. The
gap update of 14 November 2026 states the comparisons F2 and F4 and lists the
proof tasks of F1 and F3. All their statements have open proofs.

- **F1. Bernstein blocks.** The published blocks (`BernsteinBlock`,
  `BernsteinSaturatedBlock`) use the induction-occurrence support relation. The
  comparison targets are in `CuspidalSupport/BernsteinSupportComparison` (statements
  parametrized by the standard family). Existence of an induction presentation,
  `CS.BernsteinCuspidalSupportExistenceStatement`, is proved
  (`bernsteinCuspidalSupportExistence`). The following are proved only conditionally,
  on the represented VI.5.4 statement
  `RP.LeviSupercuspidalInductionAssociationStatement`:
  association, `CS.BernsteinCuspidalSupportAssociationStatement`
  (`bernsteinCuspidalSupportAssociation_of_represented`), and
  `CS.BernsteinAssociatedSupportInvarianceStatement`
  (`bernsteinAssociatedSupportInvariance_of_represented`). Uniqueness of the inertial
  support, `CS.BernsteinInertialSupportUniquenessStatement`, follows from association
  (`bernsteinInertialSupportUniqueness_of_association`). The comparison with Renard's
  Jacquet-defined support, `CS.BernsteinInductionJacquetSupportComparisonStatement`,
  has no proof. Task 6571 asks for unconditional proofs of association, invariance,
  uniqueness and the comparison. The rows of VI.7 and VI.10 that use the published
  blocks depend on these comparisons.
- **F2. Iwahori decompositions and contracting elements: statement gap closed.**
  The earlier VI.9.1 statements and VI.6.1 Theorem coverage use dynamic parabolics
  and a compact open `K` with an `M`-central contracting `g` (`IsIwahoriContraction`).
  The source allows every `K` with an Iwahori decomposition along an arbitrary
  parabolic. The represented statements of candidates `aadf29c9` and `c1490da2`
  (unit table above) are stated along every actual rational parabolic for such `K`.
  `RP.RepresentedIwahoriContractionStatement` and
  `RP.RepresentedChamberIwahoriContractionStatement` assert that such `K` admit
  contracting elements. Their proofs are open: Tasks 6533, 6534, 6594 and 6596.
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
  statements. Their proofs are Tasks 6530, 6535 and 6536, published by Worker 1222.
  The arbitrary-parabolic version of the VI.6.1 Proposition is stated under F2. The
  Haar-Hecke comparison and the inverse functor are stated in the VI.9.4 Proposition
  row.
- **F4. Represented versus standard parabolics.** For supercuspidality, the
  comparison is `RP.SupercuspidalStandardParabolicCriterionStatement` (VI.2.1
  Remark 1 row; Task 6598).

## Genuine gaps of Chapter VI

The earlier audit listed seven gaps. Each one is now stated. The update of
14 November 2026 records the statements and their proof tasks below. It does not
claim that Chapter VI has no other gaps. The individual rows remain authoritative.

1. VI.1.1 Remark, first sentence (right adjoint of `Ind_P^G`):
   `RP.LeviUnnormalizedInductionRightAdjointStatement`, Task 6597. The source's
   construction of the adjoint is not named.
2. VI.2.1, first Remark of the first block (standard parabolics suffice):
   `RP.SupercuspidalStandardParabolicCriterionStatement`, Task 6598.
3. VI.10.2 Theorem: the quasi-inverse `M ↦ M ⊗_{R_Ω} Π_Ω` was not identified in the
   pinned Library. It is now stated by the published
   `BernsteinBlockTensorQuasiInverseStatement` (candidate `a4b157d0`, Library `79de65ce`),
   with proof Task 5686.
4. VI.10.6 Corollary: `CS.StandardLeviCompactInheritanceStatement`,
   `CS.StandardRepresentativeFixedVectorCriterionStatement` and
   `CS.StandardLeviFixedVectorSupportStatement`, Tasks 6560–6562, for standard Levi
   subgroups and through representatives of `B(M)`.
5. VI.10.7 Variant: `AF.FamilyFiniteTypeCenterAdmissibleStatement`,
   `AF.FamilyFiniteTypeComponentCharacterizationStatement` and
   `AF.FamilyLeviInductionFiniteTypeStatement`, Tasks 6565–6567.
6. VI.9.4 Proposition: `Langlands.Hecke.LevelHeckeCornerComparisonStatement` (Worker
   1222; Task 6607) and `J.StandardIwahoriCornerInductionEquivalenceStatement`
   (VI.10.6 Proposition (ii)), Task 6599.
7. The arbitrary-parabolic scope of VI.6.1 (Theorem and Proposition) and VI.9.1: the
   represented statements of F2, Tasks 6533, 6534, 6594 and 6596. The source's class
   of `K` for standard parabolics in VI.6.1 Proposition, VI.6.3 Corollary and VI.9.4:
   the F3 targets, Tasks 6530, 6535 and 6536. The block comparison F1: Task 6571.

The update also states VI.10.6 Proposition (i), the decomposition
`M(G)_K = ∏_{s ∈ B(G)_K} M(G)_s`, which the earlier statement
`J.FixedVectorCategoryStatements` does not contain. It is the published candidate
`45eed456`, with proof Tasks 6639 and 6640.

The VI.5.4 Lemma, unstated before this audit, is now the published
`StandardWeylElementaryChainStatement`, proved by `standardWeylElementaryChain`
(proof-status update above). The VI.9.1 bound and Remarks, the remaining
gap found by this audit, are now stated in the published module
`Exponents/GeneralizedJacquetRemarksStatements`, with proof task 7a03c792.
