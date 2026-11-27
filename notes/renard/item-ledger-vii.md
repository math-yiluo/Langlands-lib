# Renard 2026, Chapter VII: item-by-item coverage ledger

This note is the Chapter VII part of the item ledger of the whole book
([coverage.md](coverage.md)), in the format of the
[Chapter VI item ledger](item-ledger-vi.md). It lists every headed item of Chapter VII
and the unheaded assertions found so far. For each row it gives the printed and PDF
pages, the Lean declarations, and the implementation status with its evidence. It
declares no section or chapter complete.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. Printed page
numbers are given first and PDF page numbers second. Library facts refer to commit
`16c60abdc019c1181a2734d3052305ec3d6e7b85`, except for the four proof updates for
VII.3.4–VII.3.5 below, checked on 14 November 2026 at Library
`179f569bc35e58b829420ce0590c9f4d0ff43c21`, and for the VII.1.3 Corollary row and gap 2,
checked on 14 November 2026 at Library `c0debd6f4dd02fdd68d70811cf610906b945a962`, and
for the proof-status update described below, checked at Library
`a163f87c7a46874f408deed853c10c83207e9f69`. The VII.1.2 row and source issue I2
were checked on 19 November 2026 at Library
`ecb96e554fed652972a5c0308d69b041f6bc54e4`. Other statuses retain their historical
survey scope. The VII.1.2 and VII.1.3 additions below were checked on 20 November 2026
at Library `7ae0d83b7cb2ad9aaca52ada487b3a5d3314323a`, with five further statement
pairs checked at `edf9646441fdf5d75d692913b8928b89b9d92538`. The status codes and the method of checking are those of the Chapter VI ledger.
The VII.4 proof steps, conditional proofs and source issues below were checked
on 20 November 2026 at Library `5704217a2667191d63b37f0e85a2da41c15b21d2`.
The four statement publications below were checked
on 21 November 2026 at Library `a11d1e75f52192f694c9901f4b7fd7098b0f8ff9`.
The VII.1 and VII.2 proofs and applications listed below, and the proof of
(VII.4.1.3), were checked at Library `2f86a99eb5616254ac5b9c399603c9bbbea15f7a`.
All declarations below are in `Langlands.Aubert.General.RepresentedParabolic`
(abbreviated `RP`) unless another namespace is written. The focused source maps
[root-exponent-tempered-progress](root-exponent-tempered-progress.md) and
[parabolic-functors-tempered-progress](parabolic-functors-tempered-progress.md) give
more detail for VII.1–VII.2.

The proof-status update of 14 November 2026 checks every row with status S
against Library `a163f87c7a46874f408deed853c10c83207e9f69`, by the method stated in the
Chapter VI ledger: a statement is marked proved (P) only when a Library theorem with no
hypotheses has exactly that statement as its type. It changes the rows VII.1.3
Corollary, VII.2.1 Remark 2, VII.2.6 Theorem and Remark, VII.3.1 extremes, VII.3.5
opening assertion and VII.4.1 Lemma, gap 2 and the source issue I1. Proof modules named
by bare paths are under `Langlands/Representation/`. For each new proof the
theorem line was read; its file has no `sorry` or `admit`. The new proofs, with the Library
commit where each first appeared:

| Row | Theorem | Proof module | First Library commit |
| --- | --- | --- | --- |
| VII.2.1 Remark 2 | `squareIntegrableNormalizedTempered` | [SquareIntegrableNormalizedTemperedProof](../../Langlands/Representation/Exponents/SquareIntegrableNormalizedTemperedProof.md) | `17dd94ea` |
| VII.2.6 Theorem, uniqueness | `temperedIrreducibleDiscreteSeriesUniqueness` | [TemperedIrreducibleDiscreteSeriesUniquenessProof](../../Langlands/Representation/Exponents/TemperedIrreducibleDiscreteSeriesUniquenessProof.md) | `cfedefb6` |
| VII.2.6 Remark | `temperedReducibleNotUnitarizable` | [TemperedReducibleNotUnitarizableProof](../../Langlands/Representation/Exponents/TemperedReducibleNotUnitarizableProof.md) | `730bd1f2` |
| VII.3.1 extremes | `bruhatIdentityExtremes` | [BruhatIdentityExtremesProof](../../Langlands/Representation/Exponents/BruhatIdentityExtremesProof.md) | `730bd1f2` |
| VII.3.5 opening assertion, minimal `M` | `minimalParabolicDistanceLength` | [MinimalParabolicDistanceLengthProof](../../Langlands/GroupScheme/Rational/MinimalParabolicDistanceLengthProof.md) | `730bd1f2` |
| VII.4.1 Lemma | `langlandsTripletOppositeRegularity` | [LanglandsTripletRegularityProof](../../Langlands/Representation/LanglandsClassification/LanglandsTripletRegularityProof.md) | `b128d289` |

The following Lean and Markdown statement pairs entered the Library at
`032961776f43ccd672c6266d265a9c644faeba13`. They match the files as first
checked. The last column gives the proof the Library has now.

| Coverage | Published statement | Proof in the Library |
| --- | --- | --- |
| VII.2.4 standard vanishing test | [`UnitaryJacquetVanishingStandardReductionStatement`](../../Langlands/Representation/Exponents/UnitaryJacquetVanishingStandardReductionStatement.md) | [`unitaryJacquetVanishingStandardReduction`](../../Langlands/Representation/Exponents/UnitaryJacquetVanishingStandardReductionProof.md) |
| VII.2.6 standard embedding witness | [`DiscreteSeriesEmbeddingStandardReductionStatement`](../../Langlands/Representation/Exponents/DiscreteSeriesEmbeddingStandardReductionStatement.md) | [`discreteSeriesEmbeddingStandardReduction`](../../Langlands/Representation/Exponents/DiscreteSeriesEmbeddingStandardReductionProof.md) |
| VII.2.4 and VII.2.6 from building data | [`TemperedDiscreteSeriesFromBuildingStatement`](../../Langlands/Representation/Exponents/TemperedDiscreteSeriesFromBuildingStatement.md) | [`temperedDiscreteSeriesFromBuilding`](../../Langlands/Representation/Exponents/TemperedDiscreteSeriesFromBuildingProof.md) |
| (VII.4.1.3) ambient displacement | [`DominantWeylDisplacementStatement`](../../Langlands/Representation/LanglandsClassification/DominantWeylDisplacementStatement.md) | [`Langlands.GroupScheme.dominantWeylDisplacement`](../../Langlands/Representation/LanglandsClassification/DominantWeylDisplacementProof.md) |

Most Chapter VII statements are **derived formulations** for the represented-parabolic
interface. They range over arbitrary actual rational parabolics instead of standard ones,
and they test cone conditions through compatible root presentations
(`ParabolicRootPresentation`). Two forms of this test occur, and V1 below compares
them. The published normalized temperedness predicate `IsNormalizedExponentTempered`
requires, at every parabolic, rational Levi and split-component triple, both the
existence of a compatible presentation and the cone condition for every such
presentation (`SatisfiesNormalizedExponentConeCondition`, `Exponents/ArbitraryParabolicTempered`).
The Casselman criterion `RP.ArbitraryParabolicCasselmanCriterionStatement`, by contrast,
only tests every supplied presentation and requires none to exist. Each statement's
Markdown documents its departures. The rows below name the departures that change
mathematical content.

### Checked applications of the building proofs

Lean checks each term in the table against the indicated exact proposition
at independent field and representation-carrier universes `u` and `v`.
Rows marked **A** refer to these applications of named Library theorems.

| Exact proposition in `RP` | Lean term with `RP` open |
| --- | --- |
| `ArbitraryParabolicCasselmanCriterionStatement.{u, v}` | `casselmanFromBuilding Langlands.Geometry.Building.bruhatTitsAvailability` |
| `MaximalLeviSupercuspidalReducibilityStatement.{u, v}` | `maximalLeviReducibilityFromJointBasis Langlands.BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence` |
| `TemperedSquareIntegrableUnitaryPartStatement.{u, v}` | `(temperedDiscreteSeriesFromBuilding Langlands.Geometry.Building.groupAxiomsExistence).1` |
| `TemperedIrreducibleDiscreteSeriesStatement.{u, v}` | `(temperedDiscreteSeriesFromBuilding Langlands.Geometry.Building.groupAxiomsExistence).2.1` |
| `TemperedIrreducibleUnitarizableStatement.{u, v}` | `(temperedDiscreteSeriesFromBuilding Langlands.Geometry.Building.groupAxiomsExistence).2.2` |

`casselmanFromBuilding` uses the common Cartan and Iwahori basis for
sufficiency and pairs it with the independent necessity proof.
`maximalLeviReducibilityFromJointBasis` uses the joint basis for admissibility
and compact support, and derives fixed-level finiteness as used in VI.3.4.
The premises are proved by
[`bruhatTitsAvailability`](../../Langlands/Geometry/Building/BruhatTitsAvailabilityProof.md)
and [`jointSpecialCompactBasisExistence`](../../Langlands/BruhatTits/SpecialCompact/JointBasisProof.md).

`temperedDiscreteSeriesFromBuilding` obtains Casselman's criterion from
one-group building existence via `bruhatTitsAvailabilityReduction`. For VII.2.4
it identifies strict positivity of normalized Jacquet exponents with vanishing
of the unitary parts at all proper represented rational parabolics. For VII.2.6
it uses an irreducible quotient of the unitary Jacquet part at a minimal
parabolic with nonzero unitary part and obtains an embedding by Frobenius
reciprocity. The corollary induces an invariant positive form from the
square-integrable representation of the Levi and restricts it along the
embedding. The one-group premise is proved by
[`groupAxiomsExistence`](../../Langlands/Geometry/Building/GroupAxiomsExistenceProof.md).

## VII.1 Casselman's criterion and applications

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| VII.1.1 characteristic spaces `(r_P^G V)_χ`, normalized exponents, `Exp(A, r_P^G V)` | 220 / 226 | `normalizedJacquetWeightSpace`, `IsNormalizedJacquetExponent`, `normalizedJacquetExponents` (`Exponents/ArbitraryParabolic`) | D |
| (VII.1.1.1) and finiteness of `Exp` in finite length | 220 / 226 | `RP.ArbitraryParabolicExponentStatement` | P: `arbitraryParabolicExponent` |
| VII.1.1 Remark (`P = G`) | 220 / 226 | `RP.ArbitraryParabolicExponentStatement` | P |
| VII.1.1 Lemma (i)–(ii) | 220–221 / 226–227 | `RP.ArbitraryParabolicExponentStatement` | P |
| VII.1.2 Theorem (Casselman's criterion) | 221 / 227 | `RP.ArbitraryParabolicCasselmanCriterionStatement`, with necessity `RP.ArbitraryParabolicCasselmanNecessityStatement` | A. Necessity is also proved by `arbitraryParabolicCasselmanNecessity`. The corrected condition is the strictly positive root cone from the final decay test. The printed coroot-chamber necessity fails for an actual square-integrable representation of `Sp₄(ℚ₃)` (I2) |
| VII.1.2 Theorem with Bruhat–Tits availability | 221–224 / 227–230 | `RP.CasselmanFromBuildingStatement` | P by `casselmanFromBuilding`. Bruhat–Tits availability gives the joint Cartan and Iwahori basis used for sufficiency |
| VII.1.2 first paragraph of the proof, reduction to the central uniformizer lattice | 221 / 227 | `RP.CentralUniformizerSquareIntegrabilityStatement` | P by `centralUniformizerSquareIntegrability`. The evaluated cocharacter lattice is closed, its quotient in the full center is compact, and square integrability modulo the two central subgroups is equivalent for arbitrary quotient Haar normalizations |
| VII.1.2 Cartan refinement after (VII.1.2.1) and labelled series preceding (VII.1.2.2) | 221–222 / 227–228 | `Langlands.cartanLatticeL2`, `Langlands.countableCellLpUpper`, `Langlands.HarishChandraSchwartz.CartanLabelledSeriesStatement` | P for the overlap-tolerant upper estimate on the full central quotient, checked at Library `b0b4deb8c936156b61ecb9730f7ff1ebb8ff3f5c`. `cartanLabelledSeries` proves the two-sided comparison on the uniformizer quotient with disjoint coarse cells and at most \(r^2\) fine labels per point. Under the cover assumption the integral and labelled series are finite together (I3) |
| VII.1.2 ambient Haar weights in the series preceding (VII.1.2.2) | 221–222 / 227–228 | `Langlands.HarishChandraSchwartz.CentralUniformizerCellVolumeStatement` | P by `centralUniformizerCellVolume`. Each compact-open double coset embeds in the central uniformizer quotient and keeps its ambient Haar mass for the quotient measure compatible with counting measure on the lattice |
| VII.1.2 partition by the \(S_M(n)\) after (VII.1.2.2) | 222–223 / 228–229 | `Langlands.GroupScheme.CocharacterCone.ThresholdPartitionStatement` | P by `Langlands.GroupScheme.CocharacterCone.thresholdPartition`. A finite residue set and exponents along diagonal cocharacter rays parameterize the integral cone modulo its annihilator. Bounded and unbounded exponents give the disjoint threshold pieces (I7) |
| VII.1.2 double-coset volume following (VII.1.2.2) | 222–223 / 228–229 | `Langlands.Aubert.General.standardBasisMember_rayIndex`, `Langlands.Aubert.General.RationalPointFamily.rationalLatticeQuotientVolume`, `Langlands.HarishChandraSchwartz.IwahoriLeviDoubleCosetVolumeStatement` | P for the finite-translate upper bound on the full central quotient, checked at Library `24390f9f6d7a3b7df9e5b9dd4d6e79e178c8ac85`. `iwahoriLeviDoubleCosetVolume` proves the exact formula including the Levi index under Iwahori factorization, ambient injectivity and the two radical contractions (I4) |
| VII.1.3 opening paragraph, standard Levi transporters | 224 / 230 | `Langlands.GroupScheme.StandardLeviTransporterCosetsStatement` and `Langlands.GroupScheme.MaximalStandardLeviPointCosetsStatement` | `standardLeviTransporterCosets` proves the comparison of left coset sets. The second proposition (S) uses the comparison and the Weyl-side V.4.8 result for the two-coset characterization of maximal proper standard parabolics and the conjugate parabolic for a representative of the second coset (I5) |
| VII.1.3 Theorem | 224 / 230 | `RP.MaximalLeviSupercuspidalReducibilityStatement` and the reduction `RP.MaximalLeviSupercuspidalReducibilityFromInputsStatement` | A for the criterion and P for the reduction. The represented criterion uses arbitrary maximal rational parabolics and expresses the inducing-twist condition through an element of \(G(F)\) that normalizes the Levi |
| VII.1.3 Theorem with a joint compact basis | 224–226 / 230–232 | `RP.MaximalLeviReducibilityFromJointBasisStatement` | P by `maximalLeviReducibilityFromJointBasis`. The joint special-compact basis gives admissibility, compact support and fixed-level VI.3.4 finiteness at the induced carrier universe |
| VII.1.3 Corollary (i)–(iii) | 226–227 / 232–233 | `RP.MaximalLeviBlockStatements`; `RP.MaximalLeviBlockProjectionEquivalenceStatement` | S. The first statement expresses (ii) as Jacquet nonvanishing and (iii) as full faithfulness and essential surjectivity of induction. The second statement names `r_D` using a left adjoint to the block inclusion. It asserts projection existence, faithfulness of `r_D`, invertibility of `π → i_P^G r_D(π)` and the equivalence with inverse `i_P^G`. It first appeared at Library commit `c40a0134` |

These four statement pairs first entered the Library at
`95d37e11bd46972d484c6fc9e6b864ff7625cf9e`. The Lean and Markdown files at
the checked commit match the files as first checked.

| Statement explanation | Proof in the Library |
| --- | --- |
| [Casselman criterion with building availability](../../Langlands/Representation/Exponents/CasselmanFromBuildingStatement.md) | [`casselmanFromBuilding`](../../Langlands/Representation/Exponents/CasselmanFromBuildingProof.md) |
| [Central uniformizer lattice](../../Langlands/Representation/Exponents/CentralUniformizerSquareIntegrabilityStatement.md) | [`centralUniformizerSquareIntegrability`](../../Langlands/Representation/Exponents/CentralUniformizerSquareIntegrabilityProof.md) |
| [Standard Levi transporter cosets](../../Langlands/GroupScheme/Rational/StandardLeviTransporterCosetsStatement.md) | [`Langlands.GroupScheme.standardLeviTransporterCosets`](../../Langlands/GroupScheme/Rational/StandardLeviTransporterCosetsProof.md) |
| [Maximal standard Levi point cosets](../../Langlands/GroupScheme/Rational/MaximalStandardLeviPointCosetsStatement.md) | S |

The following five statements first entered the Library at
`6e9e589baa721ce995563f73f648b6f4e45718a1`. Their Lean and Markdown files
match the files as first checked.

| Statement explanation | Proof in the Library |
| --- | --- |
| [Labelled Cartan series](../../Langlands/HarmonicAnalysis/HarishChandraSchwartz/CartanLabelledSeriesStatement.md) | [`Langlands.HarishChandraSchwartz.cartanLabelledSeries`](../../Langlands/HarmonicAnalysis/HarishChandraSchwartz/CartanLabelledSeriesProof.md) |
| [Uniformizer quotient cell volume](../../Langlands/HarmonicAnalysis/HarishChandraSchwartz/CentralUniformizerCellVolumeStatement.md) | [`Langlands.HarishChandraSchwartz.centralUniformizerCellVolume`](../../Langlands/HarmonicAnalysis/HarishChandraSchwartz/CentralUniformizerCellVolumeProof.md) |
| [Cocharacter cone threshold partition](../../Langlands/GroupScheme/Rational/CocharacterConeThresholdPartitionStatement.md) | [`Langlands.GroupScheme.CocharacterCone.thresholdPartition`](../../Langlands/GroupScheme/Rational/CocharacterConeThresholdPartitionProof.md) |
| [Iwahori double-coset volume with the Levi index](../../Langlands/HarmonicAnalysis/HarishChandraSchwartz/IwahoriLeviDoubleCosetVolumeStatement.md) | [`Langlands.HarishChandraSchwartz.iwahoriLeviDoubleCosetVolume`](../../Langlands/HarmonicAnalysis/HarishChandraSchwartz/IwahoriLeviDoubleCosetVolumeProof.md) |
| [Maximal-Levi reducibility from a joint compact basis](../../Langlands/Representation/Exponents/MaximalLeviReducibilityFromJointBasisStatement.md) | [`maximalLeviReducibilityFromJointBasis`](../../Langlands/Representation/Exponents/MaximalLeviReducibilityFromJointBasisProof.md) |

## VII.2 Tempered representations

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| VII.2.1 Definition | 227 / 233 | `IsNormalizedExponentTempered` | D (normalized parameter; see the progress note for the corrected sign convention) |
| VII.2.1 Remark 1, first assertion (full-group exponents unitary) | 227 / 233 | `NormalizedTemperedFullGroupExponentStatement` | P: `normalizedTemperedFullGroupExponent` |
| VII.2.1 Remark 1, second assertion (central character unitary) | 227 / 233 | `NormalizedTemperedCentralCharacterStatement` (nonzero representations) | P: `normalizedTemperedCentralCharacter` |
| VII.2.1 Remark 2 (square-integrable implies tempered) | 227 / 233 | `RP.SquareIntegrableNormalizedTemperedStatement` | P: `squareIntegrableNormalizedTempered` (`Exponents/SquareIntegrableNormalizedTemperedProof`) |
| VII.2.1 Remark 3 (standard parabolics suffice) | 227 / 233 | `NormalizedTemperedStandardReductionStatement` | P: `normalizedTemperedStandardReduction` |
| VII.2.2 Lemma | 227–228 / 233–234 | `RP.LeviInductionNormalizedTemperedStatement` | P: `leviInductionNormalizedTempered` |
| VII.2.3 Lemma | 229 / 235 | `RP.UnitaryJacquetPartTemperedStatement` | P: `unitaryJacquetPartTempered` |
| VII.2.4 Proposition | 229 / 235 | `RP.TemperedInductionUnitaryReciprocityStatement`, `RP.TemperedJacquetUnitaryRestrictionStatement` | P: `temperedInductionUnitaryReciprocity`, `temperedJacquetUnitaryRestriction` |
| VII.2.4 Lemma | 230 / 236 | `RP.TemperedSquareIntegrableUnitaryPartStatement` | A |
| VII.2.4 Lemma, standard-parabolic test | 230 / 236 | `RP.UnitaryJacquetVanishingStandardReductionStatement` | P by `unitaryJacquetVanishingStandardReduction`. For any smooth complex representation, rational conjugation compares vanishing at all proper represented rational parabolics with vanishing in the fixed proper standard family |
| VII.2.5 Proposition | 230 / 236 | `RP.TemperedGeometricLemmaStatement` | P: `temperedGeometricLemma` |
| VII.2.6 Theorem | 231 / 237 | `RP.TemperedIrreducibleDiscreteSeriesStatement`, `RP.TemperedIrreducibleDiscreteSeriesUniquenessStatement`, and `RP.NormalizedTemperedSubrepresentationStatement` | A for the embedding equivalence. Uniqueness is proved by `temperedIrreducibleDiscreteSeriesUniqueness` and the subrepresentation step by `normalizedTemperedSubrepresentation` |
| VII.2.6 Theorem, standard-parabolic witness | 231 / 237 | `RP.DiscreteSeriesEmbeddingStandardReductionStatement` | P by `discreteSeriesEmbeddingStandardReduction`. A single rational conjugation standardizes the parabolic and Levi. The comparison retains square integrability of the inducing representation for every Borel Haar measure on its center quotient |
| VII.2.6 Corollary | 232 / 238 | `RP.TemperedIrreducibleUnitarizableStatement` | A |
| VII.2.6 Remark (without irreducibility the Corollary can fail) | 232 / 238 | `RP.TemperedReducibleNotUnitarizableStatement` | P: `temperedReducibleNotUnitarizable` (`Exponents/TemperedReducibleNotUnitarizableProof`) |
| VII.2.4 Lemma and VII.2.6 embedding equivalence and Corollary with building data | 230–232 / 236–238 | `RP.TemperedDiscreteSeriesFromBuildingStatement` | P by `temperedDiscreteSeriesFromBuilding`. `Langlands.Geometry.Building.GroupAxiomsExistenceStatement` supplies the geometry for the strict-root-cone criterion in the proof of the VII.2.4 Lemma. The other conclusions are the VII.2.6 embedding equivalence and unitarizability |

## VII.3 Intertwining operators of induced representations

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| VII.3.1 Definition (Bruhat order `≤_{PQ}`) | 232 / 238 | `Langlands.Geometric.BruhatLE` (on actual double cosets), `IsBruhatRefinement` | D |
| VII.3.1: `1̄` is the least element when `P = Q` and the greatest when `Q = P̄` | 232–233 / 238–239 | `RP.BruhatIdentityExtremesStatement` | P: `bruhatIdentityExtremes` (`Exponents/BruhatIdentityExtremesProof`) |
| VII.3.2 filtrations and their comparisons | 233–234 / 239–240 | `RP.PQSupportGradedStatement`; support subfunctors in `Intertwining/PQRegularity` | P: `pqSupportGraded` |
| VII.3.3 Lemma (`PQ`-regularity) | 234 / 240 | `RP.PQRegularityLemmaStatement`; `IsPQRegular` | S |
| VII.3.4 Proposition and preceding integral identification | 235–236 / 241–242 | `RP.PQIntertwiningOperatorStatement` (derived: the integral replaced by an arbitrary identification); explicit integral form `RP.PQIntegralIntertwiningOperatorStatement` | Derived form P: `pqIntertwiningOperator`; integral form P: [`pqIntegralIntertwiningOperator`](../../Langlands/Representation/Intertwining/PQIntegralIntertwiningOperatorProof.md) |
| VII.3.5 Proposition (i) | 237 / 243 | `RP.PQIntertwiningCompositionStatement` | P: [`pqIntertwiningComposition`](../../Langlands/Representation/Intertwining/PQIntertwiningCompositionProof.md) |
| VII.3.5 Proposition (ii) | 237 / 243 | `RP.PQIntertwiningInnerLeviStatement` | P: [`pqIntertwiningInnerLevi`](../../Langlands/Representation/Intertwining/PQIntertwiningInnerLeviProof.md) |
| VII.3.5 Proposition (iii) | 237 / 243 | `RP.PQIntertwiningOuterLeviStatement` | P: [`pqIntertwiningOuterLevi`](../../Langlands/Representation/Intertwining/PQIntertwiningOuterLeviProof.md) |
| VII.3.5 opening assertion "`d(P, Q)` is the length of the element `w ∈ W(A_M)` with `w · P = Q`" | 236 / 242 | `Langlands.GroupScheme.MinimalParabolicDistanceLengthStatement` (minimal `M`, corrected form) | P: `minimalParabolicDistanceLength` (`Langlands/GroupScheme/Rational/MinimalParabolicDistanceLengthProof`). For non-minimal `M` the printed assertion is a source issue (I1 below) |

## VII.4 The Langlands classification

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| VII.4.1 Definition (Langlands triplet) | 241 / 247 | `IsLanglandsTriplet`, chambers `Langlands.GroupScheme.restrictedCorootChamber` (`LanglandsClassification/LanglandsTriplet`) | D |
| VII.4.1 Lemma | 241 / 247 | `RP.LanglandsTripletOppositeRegularityStatement`; proved steps `RP.LanglandsTripletOppositePieceSeparationStatement`, `RP.LanglandsTripletOppositeRegularityReductionStatement` | P: `langlandsTripletOppositeRegularity` (`LanglandsClassification/LanglandsTripletRegularityProof`); steps P |
| (VII.4.1.1), cone for the tempered exponent contribution | 241 / 247 | `RP.GeometricLemmaIntersectionDatum.normalizedRealPart_sub_unramifiedPieceRealPart_mem_nonnegCone`, `Langlands.GroupScheme.ParabolicRootPresentation.neg_mem_nonnegCone_of_opposite` | P as the `hxQ` and `hxP` steps of `langlandsTripletOppositePieceSeparation`. The bound is on the full geometric-lemma piece's exponent after subtracting its unramified contribution |
| (VII.4.1.2), nonzero negative-cone shift for the unramified contribution | 241–242 / 247–248 | `RP.GeometricLemmaIntersectionDatum.unramifiedPieceDisplacement_mem_nonnegCone_and_ne_zero` | P as the `hδ` step of `langlandsTripletOppositePieceSeparation`. Lean uses the original inducing real part minus the piece parameter, so the displacement lies in the nonnegative cone of \(P\) |
| (VII.4.1.3), ambient Weyl displacement | 241–242 / 247–248 | `Langlands.GroupScheme.DominantWeylDisplacementStatement` | P by `dominantWeylDisplacement`. Over any field, a point of the closed coroot chamber minus its inverse Weyl translate lies in the nonnegative simple-root cone in the full real character space (I8) |
| VII.4.2 Theorem (i)–(iii) | 243–246 / 249–252 | `RP.LanglandsQuotientUniqueStatement`, `RP.LanglandsQuotientInjectiveStatement`, `RP.LanglandsQuotientExhaustiveStatement`, conjunction `RP.LanglandsClassificationStatement` | S. P for `RP.LanglandsClassificationFromInputsStatement`, with four Chapter VI premises. See the proofs of the implications below and source issue I9 |
| VII.4.2 sentence after the proof of (i), exponent characterization of `J(P, σ, ψ)` | 243 / 249 | `RP.LanglandsQuotientExponentCharacterizationStatement` | S. P for `RP.LanglandsQuotientExponentCharacterizationFromSecondAdjointnessStatement`, with second adjointness as its sole premise |

In (VII.4.1.1)–(VII.4.1.2), the compatible presentation of \(P\) comes from the
Langlands triplet. The proof obtains an opposite presentation on the same split
component and uses Jacquet admissibility of the twisted source. For a hypothetical
common exponent, its tempered offset \(x\) lies in the opposite cone. Hence \(-x\) and
the nonzero displacement \(\delta\) lie in the cone of \(P\). Pointedness gives
\(-x+\delta\ne 0\), contradicting equality of the exponent real parts.
[Piece separation proof](../../Langlands/Representation/LanglandsClassification/LanglandsTripletOppositePieceSeparation.md)

### VII.4.2 conditional proof publications

The two implication proofs below are in the Library. Their
Lean and Markdown pairs and the pairs of their target implications match the
files as first checked. Both proofs were checked by a Lake build against the
exact target, with the statement and its inputs unchanged.

| Target implication | First Library commit of proof |
| --- | --- |
| `LanglandsClassificationFromInputsStatement` | `85c2fe719cf62e96f22aaf4ca03961c5814d086b` |
| `LanglandsQuotientExponentCharacterizationFromSecondAdjointnessStatement` | `51e4d8972659f1ffcf0ca89e8eee9540a30b52d3` |

- `langlandsClassificationFromInputs` proves all three parts at independent
  field and representation-carrier universes `u, v`. It takes second adjointness
  (`RP.LeviSecondAdjointnessStatement`, VI.9.6), finite length under
  normalized induction and Jacquet restriction (`RP.LeviInductionFiniteLengthStatement`,
  `RP.LeviJacquetFiniteLengthStatement`, VI.6.2 and VI.6.4), and
  irreducible admissibility (`Langlands.Aubert.General.RationalPointsIrreducibleAdmissibleStatement`,
  VI.2.2). Part (i) uses finite length to obtain a quotient and the
  VII.4.1 regularity argument to identify its kernel. Part (ii) uses mutual
  opposite intertwiners to compare the two triplets. Part (iii) uses a maximal
  positive part of an opposite Jacquet exponent to select a tempered untwist
  and applies second adjointness to obtain the quotient map.
  [Classification proof](../../Langlands/Representation/LanglandsClassification/LanglandsClassificationFromInputsProof.md)
- `langlandsQuotientExponentCharacterizationFromSecondAdjointness` takes
  `RP.LeviSecondAdjointnessStatement.{u, v}`. For an irreducible subquotient \(\pi\)
  of \(i_P^G(\sigma\otimes\psi)\), it proves that \(\pi\) is a quotient if and only if
  a normalized exponent of \(r_{\bar P}^G(\pi)\) on the Levi split component has
  real part \(\Re\psi\). For the reverse implication the proof separates the
  given exponent from all nonidentity pieces using their action ideals. It
  obtains a nonzero map from the inducing twist to \(r_{\bar P}^G(\pi)\) and
  applies second adjointness.
  [Exponent characterization proof](../../Langlands/Representation/LanglandsClassification/LanglandsQuotientExponentCharacterizationFromSecondAdjointnessProof.md)

## VII.5 Notes on Chapter VII

| Item | Pages | Status |
| --- | --- | --- |
| VII.5 notes | 246 / 252 | X: attributions ([2], [20], [22], [23], [45], [40]). The notes also say that VII.1.3 is the point that makes the small progenerators of VI.10.1 generators; that use is in the proofs of the VI.10.1 statements. |

## Proof-publication update, 14 November 2026

The four updated targets above have proofs in the Library. This update
compares their Lean and paired Markdown with the original VII.3.4–VII.3.5 passage, printed
pp.235–240 / PDF pp.241–246. The following five entries cover four theorems: two versions of the composition proof
were reconciled in one file. Each was checked by a Lake build against the exact target,
with the statement and its inputs unchanged. A fresh check of the four proof modules at
this update's Library base also passed with no errors or warnings.

| Item | First appeared at Library commit |
| --- | --- |
| VII.3.4 integral form | `0c3f30c24701c74d5474fca3fbb5324a99aa1d58` |
| VII.3.5 (i) | `85c2fe719cf62e96f22aaf4ca03961c5814d086b` |
| VII.3.5 (i), second version | `85c2fe719cf62e96f22aaf4ca03961c5814d086b` |
| VII.3.5 (ii) | `51e4d8972659f1ffcf0ca89e8eee9540a30b52d3` |
| VII.3.5 (iii) | `51e4d8972659f1ffcf0ca89e8eee9540a30b52d3` |

The integral, inner-Levi and outer-Levi pairs at this update's base equal the files as
first checked. For composition, the Lean file equals the Lean file of the first version;
the Markdown equals the file of the reconciled version. It
documents the retained term using `pqCompositionHaar`, whose proof applies
`pqCompositionHaar_of_product` to `pqCompositionProduct`. It does not equal the
Markdown of either version as first checked. The published Lean and explanation agree.

### Exact hypotheses and conclusions

These are proofs of the existing Prop-valued statements, at their original universes
`u, v`. Their common setting is an arbitrary nonarchimedean local field and an actual
connected reductive group scheme, with the canonical rational-point topology and explicit
local-compactness and nonarchimedean-group instances. Represented parabolics supply the
actual Levi and geometric unipotent radical inclusions and the multiplication isomorphism.
Common Levis have equal embeddings into the ambient group. Opposites have that same
embedded Levi and the prescribed rational-point intersection. Split components are
supplied where regularity or root distance is used. Measures are Borel Haar measures on
the indicated actual intersection subgroups. The representations are smooth complex
representations, without an added admissibility or finite-length assumption. Further
statement details are in the paired explanations of
[PQIntegralIntertwiningStatements](../../Langlands/Representation/Intertwining/PQIntegralIntertwiningStatements.md)
and [PQIntertwiningLeviStatements](../../Langlands/Representation/Intertwining/PQIntertwiningLeviStatements.md).

- **VII.3.4, printed pp.235–236 / PDF pp.241–242.** For every smooth `σ`, the
  support-filtration quotient is identified equivariantly with `σ` by integration over
  `V = N̄(F) ∩ U(F)`. For `PQ`-regular `σ`, there is exactly one intertwiner satisfying
  `J(f)(1) = ∫_V f(v) dv` on the boundary-vanishing subspace. The formula means both
  integrability and equality after every algebraic linear form on `σ`; it imposes no
  norm or topology on the representation space. The proof constructs the integral,
  descends through the Jacquet relations and lower support, proves surjectivity,
  naturality and Levi covariance, and uses natural-surjection rigidity to obtain the
  equivalence. The final published reduction gives the unique operator. This direct
  route differs from Renard's appeal to (VI.5.1.12).
- **VII.3.5 (i), statement p.237 / PDF p.243, computation p.239 / PDF p.245.** The
  assumptions include both `d(P₁,P₂) + d(P₂,P₃) = d(P₁,P₃)` and `d(P₁,P₂) = 1`.
  The distance counts indivisible relative roots, as in V.3.4. Given Haar measures on
  `V₁₂ = N̄₁ ∩ N₂` and `V₂₃ = N̄₂ ∩ N₃`, the theorem constructs a compatible measure
  on `V₁₃ = N̄₁ ∩ N₃`: its integral is the iterated integral of `φ(vu)`, with `v ∈ V₁₂`
  integrated first. It transfers `P₁P₃`-regularity to both adjacent pairs and proves
  `J₂₃.comp J₁₂ = J₁₃` for supplied integral-normalized operators and compatible
  measures. The proof supplies the support, multiplication-homeomorphism, Haar and
  regularity inputs of the published reduction, then uses the double-integral
  computation and uniqueness. It does not use the opening length assertion (I1).
- **VII.3.5 (ii), statement p.237 / PDF p.243, proof pp.238–240 / PDF pp.244–246.**
  A represented `Q = LU` contains `P₁` and `P₂`; represented parabolics `Pᵢ'` of `L`
  have images `Pᵢ(F) ∩ L(F)`, with compatible common `M` and opposites. The theorem
  transports every Haar measure on `N̄₁' ∩ N₂'` to a compatible one on `N̄₁ ∩ N₂`,
  constructs stage functions `f̃(g)(x) = δ_U(x)^(-1/2) f(emb(x)g)`, transfers
  `P₁P₂`-regularity to `P₁'P₂'`-regularity, and proves
  `J'(f̃(g))(x) = δ_U(x)^(-1/2) J(f)(emb(x)g)` for supplied normalized operators.
  The proof uses the actual integration-domain homeomorphism, Haar transport,
  the stage map and boundary transfer, and uniqueness of integral-normalized maps.
- **VII.3.5 (iii), statement p.237 / PDF p.243, proof pp.238–240 / PDF pp.244–246.**
  Represented `Qᵢ = LUᵢ` contain `Pᵢ`, share the same embedded `L`, and have a common
  represented intersection `P'` in `L`, with the stated opposites and split components
  of `M` and `L`. For `X = i_{P'}^L(σ)`, `Q₁Q₂`-regularity of `X` implies
  `P₁P₂`-regularity of `σ`. The theorem transports Haar measures from `Ū₁ ∩ U₂` to
  `N̄₁ ∩ N₂`, constructs the first stage function with `δ_{U₁}^(-1/2)`, and proves
  `J_Q(f̃)(g)(x) = δ_{U₂}(x)^(-1/2) J(f)(emb(x)g)` for supplied normalized maps.
  The proof identifies the integration domains, transports their measures, and proves
  this identity through the stage maps and integral uniqueness.

Both Levi regularity proofs use surjections of normalized Jacquet quotients and kernel
comparison, an alternative to the source's Bruhat-cell ideal comparison. The two final
Levi statements assert existence of the forward stage functions and identities for
supplied operators; they do not themselves assert that the stage maps are bijective or
that the operators exist. The integral theorem above supplies operator existence
separately when its hypotheses in `G` or `L` are instantiated. These four proof updates
leave the other historical row statuses, V1–V2, source issue I1 and the genuine gaps below
as recorded.

## Framework comparisons used above

- **V1. Root presentations.** Every actual rational parabolic, rational Levi and split
  component of a connected reductive group admits a compatible presentation: the
  published `Langlands.GroupScheme.ParabolicRootPresentationExistenceStatement` is proved
  without further premises by `parabolicRootPresentationExistence`
  (`GroupScheme/Rational/ParabolicRootPresentationProof`, which also proves the
  independence of the restricted roots and cones from the presentation as
  `parabolicRootPresentation`). The VII.2.2 proof `leviInductionNormalizedTempered`
  (`Exponents/LeviInductionNormalizedTemperedProof`) uses this theorem. This structural
  obligation is discharged. Its effect on the two forms of the presentation test:
  - `IsNormalizedExponentTempered` requires `Nonempty (ParabolicRootPresentation p l a)` at
    every triple, so it is never satisfied vacuously; by the existence theorem this
    conjunct always holds for connected reductive `G`, and the predicate is the cone
    condition for every compatible presentation.
  - `RP.ArbitraryParabolicCasselmanCriterionStatement` and the other statements with a
    universal presentation binder test every supplied presentation. By the existence
    theorem the test is never empty. The Markdown of the Casselman statement still
    describes presentation existence as unproved; that sentence predates
    `parabolicRootPresentationExistence`.
  Independent of existence, the comparison of the presentation cones with the source's
  normalizations (the VII.1.2 row above, and the sign convention of VII.2.1 in the progress note)
  remains as recorded in the rows.
- **V2. Represented versus standard parabolics.** The source works with standard
  (semi-standard) parabolics and transports by conjugation; the statements use all actual
  rational parabolics. VII.2.1 Remark 3 (`NormalizedTemperedStandardReductionStatement`,
  proved) compares the temperedness conditions. The VII.2.4 vanishing test uses
  proper standard parabolics, and the VII.2.6 embedding witness may be chosen
  from the standard family by the two reductions listed in VII.2.

## Source issues

- **I1. VII.3.5, opening paragraph (printed p.236 / PDF p.242).** The book defines
  `d(P, Q) = |Σ(P) ∩ Σ(Q̄)|` for semi-standard `P`, `Q` with the same Levi factor `M`, and
  says that it is well known that `d(P, Q)` is the length of the element `w` of
  `W(A_M) = N_G(A_M)/Z_G(A_M)` (V.3.5) with `w · P = Q`. The assertion needs two
  corrections.
  - For non-minimal `M` such a `w` need not exist. Example: `G = GL_3` with
    `M = GL_2 × GL_1` block diagonal, `A_M = {diag(a, a, b)}`, `P` the upper
    block-triangular parabolic and `Q = P̄`. An element of `N_G(A_M)` maps `diag(a, a, b)`
    to an element of `A_M` with the same eigenvalues and multiplicities, hence fixes it, so
    `W(A_M)` is trivial, while `P ≠ Q` and `d(P, Q) = |Σ(P)| = 1`. The book also defines no
    length function on `W(A_M)` for non-minimal `M`; this ledger makes no claim that none
    exists.
  - For minimal `M`, `W(A_M)` is the relative Weyl group `W`, which acts simply
    transitively on the minimal semi-standard parabolics, so `w` exists and is unique. Fix
    the standard minimal parabolic `P_∅` and write `P = uP_∅`, `Q = vP_∅` with
    `u, v ∈ W`, so that `w = vu⁻¹`. Then `Σ(P) = uΣ(P_∅)` and `Σ(Q̄) = −vΣ(P_∅)`, and
    `d(P, Q)` is the number of reduced roots `β ∈ Σ(P_∅)` with `v⁻¹uβ ∉ Σ(P_∅)`, that is
    `ℓ(u⁻¹v)` for the length `ℓ` defined by the simple roots of `P_∅`. This is the
    length of `w` for the simple reflections of `P` (the conjugates by `u` of those of
    `P_∅`). With the length defined by `P_∅` the assertion holds when `P = P_∅` and fails
    in general: for `G = GL_3` with `M` the diagonal torus, `P = s_1P_∅` and
    `Q = s_1s_2P_∅` give `Σ(P) ∩ Σ(Q̄) = {α_1 + α_2}`, so `d(P, Q) = 1`, while
    `w = s_1s_2s_1` has length 3.

  The assertion is not used by the Chapter VII statements above. Retained scope: the
  minimal-`M` assertion in both corrected forms (`d(P, Q)` is the length of `w` for the
  simple reflections of `P`, and `d(uP_∅, vP_∅) = ℓ(u⁻¹v)`) is stated by the published
  `MinimalParabolicDistanceLengthStatement`, proved by
  `minimalParabolicDistanceLength` (see the proof-status update in the introduction); the non-minimal case is
  a source issue with the counterexample above.

- **I2. VII.1.2, Casselman's criterion (printed p. 221 / PDF p. 227).** Sally–Tadić,
  Theorem 5.1(i) and its proof (printed pp. 120–121 / PDF pp. 47–48), give a
  square-integrable representation of `Sp₄(ℚ₃)` whose normalized Jacquet exponent
  at the standard Borel has `q^(-s)` real part `e₁`. Its pairing with the long
  simple coroot `e₂∨` is zero, refuting the printed necessity. Its coefficients
  in the simple-root basis `e₁ − e₂, 2e₂` are `1, 1/2`, which satisfy the
  strict root-cone condition used by the published corrected statement and
  necessity proof. [Counterexample and normalization](../errata/renard-2026-representations-groupes-reductifs-padiques.md)

- **I3. VII.1.2, Cartan cover and series (printed pp. 221–222 / PDF pp. 227–228).**
  For `G = ℚ₃ˣ`, `K₀ = ℤ₃ˣ` and `K = 1 + 3ℤ₃`, each of the two cells in
  the quotient by `3^ℤ` occurs twice in the labelled Cartan cover. With the
  trivial coefficient and total quotient measure one, the integral is one
  and the labelled sum is two. Summing each distinct cell once gives equality.
  The Lean sufficiency assembly uses subadditivity on the countable cover.
  [Counterexample and corrected integral bound](../errata/renard-vii12-cartan-cover.md)

- **I4. VII.1.2, double-coset volume (printed pp. 222–223 / PDF pp. 228–229).**
  For the upper \((2,1)\) parabolic of \(\mathrm{GL}_3(F)\),
  \(m=\operatorname{diag}(\varpi^3,\varpi^2,1)\) lies in the source's \(S_M(1)\).
  For a principal congruence subgroup \(K\), the double-coset volume ratio
  is \(q^6\), while \(\delta_P(m)=q^5\). The exact formula under the two
  radical contractions includes \([K_M:K_M\cap mK_Mm^{-1}]\). The published
  estimates use split-component rays and absorb finite translates by
  submultiplicativity of double-coset indices. The erratum is in the Library.
  [Counterexample, index formula and upper bound](../errata/renard-vii12-iwahori-volume.md)

- **I5. VII.1.3, Levi transporters (printed p. 224 / PDF p. 230).**
  In split \(\mathrm{GL}_3\), the three-cycle sending \(1\) to \(2\), \(2\) to \(3\)
  and \(3\) to \(1\) sends the standard Levi block \(\{1,2\}\) to \(\{2,3\}\).
  Its square sends the block to \(\{3,1\}\), which is outside the standard Levi
  list. Thus the transporter set may fail closure under multiplication.
  The published statements use its set of left cosets.
  [Transporter statement and example](../../Langlands/GroupScheme/Rational/StandardLeviTransporterCosetsStatement.md)

- **I6. VII.1.3, nonsplitting after (VII.1.3.2) (printed p. 225 / PDF p. 231).**
  Length two and one-dimensional Hom spaces in both directions exclude
  simultaneous semisimplicity in the source argument. They allow one split
  extension, as the upper-triangular algebra example shows. In the distinct-Levi
  case, applying VI.5.3, first adjointness and Schur's lemma to each self-Hom
  proves that each endomorphism space consists of scalars. This excludes a
  projection onto a nonzero proper summand. In the unitary branch both
  inductions are semisimple, so the mutual Hom computation suffices.
  The erratum is in the Library.
  [Example and self-endomorphism argument](../errata/renard-vii13-mutual-hom.md)

- **I7. VII.1.2, the monoid underlying the threshold partition (printed pp. 222–223 / PDF pp. 228–229).**
  A cocharacter \((a,b,-a-b)\) of the diagonal torus of split \(\mathrm{SL}_3\) has
  simple-root coordinates \((p,q)=(a-b,a+2b)\), so the image consists of pairs
  with \(p\equiv q\pmod 3\). In its nonnegative submonoid, the indecomposable
  elements \((3,0),(0,3),(1,1)\) satisfy \((3,0)+(0,3)=3(1,1)\). This contradicts
  the free-monoid description. Dividing by the coordinate steps of the two axis
  rays leaves the residues \((0,0),(1,1),(2,2)\). The published threshold
  statement retains a finite residue set and bounds the exponents in each
  Levi piece using the source's cutoff.
  [Threshold partition statement](../../Langlands/GroupScheme/Rational/CocharacterConeThresholdPartitionStatement.md)

- **I8. (VII.4.1.3), reflection coefficients (printed p. 242 / PDF p. 248).**
  If \(\beta_i\) is dual to the simple roots, then
  \(\beta_i-s_j\beta_i=\delta_{ij}\alpha_j^\vee\). The coroot
  \(\alpha_j^\vee\) gives both corrected coefficients in the printed length
  induction and yields the stated ambient bound. The correction with two split
  \(\mathrm{SL}_3\) examples is in the Library.
  [Reflection coefficients and Levi restriction](../errata/renard-vii41-reflection-coefficients.md)

- **I9. VII.4.2(ii), central part of the real parameter (printed p. 246 / PDF p. 252).**
  After obtaining \(\mu_1=\mu_2\), the printed argument writes each full
  parameter as a positive sum of restricted simple roots. Every such root
  vanishes on the split center of \(G\), whereas V.3.15–16 allow any central
  component in the coroot chamber (printed pp. 113–114 / PDF pp. 119–120).
  For the upper Borel of split \(\mathrm{GL}_2\), the unramified character
  \(\psi(\operatorname{diag}(x,y))=|x|_F\) has normalized real parameter \(e_1\).
  Its pairing with the single simple coroot is \(1\). Its restriction to the
  central cocharacter \(z\mapsto\operatorname{diag}(z,z)\) is also \(1\), so it
  lies outside the span of \(e_1-e_2\). It has central component
  \((e_1+e_2)/2\).
  The published `RP.fullRealPart_eq_and_index_eq_of_mutual_mem_nonnegCone`
  obtains equality of the full parameters by the invariant form comparison.
  It applies `Langlands.GroupScheme.RelativeRootReflectionData.selected_eq_of_pair`
  to recover each standard Levi index as the simple roots whose coroots pair to
  zero with the common full parameter. This proves the Levi equality required
  at the end of VII.4.2(ii).
  [Mutual parameter comparison](../../Langlands/Representation/LanglandsClassification/MutualOppositeParameterComparison.md)

## Genuine gaps of Chapter VII

1. VII.1.3, opening paragraph. `Langlands.GroupScheme.MaximalStandardLeviPointCosetsStatement`
   asks for the maximality characterization by the number of rational point
   cosets and the opposite-parabolic conclusion for the second coset.
2. VII.1.3 Corollary: projection existence, faithfulness, the adjunction unit
   isomorphism and equivalence in `RP.MaximalLeviBlockProjectionEquivalenceStatement`
   have no unconditional proof in the Library.
   The published `RP.maximalLeviBlockProjectionEquivalenceOfDecompositionOfBlocks`
   derives the exact proposition from the VI.3.3.1 inertia decomposition
   `CuspidalSupport.RationalCuspidalInertiaDecompositionStatement` and
   `RP.MaximalLeviBlockStatements`; the Library proves neither (it derives the
   first from further hypotheses). The source's last step applies the
   adjunction triangle to the isomorphic counit, then reflects the resulting
   unit isomorphism through the exact faithful `r_D`.
   [Published conditional reduction](../../Langlands/Representation/Exponents/MaximalLeviBlockProjectionReduction.md)
3. VII.4.2: the unconditional classification and its exponent characterization
   await the Chapter VI premises named above. Second adjointness suffices for
   the characterization and for the injectivity part of the classification.

Update at Library `9951a27f`: the VII.3.5 gap on the minimal-`M` form of the
opening assertion is stated by the published `MinimalParabolicDistanceLengthStatement`,
now proved as `minimalParabolicDistanceLength`. For non-minimal `M`, and for the length
relative to `P_∅` when `P ≠ P_∅`, the printed assertion fails as written (I1).
`RP.LanglandsQuotientExponentCharacterizationStatement` is the published
unconditional VII.4.2 exponent characterization statement. The statements of the
VII.2.6 Remark and of the VII.3.1 extremes of the Bruhat order are published; both
are now proved (`temperedReducibleNotUnitarizable`, `bruhatIdentityExtremes`).
