# Renard 2026, Chapter VII: item-by-item coverage ledger

Worker 1222, executor of the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`, revision 1. This note is the Chapter VII
part of the item ledger that the task contract requires, in the format of the
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
pairs checked at `edf9646441fdf5d75d692913b8928b89b9d92538`. The status codes, the abbreviation of
task identifiers and the method of checking are those of the Chapter VI ledger.
The VII.4 proof steps, conditional proofs and source issues below were checked
on 20 November 2026 at Library `5704217a2667191d63b37f0e85a2da41c15b21d2`.
All declarations below are in `Langlands.Aubert.General.RepresentedParabolic`
(abbreviated `RP`) unless another namespace is written. The focused source maps
[root-exponent-tempered-progress](root-exponent-tempered-progress.md) and
[parabolic-functors-tempered-progress](parabolic-functors-tempered-progress.md) give
more detail for VII.1–VII.2.

The proof-status update of 14 November 2026, by Worker 4, checks every row with status S
against Library `a163f87c7a46874f408deed853c10c83207e9f69`, by the method stated in the
Chapter VI ledger: a statement is marked proved (P) only when a Library theorem with no
hypotheses has exactly that statement as its type. It changes the rows VII.1.3
Corollary, VII.2.1 Remark 2, VII.2.6 Theorem and Remark, VII.3.1 extremes, VII.3.5
opening assertion and VII.4.1 Lemma, gap 2 and the source issue I1. Proof modules named
by bare paths are under `Langlands/Representation/`. For each new proof Worker 4 read the
theorem line and found no `sorry` or `admit` in its file. The new proofs and their published
`lean.proof@1` records, whose Lean and Markdown files at the checked commit have the SHA256
recorded in the record:

| Row | Theorem | Proof module | Proof record | Integration ID | First Library commit |
| --- | --- | --- | --- | --- | --- |
| VII.2.1 Remark 2 | `squareIntegrableNormalizedTempered` | [SquareIntegrableNormalizedTemperedProof](../../Langlands/Representation/Exponents/SquareIntegrableNormalizedTemperedProof.md) | `3b2190cf-d09f-4d95-852a-a4f80d209a58` | `4d4f36cb43134a9480ac6db62c3b882f` | `17dd94ea` |
| VII.2.6 Theorem, uniqueness | `temperedIrreducibleDiscreteSeriesUniqueness` | [TemperedIrreducibleDiscreteSeriesUniquenessProof](../../Langlands/Representation/Exponents/TemperedIrreducibleDiscreteSeriesUniquenessProof.md) | `083f5bec-6a05-4009-8ff5-a958748085ca` | `d284d7188f164a22a398a341d28938ea` | `cfedefb6` |
| VII.2.6 Remark | `temperedReducibleNotUnitarizable` | [TemperedReducibleNotUnitarizableProof](../../Langlands/Representation/Exponents/TemperedReducibleNotUnitarizableProof.md) | `10d78506-4824-4658-b3d2-6afe58b10050` | `64b3ccc6cc8349cea1b56367828419ec` | `730bd1f2` |
| VII.3.1 extremes | `bruhatIdentityExtremes` | [BruhatIdentityExtremesProof](../../Langlands/Representation/Exponents/BruhatIdentityExtremesProof.md) | `0ec4ea93-fabc-48fb-9af2-e1a7ef1f68da` | `86a35b120bfe4abea6228234fde9bbea` | `730bd1f2` |
| VII.3.5 opening assertion, minimal `M` | `minimalParabolicDistanceLength` | [MinimalParabolicDistanceLengthProof](../../Langlands/GroupScheme/Rational/MinimalParabolicDistanceLengthProof.md) | `c68de2e3-f0ef-4f04-9d6b-2fb94aebee90` | `42fa7a88d0524773b7e00c1054efb59b` | `730bd1f2` |
| VII.4.1 Lemma | `langlandsTripletOppositeRegularity` | [LanglandsTripletRegularityProof](../../Langlands/Representation/LanglandsClassification/LanglandsTripletRegularityProof.md) | `ae39328b-9b9a-4a08-b89b-96877fa75d12` | `2dffde5df03e4e6fb61057315d0004d1` | `b128d289` |

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

## VII.1 Casselman's criterion and applications

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| VII.1.1 characteristic spaces `(r_P^G V)_χ`, normalized exponents, `Exp(A, r_P^G V)` | 220 / 226 | `normalizedJacquetWeightSpace`, `IsNormalizedJacquetExponent`, `normalizedJacquetExponents` (`Exponents/ArbitraryParabolic`) | D |
| (VII.1.1.1) and finiteness of `Exp` in finite length | 220 / 226 | `RP.ArbitraryParabolicExponentStatement` | P: `arbitraryParabolicExponent` |
| VII.1.1 Remark (`P = G`) | 220 / 226 | `RP.ArbitraryParabolicExponentStatement` | P |
| VII.1.1 Lemma (i)–(ii) | 220–221 / 226–227 | `RP.ArbitraryParabolicExponentStatement` | P |
| VII.1.2 Theorem (Casselman's criterion) | 221 / 227 | `RP.ArbitraryParabolicCasselmanCriterionStatement`; necessity `RP.ArbitraryParabolicCasselmanNecessityStatement` | S: Task 4712 (`2e8d370f-f1ed-4ad4-a529-5083212ebae0`). Necessity P: `arbitraryParabolicCasselmanNecessity`. The corrected condition is the strictly positive root cone from the final decay test in the proof. The printed coroot-chamber necessity fails on an actual square-integrable representation of `Sp₄(ℚ₃)` (I2) |
| VII.1.2 Theorem with Bruhat–Tits availability | 221–224 / 227–230 | `RP.CasselmanFromBuildingStatement` | S: Task 8060. The published Bruhat–Tits availability proposition is the explicit premise for joint Cartan and Iwahori basis assembly and hence for sufficiency. The necessity proof applies independently |
| VII.1.2 first paragraph of the proof, reduction to the central uniformizer lattice | 221 / 227 | `RP.CentralUniformizerSquareIntegrabilityStatement` | S: Task 8059. The evaluated cocharacter lattice is closed, its quotient in the full center is compact, and square integrability modulo the two central subgroups is equivalent for arbitrary quotient Haar normalizations |
| VII.1.2 Cartan refinement after (VII.1.2.1) and labelled series preceding (VII.1.2.2) | 221–222 / 227–228 | `Langlands.cartanLatticeL2`, `Langlands.countableCellLpUpper`; `Langlands.HarishChandraSchwartz.CartanLabelledSeriesStatement` | P for the overlap-tolerant upper estimate on the full central quotient used by sufficiency, checked at Library `b0b4deb8c936156b61ecb9730f7ff1ebb8ff3f5c`. S: Task 8125 for the two-sided comparison on the uniformizer quotient, with disjoint coarse cells and at most \(r^2\) fine labels per point. Under the cover assumption the integral and labelled series are finite together (I3) |
| VII.1.2 ambient Haar weights in the series preceding (VII.1.2.2) | 221–222 / 227–228 | `Langlands.HarishChandraSchwartz.CentralUniformizerCellVolumeStatement` | S: Task 8123. Each compact-open double coset embeds in the central uniformizer quotient and keeps its ambient Haar mass for the quotient measure compatible with counting measure on the lattice |
| VII.1.2 partition by the \(S_M(n)\) after (VII.1.2.2) | 222–223 / 228–229 | `Langlands.GroupScheme.CocharacterCone.ThresholdPartitionStatement` | S: Task 8121. A finite residue set and exponents along diagonal cocharacter rays parameterize the actual integral cone modulo its annihilator. Bounded and unbounded exponents give the prescribed disjoint threshold pieces (I7) |
| VII.1.2 double-coset volume following (VII.1.2.2) | 222–223 / 228–229 | `Langlands.Aubert.General.standardBasisMember_rayIndex`, `Langlands.Aubert.General.RationalPointFamily.rationalLatticeQuotientVolume`; `Langlands.HarishChandraSchwartz.IwahoriLeviDoubleCosetVolumeStatement` | P for the finite-translate upper bound on the full central quotient, checked at Library `24390f9f6d7a3b7df9e5b9dd4d6e79e178c8ac85`. S: Task 8118 for the exact formula including the Levi index, under the Iwahori factorization, ambient injectivity and the two radical contractions (I4) |
| VII.1.3 opening paragraph, standard Levi transporters | 224 / 230 | `Langlands.GroupScheme.StandardLeviTransporterCosetsStatement`; `Langlands.GroupScheme.MaximalStandardLeviPointCosetsStatement` | S. The comparison of left coset sets is the target of Task 8061. The second statement uses the comparison and the Weyl-side V.4.8 result to count two cosets precisely for maximal proper standard parabolics and to identify the conjugate parabolic for a representative of the second coset (I5) |
| VII.1.3 Theorem | 224 / 230 | `RP.MaximalLeviSupercuspidalReducibilityStatement` (and the reduction `RP.MaximalLeviSupercuspidalReducibilityFromInputsStatement`) | S: task 004e00e1; reduction P. Derived: an arbitrary maximal rational parabolic, with "`M = M'` and `ρ^w = ρψ`" expressed through a normalizing element of `G(F)` |
| VII.1.3 Theorem with a joint compact basis | 224–226 / 230–232 | `RP.MaximalLeviReducibilityFromJointBasisStatement` | S: Task 8126. The joint special-compact basis gives admissibility, compact support and the fixed-level VI.3.4 finiteness at the induced carrier universe. The conclusion is the full represented reducibility criterion |
| VII.1.3 Corollary (i)–(iii) | 226–227 / 232–233 | `RP.MaximalLeviBlockStatements`; `RP.MaximalLeviBlockProjectionEquivalenceStatement` | S. The first statement (task `f4046ca6`) expresses (ii) as Jacquet nonvanishing and (iii) as full faithfulness and essential surjectivity of induction. The second statement (task `3c3f4d9e`) names `r_D` using a left adjoint to the block inclusion. It asserts projection existence, faithfulness of `r_D`, invertibility of `π → i_P^G r_D(π)` and the equivalence with inverse `i_P^G`. Its statement record `17566075` first entered Library `c40a0134` under integration `596546b6faf9495ba266d58426b8d8d3` |

The four new statement pairs first entered the Library at
`95d37e11bd46972d484c6fc9e6b864ff7625cf9e`. The Lean and Markdown files at
the checked commit match the frozen files. The three named proof tasks
have shared draft revision 1 with complete Lean and Markdown pairs and
await proof publication.

| Statement explanation | Statement record | Integration ID | Proof task |
| --- | --- | --- | --- |
| [Casselman criterion with building availability](../../Langlands/Representation/Exponents/CasselmanFromBuildingStatement.md) | `2dfaa85f-8c49-46d7-aa4d-2e5839ad6fb9` | `2ff826e1e3fa487a9223267cad8224c5` | Task 8060 (`9857e929-2102-4c46-9d0d-cb7095342271`) |
| [Central uniformizer lattice](../../Langlands/Representation/Exponents/CentralUniformizerSquareIntegrabilityStatement.md) | `c74e419f-9221-46fe-8dee-eb21d6f20c2c` | `da07bcd9a3534387a7a4ab1ad425a1a3` | Task 8059 (`4845dbef-0fbe-49c6-8749-da714cbe5c5f`) |
| [Standard Levi transporter cosets](../../Langlands/GroupScheme/Rational/StandardLeviTransporterCosetsStatement.md) | `11f65ad0-ddbf-4b98-8f06-68316a66e91b` | `e5ec3c65162f4403ab5ad726f3c23010` | Task 8061 (`efb26077-4f4c-4fb3-9723-39115214dc09`) |
| [Maximal standard Levi point cosets](../../Langlands/GroupScheme/Rational/MaximalStandardLeviPointCosetsStatement.md) | `c817a331-6f7c-4741-b84d-d003a6dce3c7` | `7bd8513835ef4054aea6df8c8897a517` | Uses the proof of the preceding comparison |

The following five statements first entered the Library at
`6e9e589baa721ce995563f73f648b6f4e45718a1` after independent review and fresh
integrated validation. Their Lean and Markdown files match the frozen pairs
at the checked commit. Each proof task has a compile-checked shared draft at
revision 1 awaiting proof review and publication.

| Statement explanation | Statement record | Integration ID | Proof task |
| --- | --- | --- | --- |
| [Labelled Cartan series](../../Langlands/HarmonicAnalysis/HarishChandraSchwartz/CartanLabelledSeriesStatement.md) | `b9f0ae75-6c7e-4d85-b646-3d31ca56fde2` | `c2c31caa05ae498a91563d1397c08fa5` | Task 8125 (`b77701f5-413c-4f3f-bde3-88501fbf2acd`) |
| [Uniformizer quotient cell volume](../../Langlands/HarmonicAnalysis/HarishChandraSchwartz/CentralUniformizerCellVolumeStatement.md) | `62976d5e-4a0c-4855-ac32-5070d348008f` | `fe8fb8d9a4834a68846dc225b27086a2` | Task 8123 (`c84f7f0e-a093-4804-8870-9e203fd9cf99`) |
| [Cocharacter cone threshold partition](../../Langlands/GroupScheme/Rational/CocharacterConeThresholdPartitionStatement.md) | `d34beb48-4a84-42a4-9949-223d627c0959` | `4c52cb47e11842d48a24ac35663e60c5` | Task 8121 (`9f814f51-5671-40d0-8707-ef57915c71d7`) |
| [Iwahori double-coset volume with the Levi index](../../Langlands/HarmonicAnalysis/HarishChandraSchwartz/IwahoriLeviDoubleCosetVolumeStatement.md) | `5f56bd8b-776d-421b-9cca-2160ed19fc5b` | `32e461bea9f44997bf04ffdd581282a4` | Task 8118 (`237d031c-bb81-46eb-88c3-43d5c8544c80`) |
| [Maximal-Levi reducibility from a joint compact basis](../../Langlands/Representation/Exponents/MaximalLeviReducibilityFromJointBasisStatement.md) | `5e593895-e08f-4211-a758-b24a0a71c9c3` | `43cc151af16c48a0a410d814d7b49054` | Task 8126 (`52747171-71ba-4411-a132-a104466fca22`) |

## VII.2 Tempered representations

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| VII.2.1 Definition | 227 / 233 | `IsNormalizedExponentTempered` | D (normalized parameter; see the progress note for the corrected sign convention) |
| VII.2.1 Remark 1, first assertion (full-group exponents unitary) | 227 / 233 | `NormalizedTemperedFullGroupExponentStatement` | P: `normalizedTemperedFullGroupExponent` |
| VII.2.1 Remark 1, second assertion (central character unitary) | 227 / 233 | `NormalizedTemperedCentralCharacterStatement` (nonzero representations) | P: `normalizedTemperedCentralCharacter` |
| VII.2.1 Remark 2 (square-integrable implies tempered) | 227 / 233 | `RP.SquareIntegrableNormalizedTemperedStatement` | P: `squareIntegrableNormalizedTempered` (`Exponents/SquareIntegrableNormalizedTemperedProof`; task 1ebce298) |
| VII.2.1 Remark 3 (standard parabolics suffice) | 227 / 233 | `NormalizedTemperedStandardReductionStatement` | P: `normalizedTemperedStandardReduction` |
| VII.2.2 Lemma | 227–228 / 233–234 | `RP.LeviInductionNormalizedTemperedStatement` | P: `leviInductionNormalizedTempered` |
| VII.2.3 Lemma | 229 / 235 | `RP.UnitaryJacquetPartTemperedStatement` | P: `unitaryJacquetPartTempered` |
| VII.2.4 Proposition | 229 / 235 | `RP.TemperedInductionUnitaryReciprocityStatement`, `RP.TemperedJacquetUnitaryRestrictionStatement` | P: `temperedInductionUnitaryReciprocity`, `temperedJacquetUnitaryRestriction` |
| VII.2.4 Lemma | 230 / 236 | `RP.TemperedSquareIntegrableUnitaryPartStatement` | S: task f0ff1d42 |
| VII.2.5 Proposition | 230 / 236 | `RP.TemperedGeometricLemmaStatement` | P: `temperedGeometricLemma` |
| VII.2.6 Theorem | 231 / 237 | `RP.TemperedIrreducibleDiscreteSeriesStatement`, `RP.TemperedIrreducibleDiscreteSeriesUniquenessStatement`; step `RP.NormalizedTemperedSubrepresentationStatement` | `RP.TemperedIrreducibleDiscreteSeriesStatement` S: task 225f7d3d; uniqueness P: `temperedIrreducibleDiscreteSeriesUniqueness` (`Exponents/TemperedIrreducibleDiscreteSeriesUniquenessProof`); step P: `normalizedTemperedSubrepresentation` |
| VII.2.6 Corollary | 232 / 238 | `RP.TemperedIrreducibleUnitarizableStatement` | S: task 225f7d3d |
| VII.2.6 Remark (without irreducibility the Corollary can fail) | 232 / 238 | `RP.TemperedReducibleNotUnitarizableStatement` | P: `temperedReducibleNotUnitarizable` (`Exponents/TemperedReducibleNotUnitarizableProof`; Task 5685, statement candidate `9492bbaa`) |

## VII.3 Intertwining operators of induced representations

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| VII.3.1 Definition (Bruhat order `≤_{PQ}`) | 232 / 238 | `Langlands.Geometric.BruhatLE` (on actual double cosets), `IsBruhatRefinement` | D |
| VII.3.1: `1̄` is the least element when `P = Q` and the greatest when `Q = P̄` | 232–233 / 238–239 | `RP.BruhatIdentityExtremesStatement` | P: `bruhatIdentityExtremes` (`Exponents/BruhatIdentityExtremesProof`; Task 5685) |
| VII.3.2 filtrations and their comparisons | 233–234 / 239–240 | `RP.PQSupportGradedStatement`; support subfunctors in `Intertwining/PQRegularity` | P: `pqSupportGraded` |
| VII.3.3 Lemma (`PQ`-regularity) | 234 / 240 | `RP.PQRegularityLemmaStatement`; `IsPQRegular` | S: task d935ffb6 |
| VII.3.4 Proposition and preceding integral identification | 235–236 / 241–242 | `RP.PQIntertwiningOperatorStatement` (derived: the integral replaced by an arbitrary identification); explicit integral form `RP.PQIntegralIntertwiningOperatorStatement` | Derived form P: `pqIntertwiningOperator`; integral form P: [`pqIntegralIntertwiningOperator`](../../Langlands/Representation/Intertwining/PQIntegralIntertwiningOperatorProof.md) |
| VII.3.5 Proposition (i) | 237 / 243 | `RP.PQIntertwiningCompositionStatement` | P: [`pqIntertwiningComposition`](../../Langlands/Representation/Intertwining/PQIntertwiningCompositionProof.md) |
| VII.3.5 Proposition (ii) | 237 / 243 | `RP.PQIntertwiningInnerLeviStatement` | P: [`pqIntertwiningInnerLevi`](../../Langlands/Representation/Intertwining/PQIntertwiningInnerLeviProof.md) |
| VII.3.5 Proposition (iii) | 237 / 243 | `RP.PQIntertwiningOuterLeviStatement` | P: [`pqIntertwiningOuterLevi`](../../Langlands/Representation/Intertwining/PQIntertwiningOuterLeviProof.md) |
| VII.3.5 opening assertion "`d(P, Q)` is the length of the element `w ∈ W(A_M)` with `w · P = Q`" | 236 / 242 | `Langlands.GroupScheme.MinimalParabolicDistanceLengthStatement` (minimal `M`, corrected form) | P: `minimalParabolicDistanceLength` (`Langlands/GroupScheme/Rational/MinimalParabolicDistanceLengthProof`; Task 5687, statement candidate `5d306e19`). For non-minimal `M` the printed assertion is a source issue (I1 below) |

## VII.4 The Langlands classification

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| VII.4.1 Definition (Langlands triplet) | 241 / 247 | `IsLanglandsTriplet`, chambers `Langlands.GroupScheme.restrictedCorootChamber` (`LanglandsClassification/LanglandsTriplet`) | D |
| VII.4.1 Lemma | 241 / 247 | `RP.LanglandsTripletOppositeRegularityStatement`; proved steps `RP.LanglandsTripletOppositePieceSeparationStatement`, `RP.LanglandsTripletOppositeRegularityReductionStatement` | P: `langlandsTripletOppositeRegularity` (`LanglandsClassification/LanglandsTripletRegularityProof`; task 78bf8d31); steps P |
| (VII.4.1.1), cone for the tempered exponent contribution | 241 / 247 | `RP.GeometricLemmaIntersectionDatum.normalizedRealPart_sub_unramifiedPieceRealPart_mem_nonnegCone`, `Langlands.GroupScheme.ParabolicRootPresentation.neg_mem_nonnegCone_of_opposite` | P as the `hxQ` and `hxP` steps of `langlandsTripletOppositePieceSeparation`. The bound is on the full geometric-lemma piece's exponent after subtracting its unramified contribution |
| (VII.4.1.2), nonzero negative-cone shift for the unramified contribution | 241–242 / 247–248 | `RP.GeometricLemmaIntersectionDatum.unramifiedPieceDisplacement_mem_nonnegCone_and_ne_zero` | P as the `hδ` step of `langlandsTripletOppositePieceSeparation`. Lean uses the original inducing real part minus the piece parameter, so the displacement lies in the nonnegative cone of \(P\) |
| VII.4.2 Theorem (i)–(iii) | 243–246 / 249–252 | `RP.LanglandsQuotientUniqueStatement`, `RP.LanglandsQuotientInjectiveStatement`, `RP.LanglandsQuotientExhaustiveStatement`, conjunction `RP.LanglandsClassificationStatement` | S: Task 5295 (`717df3ca-7a3c-40fc-a8b3-79617086393e`). P for `RP.LanglandsClassificationFromInputsStatement`, with four Chapter VI premises. See the proof receipts below and source issue I9 |
| VII.4.2 sentence after the proof of (i), exponent characterization of `J(P, σ, ψ)` | 243 / 249 | `RP.LanglandsQuotientExponentCharacterizationStatement` | S: Task 5653 (`1df73c68-230c-4ced-8325-dc9c910df8d8`). P for `RP.LanglandsQuotientExponentCharacterizationFromSecondAdjointnessStatement`, with second adjointness as its sole premise |

In (VII.4.1.1)–(VII.4.1.2), the compatible presentation of \(P\) comes from the
Langlands triplet. The proof obtains an opposite presentation on the same split
component and uses Jacquet admissibility of the twisted source. For a hypothetical
common exponent, its tempered offset \(x\) lies in the opposite cone. Hence \(-x\) and
the nonzero displacement \(\delta\) lie in the cone of \(P\). Pointedness gives
\(-x+\delta\ne 0\), contradicting equality of the exponent real parts.
[Piece separation proof](../../Langlands/Representation/LanglandsClassification/LanglandsTripletOppositePieceSeparation.md)

### VII.4.2 conditional proof publications

The two implication proofs below have independently approved publications. Their
Lean and Markdown pairs and the pairs of their target implications match the
corresponding frozen records. Both proofs were validated with `lake-build`,
`exact-target`, `unchanged-statement` and `frozen-inputs`.

| Target implication | Statement record | Proof record | Integration ID | First Library commit of proof |
| --- | --- | --- | --- | --- |
| `LanglandsClassificationFromInputsStatement` | `5ca1c954-6ef1-4929-a40c-67f07d378daa` | `cd3326ce-0b34-4b95-aaf3-77c0429d2d60` | `9369e828df9a4a8b8c2429ffa25fde99` | `85c2fe719cf62e96f22aaf4ca03961c5814d086b` |
| `LanglandsQuotientExponentCharacterizationFromSecondAdjointnessStatement` | `45af50ab-3e52-492e-9f83-383d1f51f434` | `2a777930-54db-4d08-967d-a9d8961fc7e1` | `799cdd36dd0740699679cff4871c73c2` | `51e4d8972659f1ffcf0ca89e8eee9540a30b52d3` |

- `langlandsClassificationFromInputs` proves all three parts at independent
  field and representation-carrier universes `u, v`. It takes second adjointness
  (`RP.LeviSecondAdjointnessStatement`, VI.9.6, Task 4834), finite length under
  normalized induction and Jacquet restriction (`RP.LeviInductionFiniteLengthStatement`,
  `RP.LeviJacquetFiniteLengthStatement`, VI.6.2 and VI.6.4, Task 4950), and
  irreducible admissibility (`Langlands.Aubert.General.RationalPointsIrreducibleAdmissibleStatement`,
  VI.2.2, Task 3838). Part (i) uses finite length to obtain a quotient and the
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
| VII.5 notes | 246 / 252 | X: attributions ([2], [20], [22], [23], [45], [40]). The notes also say that VII.1.3 is the point that makes the small progenerators of VI.10.1 generators; that use is in the proofs of the VI.10.1 statements (task 2174cd68). |

## Proof-publication update, 14 November 2026

The four updated targets above have independently accepted, published proofs. This update
compares their Lean and paired Markdown with the original VII.3.4–VII.3.5 passage, printed
pp.235–240 / PDF pp.241–246. The following five records cover four theorems: the two composition candidates were reconciled in one
publication. Each record has accepted `lake-build`, `exact-target`, `unchanged-statement`
and `frozen-inputs` validation and an independent approval with no unresolved reviewer
qualifications. A fresh development check of the four proof modules at this update's
Library base also passed with no errors or warnings; that check supplies no new acceptance.

| Item | Accepted proof record | Independent reviewer | Integration ID | Published Library commit |
| --- | --- | --- | --- | --- |
| VII.3.4 integral form | `cfa9bc6a-506a-4d89-8b13-86a0ca905087` | Reviewer 1317 | `39a092dec63b4923808aea884e259cdb` | `0c3f30c24701c74d5474fca3fbb5324a99aa1d58` |
| VII.3.5 (i) | `2bd19057-d8bd-4bd1-a40c-54afb1cb3d10` | Reviewer 1532 | `5a98f8dc42274be4b6a78d776fb0ed59` | `85c2fe719cf62e96f22aaf4ca03961c5814d086b` |
| VII.3.5 (i), second record | `0ab62d05-6540-41ef-8778-105294258c9a` | Reviewer 1530 | `0492b024d4c3487d837321a52d1dd747` | `85c2fe719cf62e96f22aaf4ca03961c5814d086b` |
| VII.3.5 (ii) | `64fe3428-fe9d-45d4-a0f7-88ae3b2901b1` | Reviewer 792 | `43753bcc2a7145a199cdbcbd9fa8d858` | `51e4d8972659f1ffcf0ca89e8eee9540a30b52d3` |
| VII.3.5 (iii) | `488670d4-d2a7-4a09-a0d7-802ff94acd9c` | Reviewer 731 | `e661f82017ed4436bde3fc8de137ce89` | `51e4d8972659f1ffcf0ca89e8eee9540a30b52d3` |

The integral, inner-Levi and outer-Levi pairs at this update's base equal their frozen
accepted pairs. For composition, the Lean file equals the first composition record's frozen Lean;
the Markdown equals the joint publication's file and credits Workers 48 and 102. It
documents the retained term using `pqCompositionHaar`, whose proof applies
`pqCompositionHaar_of_product` to `pqCompositionProduct`. It does not equal either
candidate's frozen Markdown. The published Lean and explanation agree.

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
  norm or topology on the representation space. Worker 48 constructs the integral,
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
  Worker 115's proof uses the actual integration-domain homeomorphism, Haar transport,
  the stage map and boundary transfer, and uniqueness of integral-normalized maps.
- **VII.3.5 (iii), statement p.237 / PDF p.243, proof pp.238–240 / PDF pp.244–246.**
  Represented `Qᵢ = LUᵢ` contain `Pᵢ`, share the same embedded `L`, and have a common
  represented intersection `P'` in `L`, with the stated opposites and split components
  of `M` and `L`. For `X = i_{P'}^L(σ)`, `Q₁Q₂`-regularity of `X` implies
  `P₁P₂`-regularity of `σ`. The theorem transports Haar measures from `Ū₁ ∩ U₂` to
  `N̄₁ ∩ N₂`, constructs the first stage function with `δ_{U₁}^(-1/2)`, and proves
  `J_Q(f̃)(g)(x) = δ_{U₂}(x)^(-1/2) J(f)(emb(x)g)` for supplied normalized maps.
  Worker 86 identifies the integration domains, transports their measures, and proves
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
  proved) compares the temperedness conditions.

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
  `MinimalParabolicDistanceLengthStatement` (candidate `5d306e19`), proved by
  `minimalParabolicDistanceLength` (Task 5687; see the proof-status update in the introduction); the non-minimal case is
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
  submultiplicativity of double-coset indices. The erratum was published as
  `788b0d0e-249b-4373-b5d9-ceda26630c5e` under integration
  `6200a3ebc33340ab94634280b08ae0f0`.
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
  The erratum was published as `46ab9a9d-e57b-4008-85dc-0ef828114c63`
  under integration `48af4d8510f14bf3bd00bb2d289bbb72`.
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
  \(\mathrm{SL}_3\) examples was published as `a9e9412e-cbe1-4ccf-afbe-0e15fa5de41f`
  under integration `4d4aaf5f35464b3b8b47811a0a2bc608`.
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

1. VII.1.2: sufficiency of the strictly positive root-cone condition in
   `RP.ArbitraryParabolicCasselmanCriterionStatement`. The exact equivalence
   remains open in Task 4712 (`2e8d370f-f1ed-4ad4-a529-5083212ebae0`). Task
   8060 supplies the intermediate target with Bruhat–Tits availability.
2. VII.1.3 Corollary: projection existence, faithfulness, the adjunction unit
   isomorphism and equivalence in `RP.MaximalLeviBlockProjectionEquivalenceStatement`
   remain the proof target of Task 6621 (`3c3f4d9e-2356-4208-bf0b-c349909b7520`).
   The published `RP.maximalLeviBlockProjectionEquivalenceOfDecompositionOfBlocks`
   derives the exact proposition from the VI.3.3.1 inertia decomposition
   `CuspidalSupport.RationalCuspidalInertiaDecompositionStatement` and
   `RP.MaximalLeviBlockStatements`, which are still statement-only.
   Its three definition records are `11c6dc2a-f4d9-4a09-85a9-a9027bddd060`,
   `59f59e4d-b105-4585-808f-a59c239a378f` and
   `bc01b73d-3aca-46ab-adbd-a9503974bd1e`. The source's last step applies the
   adjunction triangle to the isomorphic counit, then reflects the resulting
   unit isomorphism through the exact faithful `r_D`.
   [Published conditional reduction](../../Langlands/Representation/Exponents/MaximalLeviBlockProjectionReduction.md)
3. VII.4.2: the unconditional classification and its exponent characterization
   await the Chapter VI premises named above. Second adjointness suffices for
   the characterization and for the injectivity part of the classification.

Update at Library `9951a27f`: the VII.3.5 gap on the minimal-`M` form of the
opening assertion is stated by the published `MinimalParabolicDistanceLengthStatement`
(candidate `5d306e19`, proof Task 5687). For non-minimal `M`, and for the length
relative to `P_∅` when `P ≠ P_∅`, the printed assertion fails as written (I1).
`6a38904d` is the published unconditional VII.4.2 exponent characterization
statement (Task 5653). `9492bbaa` (VII.2.6 Remark and the VII.3.1 extremes of the
Bruhat order) is published, with proof Task 5685.
