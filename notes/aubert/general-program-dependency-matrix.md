# General Aubert duality: declaration and dependency matrix

This matrix covers all five families of the standalone program
`46df6a68-5db4-4428-8044-05151d6ce1f6` (Task 3640), revision 1. Declaration
names, proof status and premise boundaries are pinned to Library commit
`642008d6b3b837d8bd76de0cabcaff3db00088c0`, checked on 11 November 2026.
This refresh replaces the version pinned to
`e748734106ab2ee9de1cab1eb18a60e59593aac0`. Since that commit, Aubert's
Theorem 2.3 has been proved (`A.aubertTheorem23`), so every listed Family 5
target is now proved or closes by composition. A second published route
derives cuspidal Jacquet-factor extraction from special-vertex inputs. On that
route, Renard VI.3.5 is no longer needed for extraction or for the targets
that only use extraction or its inputs. VI.3.5 remains the only unproved input
of support decomposition, induction-Jacquet stability and Sharp support
retention.

Earlier refreshes recorded the following. Between
`de0bad590ef480242ebae25ab2b43072096ee2a5` and `e7487341` the coatom
Jacquet-length budget was proved. Between
`5263a53b575d66cc4ebc5364c0d990d1b111c7f7` and `de0bad59` the rational
Jacquet compatibility target was proved. Between
`e449cde988d4e97ab280b8d4d11262887ccc26e0` and `5263a53b` the rational
geometric K0 expansion and the rank-one geometric Jacquet target were proved.
The [earlier coverage snapshot](general-program-coverage.md) records an older
state still, and its missing-target inventory is not the current status.

The [corrected source map](general-program-source-map.md) supplies the original
reading record and correction ledger. This matrix reuses that reviewed source
account and the companion declaration maps linked below. It makes no
additional original-literature reading claim. It records constructions,
proposition targets, retained premises and proof status. It does not establish
completion of any of the five families.

## Scope and interpretation

Write `R` for the namespace
`Langlands.Aubert.General.RationalPointFamily`, `A` for `Langlands.Aubert`
and `GS` for `Langlands.GroupScheme`. An unqualified rational declaration in
the tables belongs to `R`. Links name the actual Lean files; their same-stem
Markdown explains the source correspondence.

The closed rational targets quantify over every nonarchimedean local field,
connected reductive group, maximal split torus and generic cocharacter. They
use actual rational points with canonical `pointTopology` and actual simple
relative roots, including the empty set. Field and representation universes
`u` and `v` are independent; the representation carrier is in
`max (u + 1) v`. No restriction to split, quasisplit, characteristic-zero or
GL groups is introduced.

The actual Weyl group has denominator the point centralizer,
`N_G(T₀)/Z_G(T₀)`. Its Levi subgroups use `N_{L_I}(T₀)/Z_G(T₀)`, with
`L_∅ = Z_G(T₀)`. A finite Coxeter group on unrelated labels cannot replace the
point normalizer and centralizer comparisons.

### Status vocabulary

The status of each main target is one of the following.

- **Proved.** The Library contains a theorem whose type is exactly the target
  proposition, with no further parameters. The theorem is named.
- **Closes by composition.** Published theorems compose to the exact target
  with no further parameters. Worker 3640 compiled the composite in a private
  draft against environment `bb168ec3-1031-46d9-816b-5c2ed7bbe1a6` with zero
  errors and only the axioms `propext`, `Classical.choice` and `Quot.sound`.
  A private compilation is not a publication: the owning task must still
  publish the proof.
- **Reduced.** A published theorem proves the target from named propositions,
  and at least one of them is unproved. The unproved inputs are listed. Where
  a chain of published reductions leaves only a named unproved proposition,
  the row says so. For the chains below through Renard VI.3.5 or through the
  special-vertex inputs, Worker 3640 compiled the conditional composites in a
  private draft, with the same environment, zero errors and the same three
  axioms as for **Closes by composition**.
- **Open.** No published reduction exists.

Proof status was determined by a scripted scan of the Library for theorems
whose stated type is a target proposition, followed by reading the
signatures. Staged, reviewed or approved candidates that are not yet
integrated are mentioned separately and are never counted as proofs.

Only the itemized external assertions S01–S23 in the
[Renard Chapter V ledger](../renard/chapter-v-structural-inputs.md) may form the
permitted external structural boundary. D01–D08, including D07's Haar and
root-product modulus formulas, remain in-book proof obligations. A named
intermediate predicate is not automatically one of the permitted S rows.

## Structural statements now proved

The following group-scheme propositions, which earlier snapshots treated as
retained structural inputs, have premise-free proofs at this commit:

| Proposition | Proof |
| --- | --- |
| `GS.StandardCocharacterStatement` | `GS.standardCocharacter` |
| `GS.RelativeRootSystemStatement` | `GS.relativeRootSystem` |
| `GS.StandardParabolicOrderStatement` | `GS.standardParabolicOrder` |
| `GS.StandardParabolicEndpointsStatement` | `GS.standardParabolicEndpoints` |
| `GS.StandardLeviIntersectionStatement` | `GS.standardLeviIntersection` |
| `GS.StandardLeviConjugationStatement` | `GS.standardLeviConjugation` |
| `GS.RelativeWeylCoxeterStatement` | `GS.relativeWeylCoxeter` |
| `GS.StandardParabolicPointsStatement` | `GS.standardParabolicPointsStatement_proof` |
| `GS.GenericCentralizerStatement` | `GS.genericCentralizer` |
| `GS.RationalBruhatStatement` | `GS.rationalBruhat` |
| `Langlands.BruhatTits.DynamicParabolicQuotientCompactStatement` | `Langlands.BruhatTits.dynamicParabolicQuotientCompact` |

`R.rationalWeylComparison` proves the point normalizer and centralizer
comparisons. These are proved propositions. Their use inside a final main
proof still needs the per-instance premises of each rational target, such as
closed subgroups, compact limits and finite-length preservation, to be
supplied at that target's scope. This matrix does not audit how the proofs
above map to the S rows.

## Operator premises and representation inputs

The [rational formal-target map](rational-formal-target-map.md) gives the full
binder groups.

| Input group | Actual declarations or conditions | Meaning for closure |
| --- | --- | --- |
| Standard family and roots | `GS.StandardCocharacterStatement`, `HasRelativeRootSystem`, connected reductivity, maximal split torus and generic cocharacter | Constructs the actual standard parabolic, Levi and radical family and finite simple-root indexing. The statement-level inputs are proved (table above). |
| Ambient topology | Local compactness, nonarchimedean group structure and Hausdorffness of canonical rational points; closed standard `P` and `U`; continuity of the derived Levi projections; `IsLimitOfCompactSubgroups` for each `U` | Supplies the hypotheses of the existing exactness and normalization adapters. Compact-limit means every compact subset lies in a compact subgroup. |
| Ambient finite length | Separate `hiFl` and `hrFl`: actual normalized induction and Jacquet functors preserve finite length | Representation-theoretic obligations, carried by `DynamicInductionFiniteLengthStatement` and `DynamicJacquetFiniteLengthStatement`. |
| Restricted Levi family | `StandardLeviIntersectionStatement`, closed `M`, continuous inside-Levi projections, compact-limit restricted radicals, separate `hiLFl` and `hrLFl` | Constructs Levi-in-Levi terms. `R.rationalLeviFiniteLengthStatement` proves `RationalLeviFiniteLengthStatement`. |
| Actual Weyl transport | `StandardLeviConjugationStatement`, point normalizer and centralizer comparisons, an actual finite Coxeter system, `RootLengthComparison`, `PositiveSimpleReflectionComparison`, `minimalityLengthCriterion`, `associatedSubsetLaws` | Identifies longest representatives and associated Levis. The conjugation statement and the comparisons are proved. |
| Smooth dual | Actual `ContragredientPreservesFiniteLength` and the exactness/cofinality inputs to `contragredientK0` | Representation-theoretic finiteness for the smooth dual. |

The six representation prerequisites in
[PrerequisiteStatements](../../Langlands/Representation/Aubert/General/PrerequisiteStatements.lean)
are all **open**, each with a focused proof task:

| Proposition | Proof task |
| --- | --- |
| `RationalPointsFiniteLengthAdmissibleStatement` | `aa8bb3a4-42d3-47db-9a48-98eb87ad9327` |
| `DynamicLeviFiniteLengthAdmissibleStatement` | `96949545-6354-4d63-93f7-0e5ca1e6fdfe` |
| `RationalPointsContragredientFiniteLengthStatement` | `3591f7ea-ad5b-4993-a0a0-e6e74f09a28b` |
| `DynamicLeviContragredientFiniteLengthStatement` | `05a3f022-0da7-4f43-9fe8-de5b6d368de4` |
| `DynamicInductionFiniteLengthStatement` | `174d2de0-fa21-41b4-b091-f1b86481790b` |
| `DynamicJacquetFiniteLengthStatement` | `73e60be8-481a-4cea-b464-eed3bd89be7f` |

The six statements are representation-theoretic obligations, not structural
inputs. Admissibility, Howe finite length, adjunctions, geometric
filtrations, cuspidal support and induced-class Weyl invariance must be
proved wherever they are used.

## Families 1 and 2: actual operator and formal identities

Source locators: Aubert 1995, Definition 1.5 and Theorem 1.7, printed
pp.2181–2183, and Corollary 1.10, p.2183. The operator is the unadjusted sum
`∑ I, (-1)^|I| i_I r_I` on the actual exact finite-length Grothendieck group.
The constructions `rationalAlternatingOperator`,
`rationalAlternatingOperator_ofRepresentation`,
`standardParabolicFiniteLength` and the restricted
`rationalLeviAlternatingOperator` are published in
[RationalAlternatingOperator](../../Langlands/Representation/Aubert/General/RationalAlternatingOperator.lean)
and
[RationalLeviFiniteLength](../../Langlands/Representation/Aubert/General/RationalLeviFiniteLength.lean).

| Main target | Status at `642008d6` | Remaining inputs and evidence | Proof task |
| --- | --- | --- | --- |
| `RationalCuspidalEigenvalueStatement` | Proved: `rationalCuspidalEigenvalue` | None. | — |
| `RationalGeometricK0ExpansionStatement` | Proved: `rationalGeometricK0Expansion` | None. The proof applies `rationalGeometricK0Expansion_of_standardParabolicPoints` to `GS.standardParabolicPointsStatement_proof`. | `f722f1c6-147e-453e-8664-02b7822b7bce` (completed) |
| `RationalJacquetCompatibilityStatement` | Proved: `rationalJacquetCompatibility` | None. The proof applies `rationalJacquetCompatibility_of_rationalGeometricK0Expansion` to `rationalGeometricK0Expansion`. | `47650cf4-dbb8-4197-8730-4f9848d22955` (completed) |
| `RationalInductionCompatibilityStatement` | Reduced | `rationalInductionCompatibility_of_expansion_and_inducedWeyl` needs the geometric expansion (proved) and `RationalInducedK0WeylConjugacyStatement`. | `475f7a39-11ad-4748-87b3-cfaef16a59cb` |
| `RationalInducedK0WeylConjugacyStatement` and `RationalInducedClassWeylConjugacyStatement` | Reduced | The two are equivalent by published theorems. `rationalInducedK0WeylConjugacy_of_genericIso` needs the two admissibility prerequisites and `RationalSameLeviGenericInductionIsoStatement` (proof task `ba00e20e-ea55-4b97-89cc-2e9127ada887`). | `f85448c5-077a-467f-8121-66e53755fae0`, `03e05250-cda0-4d0b-a3de-d0291194f10b` |
| `RationalInvolutivityStatement` | Reduced | `rationalInvolutivityStatement_of_reductions` needs induction compatibility, `RationalTermTransitivityStatement` and `RationalTopTermStatement`. The last two have no published proof; the involutivity task has a shared draft for term transitivity. Intersection and Levi finite length are proved. | `2f01b264-fb0e-4029-901c-009044feaa97` |
| `RationalContragredientCommutationStatement` | Reduced | `rationalContragredientCommutation_of_schemeWeylDuality` needs induced-class Weyl conjugacy and the two admissibility prerequisites. Its Coxeter, conjugation, opposite-transport and natural-duality inputs are proved. A second reduction needs `RationalContragredientTermComparisonStatement`. | `54d4578e-fc6b-4995-abf4-1ca845f4ebab` |
| `RationalCorollary110aStatement` | Open | No published reduction. | `892c3af1-7d30-4200-b80a-f90740c269d2` |
| `RationalCorollary110bStatement` | Reduced | `rationalCorollary110bFromRankOneInputs` needs `RationalRankOneSelfAssociationStatement`, `RationalRankOneJacquetModulesStatement` and induced K0 Weyl conjugacy. The second reduces to cuspidal Jacquet-factor extraction alone (below). | `053e93d1-59ac-48f0-bbe0-38b26225fe46` |
| `RationalRankOneSelfAssociationStatement` | Reduced | The published bridge `rationalRankOneSelfAssociation_of_maximalLeviSupercuspidalReducibility` needs only Renard VII.1.3, `MaximalLeviSupercuspidalReducibilityStatement` (proof task `004e00e1-5995-4dc1-884e-a5f512150d0c`). | `46f751c8-0d69-40a6-ab67-4c19be8fc4c9` |
| `RationalRankOneLengthTwoStatement` | Reduced | `rationalRankOneLengthTwo_of_extraction` needs only cuspidal Jacquet-factor extraction. It composes `rationalRankOneLengthTwoFromInputs`, `rationalMaximalCuspidalJacquetDetectionFromExtraction` and the proved budget `rationalMaximalCuspidalJacquetBudget` (proof task `cdc95bfc-a501-4693-a1d3-fcc890aee15b`). `rationalRankOneLengthTwo_of_wholeStatement` derives the target from VI.3.5. Either VI.3.5 or the special-vertex inputs suffices (Family 3). | `c53e3363-ffa5-4f01-ae77-aca8e1f49117` |
| `RationalRankOneJacquetModulesStatement` | Reduced | `rationalRankOneJacquetModules_of_extraction` needs only cuspidal Jacquet-factor extraction. Either VI.3.5 or the special-vertex inputs suffices (Family 3). The older reduction `rationalRankOneJacquetModules_of_lengthTwo_extraction_geometry` also needs length two. | `1244dad8-89c0-4c13-95f7-1942ccf77842` |

Proved helpers used above: `rationalNaturalInductionDuality`,
`rationalNaturalJacquetDuality`, `rationalLeviFiniteLengthStatement`,
`rationalWeylComparison`, and the structural proofs listed earlier.

## Family 3: corrected actual complex and terminal comparison

Source: Aubert 1995, pp.2186–2187, corrected by the erratum, pp.4687–4690,
and the two-sided filtration and actual-map repair in Ban–Jantzen §4,
pp.160–162. The
[complex source map](smooth-complex-construction-source-map.md) and
[support/filtration source map](support-filtration-consequences-source-map.md)
explain the source correspondence. The actual complex, its differential,
initial identification and terminal cokernel `E#` are published constructions
in
[RationalStandardComplex](../../Langlands/Representation/Aubert/General/RationalStandardComplex.lean)
and
[RationalCorrectedTheorem36](../../Langlands/Representation/Aubert/General/RationalCorrectedTheorem36.lean).

| Main target | Status at `642008d6` | Remaining inputs and evidence | Proof task |
| --- | --- | --- | --- |
| `RationalCorrectedTheorem36Statement` | Reduced | `rationalCorrectedTheorem36_of_inputs` needs `RationalCorrectedExactnessInputs`: Bruhat (proved), graded vanishing, graded transition (proved), support induction-Jacquet stability (reduced to VI.3.5 alone, below) and exactness detection. | `613611a4-9c0e-43e3-82aa-f91d2044cfe2` |
| `RationalCorrectedGradedVanishingStatement` | Open | No published reduction. | `277860be-2aeb-4a85-8ccb-f1e2e5c573b9` |
| `RationalCorrectedGradedTransitionStatement` | Proved: `rationalCorrectedGradedTransitionStatement` | None. | — |
| `RationalFixedLeviComparisonStatement` | Proved: `rationalFixedLeviComparison` | None. | — |
| `RationalAssociatedLeviComparisonStatement` | Reduced | `rationalAssociatedLeviComparisonStatement_of_published` needs only graded vanishing. Its other six inputs (Bruhat, dynamic quotient compactness, surviving support, orbit-radical intersection, squared orbit modulus, graded transition) are proved. | `f7d95940-33d0-49d3-93d6-8d5ff8d89373` |
| `RationalJacquetCuspidalStatement` | Reduced | `rationalJacquetCuspidal_of_jacquetVanishing` needs support Jacquet vanishing. Either VI.3.5 or the special-vertex inputs suffices. | `b752450b-5e2d-4cb3-95f4-3812331c0b8a` |

The nine support-category targets are in
[RationalSupportCategoryTargets](../../Langlands/Representation/Aubert/General/RationalSupportCategoryTargets.lean).

| Support target | Status at `642008d6` | Remaining inputs | Proof task |
| --- | --- | --- | --- |
| `RationalCuspidalSeriesExistenceStatement` | Proved: `rationalCuspidalSeriesExistence` | None. | — |
| `RationalSupportCategoryAssociationInvarianceStatement` | Proved: `rationalSupportCategoryAssociationInvariance` | None. | — |
| `RationalCuspidalSupportAssociationStatement` | Reduced | Cuspidal Jacquet-factor extraction. Either VI.3.5 or the special-vertex inputs suffices. | `fc414cb1-5832-4033-a2aa-d7c27f5e4691` |
| `RationalSupportCategoryIrreducibleJacquetDetectionStatement` | Reduced | Cuspidal Jacquet-factor extraction. Either VI.3.5 or the special-vertex inputs suffices. | `b7887025-20b3-4c11-9fad-0e70bdf59da6` |
| `RationalSupportCategoryJacquetVanishingStatement` | Reduced | Dynamic quotient compactness (proved) and support association. Either VI.3.5 or the special-vertex inputs suffices. | `bc64458d-2bc4-438a-9992-ba06185affa7` |
| `RationalSupportCategoryDecompositionStatement` | Reduced | `RationalCuspidalInducedEmbeddingStatement` (task `198824c2-4e2f-40c1-94a0-07fa748bede9`), `RationalInducedCuspidalSupportCategoryStatement` (task `c79b0cd0-661f-4239-9f65-483d6f319480`) and support association. The first follows from VI.3.5 by `rationalCuspidalInducedEmbedding_of_wholeStatement`; its other published reduction needs `RationalLeviJacquetCuspidalRemainderSplittingStatement`, which also has only VI.3.5 reductions. The second follows from VI.3.5 by `rationalInducedCuspidalSupportCategory_of_wholeStatement`, and from the extraction inputs by `rationalInducedCuspidalSupportCategory_of_extractionInputs`. Only VI.3.5 remains. | `8452c8a4-3686-47c2-80cf-c4ff4e16b3b2` |
| `RationalSupportCategoryInductionJacquetStatement` | Reduced | Decomposition, `RationalLeviJacquetCuspidalRemainderSplittingStatement` and support association. The splitting follows from VI.3.5 by `rationalLeviJacquetCuspidalRemainderSplitting_of_wholeStatement`. Only VI.3.5 remains. | `09268952-5848-4585-90e4-0a12121c60ef` |
| `RationalSupportCategoryZeroDetectionStatement` | Open | No published reduction. | `db02aabd-9901-4fae-9583-ec28c66aec3c` |
| `RationalSupportCategoryExactnessDetectionStatement` | Open | No published reduction. | `d70a1edd-5a84-4b03-aecf-2818901809d4` |

`RationalCuspidalJacquetFactorExtractionStatement` has proof task
`e6add7c5-44c5-45ea-afe9-7f48c98fb927`. Its published reduction
`rationalCuspidalJacquetFactorExtraction_of_inputs` needs
`RationalCuspidalExtractionInputsStatement`. Two published theorems derive
those inputs, and both of their premises are unproved:

- `rationalCuspidalExtractionInputs_of_wholeStatement` derives them from
  Renard VI.3.5, the whole-category cuspidal splitting
  `Langlands.CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement`
  (module `Langlands.Representation.CuspidalSupport.RationalWholeCuspidalDecompositionStatement`,
  proof task `4bee987a-093b-4054-bd65-7360168351d2`).
- `rationalCuspidalExtractionInputs_of_specialVertexInputs` (module
  [RationalCuspidalExtractionFromSpecialVertex](../../Langlands/Representation/Aubert/General/RationalCuspidalExtractionFromSpecialVertex.lean))
  derives them from the special-vertex inputs
  `Langlands.CuspidalSupport.RationalSpecialVertexCompactInputsStatement`.
  The published `CuspidalSupport.rationalSpecialVertexCompactInputs_of_jointBasis`
  derives those from
  `Langlands.BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement`
  (proof task `8c39faa0-2a70-4fc4-a027-914987aba924`). This route does not use
  VI.3.5. The module also publishes
  `rationalCuspidalJacquetFactorExtraction_of_specialVertexInputs` and
  `rationalCuspidalJacquetFactorExtraction_of_jointBasis`.

"Only VI.3.5 remains" in the rows of Families 1–4, and the VI.3.5 alternative
in "Either VI.3.5 or the special-vertex inputs suffices", mean the following.
Worker 3640 compiled, as described under the status vocabulary, theorems
that derive each of these targets at universes `u, v` from the single
hypothesis `RationalWholeCuspidalCategoryDecompositionStatement.{u, max (u + 1) v}`:
extraction, support association, irreducible Jacquet detection, support
Jacquet vanishing, Jacquet cuspidality, induced cuspidal support,
decomposition, induction-Jacquet stability and Sharp support retention. They
use only the published theorems
`rationalCuspidalExtractionInputs_of_wholeStatement`,
`rationalCuspidalJacquetFactorExtraction_of_inputs`,
`rationalCuspidalSupportAssociation_of_cuspidalJacquetFactorExtraction`,
`rationalSupportCategoryIrreducibleJacquetDetection_of_cuspidalFactors`,
`rationalSupportCategoryJacquetVanishing_of_dynamicCompact_and_association`
with `Langlands.BruhatTits.dynamicParabolicQuotientCompact`,
`rationalJacquetCuspidal_of_jacquetVanishing`,
`rationalInducedCuspidalSupportCategory_of_wholeStatement`,
`rationalCuspidalInducedEmbedding_of_wholeStatement`,
`rationalSupportCategoryDecomposition_of_inducedCuspidal`,
`rationalLeviJacquetCuspidalRemainderSplitting_of_wholeStatement`,
`rationalSupportCategoryInductionJacquet_of_decomposition_splitting_and_association`
and `rationalSharpSupportRetention_of_inductionJacquet`. The same draft
derives the rank-one Jacquet-module target from that hypothesis alone,
adding `rationalRankOneJacquetModules_of_extraction`. It also derives the
rank-one length-two target from that hypothesis alone, adding
`rationalMaximalCuspidalJacquetDetectionFromExtraction`,
`rationalRankOneLengthTwoFromInputs` and the proved
`rationalMaximalCuspidalJacquetBudget`. The published theorem
`rationalRankOneLengthTwo_of_wholeStatement` now has the same type and route.

Its special-vertex alternative means the following. A second private
composite of Worker 3640 derives extraction, support association,
irreducible Jacquet detection, support Jacquet vanishing, Jacquet
cuspidality, induced cuspidal support, the rank-one Jacquet modules and
rank-one length two at universes `u, v` from the single hypothesis `RationalSpecialVertexCompactInputsStatement.{u}`. It uses
`rationalCuspidalJacquetFactorExtraction_of_specialVertexInputs`,
`rationalCuspidalExtractionInputs_of_specialVertexInputs`,
`rationalInducedCuspidalSupportCategory_of_extractionInputs`,
`rationalRankOneLengthTwo_of_extraction` and the extraction-based reductions
listed above. Composing with
`CuspidalSupport.rationalSpecialVertexCompactInputs_of_jointBasis` gives the
same targets from `JointSpecialCompactBasisExistenceStatement.{u}`. Support
decomposition, induction-Jacquet stability and Sharp support retention are not
on this route: the cuspidal induced embedding and the Levi-Jacquet remainder
splitting have only VI.3.5 reductions.

The terminal cokernel `E#` survives; there is no final zero asserting its
vanishing. Proposition 3.2 remains unresolved, and neither its failed proof
nor the original application establishes any row of this matrix.

## Family 4: finite length, irreducibility and actual involution

Source: Corollary 3.9, printed p.2189, with the corrected complex and erratum
p.4690. All six targets are in
[RationalSharpConsequenceTargets](../../Langlands/Representation/Aubert/General/RationalSharpConsequenceTargets.lean).

| Main target | Status at `642008d6` | Remaining inputs | Proof task |
| --- | --- | --- | --- |
| `RationalSharpFiniteLengthStatement` | Open | No published reduction. | `0da1c37e-a39a-42e1-b90d-135db6c6e5c3` |
| `RationalSharpClassFormulaStatement` | Open | No published reduction. | `13e2abdc-2be7-4191-b74b-9eae99a56fcc` |
| `RationalSharpSupportRetentionStatement` | Reduced | `rationalSharpSupportRetention_of_inductionJacquet` needs support induction-Jacquet stability. Only VI.3.5 remains (Family 3). | `d441ca88-a2fa-4174-93e0-97d1b9fca9ba` |
| `RationalSharpIrreducibleStatement` | Open | No published reduction. | `44d0ed8c-18a6-44f8-8836-dc351694e9d9` |
| `RationalSharpCuspidalSeriesStatement` | Open | No published reduction. | `6316db5a-5618-43bb-a920-eadd3a912b88` |
| `RationalSharpInvolutionStatement` | Reduced | `rationalSharpInvolutionStatement_of_inputs` needs dynamic induction and Jacquet finite length, K0 involutivity, the class formula and cuspidal-series retention. | `9d570c9e-e376-4437-8d15-3cbe9e9a0027` |

Corrected exactness, termwise exactness, length and Euler arguments, support
and nonvanishing must be supplied where used. Equality of exact-K0 classes
does not imply isomorphism of modules.

## Family 5: actual GL specialization and the whole graded ring

Source: Aubert 1995, Definition 2.1, Remark 2.2 and Theorem 2.3, printed
pp.2184–2185. The [GL target map](gl-specialization-source-map.md),
[general-specialization addendum](gl-general-specialization.md) and
[point-topology comparison](gl-algebraic-point-specialization.md) give the
model and dependency boundaries.

| Target | Status at `642008d6` | Evidence or remaining inputs |
| --- | --- | --- |
| `Langlands.Parabolic.GeneralLinearModulusCompatibility` | Proved: `Langlands.Parabolic.generalLinearModulusCompatibility` | Full Haar-to-block modulus comparison in every rank, including rank zero. |
| `A.generalAlternatingOperator_eq` with its modulus premise discharged | Closes by composition | `A.generalAlternatingOperator_eq F T n (fun B => Parabolic.generalLinearModulusCompatibility F T B)` identifies the general unadjusted operator on the GL block families with `A.alternatingOperator` in every rank. The comparison is for `PadicField` models. |
| `A.BinaryProductExactnessStatement` | Proved: `A.binaryProductExactness` | — |
| `A.GradedInductionRingLawsStatement` | Proved: `A.gradedInductionRingLaws` | — |
| `A.SegmentPolynomialComparisonStatement` | Proved: `A.segmentPolynomialComparison` | — |
| `A.AdjustedSegmentExchangeStatement` | Proved: `A.adjustedSegmentExchange` | — |
| `A.AdjustedInvolutivityStatement` | Proved: `A.adjustedInvolutivity` | — |
| `A.AdjustedHomogeneousMultiplicativityStatement` | Proved: `A.adjustedHomogeneousMultiplicativity` | — |
| `A.AdjustedMultiplicativityStatement` | Closes by composition | `A.gradedOperator_multiplicative_of_homogeneous` applied to the homogeneous proof. |
| `A.AubertTheorem23Statement` | Proved: `A.aubertTheorem23` | None. The proof combines multiplicativity as above, the comparison from `A.gradedOperatorRingHom_eq_zelevinsky` with `A.gradedAdjustedOperator_unit` and the segment exchange, and Zelevinsky involutivity from the comparison and adjusted involutivity. It keeps the three parameters `hx`, `hl` and `hp` of the statement. Proof task `1850a779-27e5-4d34-a280-4b0c58e22a7a` (Task 5362). |
| `A.ZelevinskyInvolutivityStatement`, `A.AubertZelevinskyComparisonStatement` | Close by composition | They are the second and third conjuncts of Theorem 2.3: `(A.aubertTheorem23 F T hx hl hp).2.1` and `.2.2`. |
| `A.SegmentMonomialSpanningStatement`, `A.SegmentMonomialBasisStatement` | Close by composition | With `b := A.segmentMonomialBasis F T hx hl (A.segmentPolynomialComparison F T hx hl)`, the pair `⟨b.linearIndependent, b.span_eq⟩` proves the basis statement and `b.span_eq` proves the spanning statement (`Module.Basis.linearIndependent`, `Module.Basis.span_eq`; `A.segmentMonomialBasis_apply` identifies the basis vectors with `A.segmentMonomial` by `rfl`). No standalone theorem with either type is published yet. Theorem 2.3 does not need them: it uses the polynomial comparison directly. |

The segment socle and special quotient are exchanged by the unadjusted
operator with sign `(-1)^(n-k)` (`A.segmentSocleHead`), and without sign by the
adjusted operator (`A.adjustedSegmentExchange`).

The actual rational-point specialization is not yet stated. That would be the
comparison of `rationalAlternatingOperator` for the general linear group
scheme over a nonarchimedean local field with `A.alternatingOperator`. The
algebraic bridge `Langlands.Group.GL.AlgebraicPointTopology` is separate from
`GeneralLinearSpecialization` and is not automatically combined with it.

## Bottlenecks

Several open inputs each block many main targets.

1. **Renard VI.3.5 whole-category cuspidal splitting**
   (`4bee987a-093b-4054-bd65-7360168351d2`). It is the only remaining input of
   support decomposition, induction-Jacquet stability and Sharp support
   retention. Through induction-Jacquet stability it is also an input of
   Theorem 3.6. It alone also suffices for cuspidal Jacquet-factor extraction
   (`e6add7c5-44c5-45ea-afe9-7f48c98fb927`), support association, irreducible
   Jacquet detection, Jacquet vanishing, Jacquet cuspidality, induced cuspidal
   support, the rank-one Jacquet modules and the rank-one length-two target.
   Through the rank-one Jacquet modules it feeds Corollary 1.10(b).
2. **Special-vertex inputs or joint special-compact basis existence**
   (`8c39faa0-2a70-4fc4-a027-914987aba924`). Either one suffices, in place of
   VI.3.5, for the extraction targets listed in item 1 (all except
   decomposition, induction-Jacquet stability and Sharp support retention).
3. **Admissibility** (`aa8bb3a4-42d3-47db-9a48-98eb87ad9327`,
   `96949545-6354-4d63-93f7-0e5ca1e6fdfe`) **and generic same-Levi induction
   isomorphism** (`ba00e20e-ea55-4b97-89cc-2e9127ada887`). Together they give
   induced K0 Weyl conjugacy. That in turn feeds induction compatibility,
   involutivity, contragredient commutation, Corollary 1.10(b) and Sharp
   involution.
4. **Corrected graded vanishing** (`277860be-2aeb-4a85-8ccb-f1e2e5c573b9`).
   It is the only remaining input of the associated-Levi comparison, and an
   input of Theorem 3.6.
5. **Renard VII.1.3** (`004e00e1-5995-4dc1-884e-a5f512150d0c`). It is the only
   remaining input of rank-one self-association.
6. **Targets with no published reduction**: term transitivity and the top
   term (inputs to involutivity), support zero and exactness detection,
   Corollary 1.10(a), and Sharp finite length, class formula, irreducibility
   and cuspidal-series retention.

## Classification accounting

This program permits Langlands and Zelevinsky classification. An upstream
consumer decides separately whether a published proof satisfies its own route
constraints. A final audit must traverse both declaration types and proof
values and identify each classification declaration by exact name.

- `R.rationalCuspidalEigenvalue`: its reviewed route uses no Langlands
  classification, character independence or geometric lemma, under its
  visible premises.
- `R.rationalGeometricK0Expansion`: its paired
  [Markdown](../../Langlands/Representation/Aubert/General/RationalGeometricK0Expansion.md)
  states that the proof bodies of the theorem, its two assembly declarations,
  the modules of its chain and `GS.standardParabolicPointsStatement_proof`
  invoke no adjointness, cuspidal support, character independence or Langlands
  classification.
- `R.rationalJacquetCompatibility`: its paired
  [Markdown](../../Langlands/Representation/Aubert/General/RationalJacquetCompatibilityProof.md)
  reports a reachable-constant check. It uses the geometric lemma through
  `R.rationalGeometricK0Expansion` and no adjointness, Langlands
  classification or character independence. The only reachable declarations
  in cuspidal-support or classification modules are the generic helpers that
  Markdown names.
- `R.rationalMaximalCuspidalJacquetBudget`: its paired
  [Markdown](../../Langlands/Representation/Aubert/General/RationalMaximalCuspidalJacquetBudgetProof.md)
  states that the named proof bodies use no adjointness, cuspidal-support
  theorem, character independence or Langlands classification. It uses the
  geometric lemma through `R.rationalMaximalSourceGeometricFiltration`.
- Family 5: the published proofs of the segment exchange, adjusted
  involutivity and homogeneous multiplicativity each list, in their paired
  Markdown, the declarations they reach in `Langlands.Classification` and
  `Langlands.Representation.Classification.*` modules. Examples are
  `Langlands.Classification.segmentZelevinskyConstituentExistence`,
  `Langlands.Classification.normalizedInductionFiniteLength` and
  `Langlands.Classification.irreducibleProductEmbedding`. Theorem 2.3
  therefore depends transitively on GL classification results. The exact
  inventories are in
  [AdjustedSegmentExchangeProof](../../Langlands/Representation/Aubert/AdjustedSegmentExchangeProof.md),
  [AdjustedInvolutivityProof](../../Langlands/Representation/Aubert/AdjustedInvolutivityProof.md)
  and
  [AdjustedHomogeneousMultiplicativityProof](../../Langlands/Representation/Aubert/AdjustedHomogeneousMultiplicativityProof.md).
  The paired Markdown of `A.aubertTheorem23`,
  [AubertTheorem23Proof](../../Langlands/Representation/Aubert/AubertTheorem23Proof.md),
  lists the 437 declarations in 58 `Langlands.Representation.Classification`
  modules that its proof reaches. It makes no claim of classification
  independence.
- For every other main target, the transitive verdict remains undetermined
  until a complete proof exists. In particular, any route to induced-class
  Weyl invariance must be audited through its actual proof declarations.

## Remaining assembly

Families 1–4 remain open. In Family 5, every target listed in its table is
proved or closes by composition, but the rational-point GL specialization
described there is not stated. The remaining work is to close the
bottlenecks above, publish the composites through their owning tasks, state
and prove the rational-point GL specialization, and discharge the
per-instance premises of the rational targets. Every proof task listed here
belongs to its existing owner. Supporting helper publications do not close
their parent targets.

Worker 76 assembled the 3 November matrix, reusing Worker 164's structural
boundary, Worker 320's correction guidance, Workers 165/1186's rational
formal-target map, Workers 194/379's corrected-complex and support accounts,
and Workers 585/34's GL construction and dependency accounts. Worker 3640
(formerly Worker 18) refreshed the status four times on 10 November 2026, at
`e449cde`, `5263a53b`, `de0bad59` and `e7487341`, and again on 11 November
2026 at `642008d6`. These
attributions do not extend any original-source reading record or supply proof
acceptance.
