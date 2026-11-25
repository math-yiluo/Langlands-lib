# General Aubert duality: published bridges, conditional reductions and whole GL proof

The data below were checked on 14 November 2026 against Library commit
`457e31a2131a1083c26931d33fec09a71fea54d6`; the proof statuses were checked
again against the Library as it is.

Nine exact proofs are in the Library. They establish the two canonical
bridge packages, six conditional reductions and the whole rational GL
Theorem 2.3 target. This bounded update supersedes the proof statuses for
these statements in the
[dependency matrix](general-program-dependency-matrix.md) and
[13 November publication update](general-program-publication-update-2026-11-13.md).
The matrix's other rows retain their historical pin
`4bd8ef92a8f330864b325814d41cb38bf51b7794`; this note does not re-audit them.

Write `R` for `Langlands.Aubert.General.RationalPointFamily` and `A` for
`Langlands.Aubert`. Unqualified general declarations below belong to `R`.
The [source map](general-program-source-map.md) and
[corrected-filtration audit](corrected-filtration-topology-audit.md) retain
the original reading and correction record. This note compares Lean/Markdown
pairs of the Library and the commits where they entered it; it claims no additional
original-literature reading.

## Exact proofs

All nine proofs were checked with a Lake build, against their exact
targets, with the statements and their inputs unchanged. They first
appeared in the Library at commit `b3a1bdaf15715f16a43643513b7cbb6cbb58ef3a`,
and both files of each pair were unchanged at the checked commit. The table
names the theorem and the unchanged proposition it proves; linked companion
Markdown gives the implemented route and scope.

| Published theorem | Exact statement |
| --- | --- |
| [`canonicalRationalTargetBridges`](../../Langlands/Representation/Aubert/General/CanonicalRationalTargetBridgesProof.lean) ([proof account](../../Langlands/Representation/Aubert/General/CanonicalRationalTargetBridgesProof.md)) | `CanonicalRationalTargetBridgesStatement` |
| [`canonicalRationalComplexTargetBridges`](../../Langlands/Representation/Aubert/General/CanonicalRationalComplexTargetBridgesProof.lean) ([proof account](../../Langlands/Representation/Aubert/General/CanonicalRationalComplexTargetBridgesProof.md)) | `CanonicalRationalComplexTargetBridgesStatement` |
| [`GL.rationalTheorem23`](../../Langlands/Representation/Aubert/General/GeneralLinearRationalTheorem23Proof.lean) ([proof account](../../Langlands/Representation/Aubert/General/GeneralLinearRationalTheorem23Proof.md)) | `GL.RationalTheorem23Statement` |
| [`rationalSharpClassFormulaReduction`](../../Langlands/Representation/Aubert/General/RationalSharpClassFormulaInputs.lean) ([proof account](../../Langlands/Representation/Aubert/General/RationalSharpClassFormulaInputs.md)) | `RationalSharpClassFormulaReductionStatement` |
| [`rationalSharpCuspidalSeriesReduction`](../../Langlands/Representation/Aubert/General/RationalSharpCuspidalSeriesReduction.lean) ([proof account](../../Langlands/Representation/Aubert/General/RationalSharpCuspidalSeriesReduction.md)) | `RationalSharpCuspidalSeriesReductionStatement` |
| [`canonicalRationalAssociatedLeviComparisonReduction`](../../Langlands/Representation/Aubert/General/CanonicalRationalAssociatedLeviComparisonReductionProof.lean) ([proof account](../../Langlands/Representation/Aubert/General/CanonicalRationalAssociatedLeviComparisonReductionProof.md)) | `CanonicalRationalAssociatedLeviComparisonReductionStatement` |
| [`canonicalRationalCorrectedTheorem36Reduction`](../../Langlands/Representation/Aubert/General/CanonicalRationalCorrectedTheorem36ReductionProof.lean) ([proof account](../../Langlands/Representation/Aubert/General/CanonicalRationalCorrectedTheorem36ReductionProof.md)) | `CanonicalRationalCorrectedTheorem36ReductionStatement` |
| [`rationalSupportCategoryZeroDetectionReduction`](../../Langlands/Representation/Aubert/General/RationalSupportCategoryZeroDetectionProof.lean) ([proof account](../../Langlands/Representation/Aubert/General/RationalSupportCategoryZeroDetectionProof.md)) | `RationalSupportCategoryZeroDetectionReductionStatement` |
| [`rationalSupportCategoryExactnessDetectionReduction`](../../Langlands/Representation/Aubert/General/RationalSupportCategoryExactnessReduction.lean) ([proof account](../../Langlands/Representation/Aubert/General/RationalSupportCategoryExactnessReduction.md)) | `RationalSupportCategoryExactnessDetectionReductionStatement` |

### What the bridges prove

The eight formal bridges take the existing whole rational targets to their
canonical counterparts: contragredient commutation, induction compatibility,
Jacquet compatibility, involutivity, the cuspidal eigenvalue, Corollary
1.10(a), Corollary 1.10(b) and induced K0 Weyl conjugacy. Each original target
remains a premise. Canonical structural witnesses supply the actual data;
the operator conclusions retain their internal dynamic induction and Jacquet
finite-length hypotheses, and contragredient commutation retains its `hc`.

The nine complex bridges similarly cover corrected Theorem 3.6, the fixed-
and associated-Levi comparisons, Sharp finite length, the class formula,
support retention, irreducibility, cuspidal-series retention and involution.
They discharge none of those input propositions. An existing fixed-Levi
proof can be composed with its bridge; publication of the bridge package
does not itself supply a proof of every conclusion.

### What the six reductions retain

For this paragraph, `Whole` abbreviates
`Langlands.CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement`,
`Extraction` abbreviates `RationalCuspidalJacquetFactorExtractionStatement`,
`GradedVanishing` abbreviates `RationalCorrectedGradedVanishingStatement`,
and the other short names omit the prefix `Rational` and suffix `Statement`.
All are unchanged whole propositions, rather than selected instances.

| Published reduction | Retained antecedents and conclusion |
| --- | --- |
| Class formula | `GradedVanishing` → `SupportCategoryInductionJacquet` → `SupportCategoryExactnessDetection` → `SupportCategoryJacquetVanishing` → `RationalSharpClassFormulaStatement`. The order is the statement's curried order. |
| Cuspidal series | `SharpSupportRetention` → `SharpIrreducible` → `RationalSharpCuspidalSeriesStatement`. |
| Canonical associated-Levi comparison | `GradedVanishing.{u,v}` → `CanonicalRationalAssociatedLeviComparisonStatement.{u,v}`. |
| Canonical corrected Theorem 3.6 | `Whole.{u,max (u+1) v}` → `GradedVanishing.{u,v}` → `CanonicalRationalCorrectedTheorem36Statement.{u,v}`. |
| Support-category zero detection | `Extraction.{u,v}` → `RationalSupportCategoryZeroDetectionStatement.{u,v}`. |
| Support-category exactness detection | `SupportCategoryZeroDetection.{u,v}` → `RationalSupportCategoryExactnessDetectionStatement.{u,v}`. |

The class formula keeps `hfl : ∀ J, ParabolicFiniteLength …` inside its
conclusion, together with finite length of the object `E` and its terminal
object `E#`. Its Euler identity is in the exact finite-length Grothendieck
group, retaining relations from nonsplit short exact sequences. The
cuspidal-series reduction retains an actual associated Levi and conjugated
cuspidal module; it does not infer module isomorphism from arbitrary K0
class equality.

The associated-Levi proof directly instantiates the published
rational comparison assembly with canonical Bruhat, dynamic compactness,
surviving-support, radical, squared-modulus and transition data, and the
graded-vanishing premise. The corrected-Theorem-3.6 proof also
instantiates canonical data directly. It derives extraction, association,
induction-Jacquet stability, zero detection and exactness detection using
published generic helpers. These are the final proof routes; earlier
plans through other proofs are not their dependencies.

Zero detection derives irreducible Jacquet detection internally from
extraction and supplies compact-limit data from the standard parabolic
data. Its generic argument takes an irreducible subquotient of an arbitrary
nonzero smooth module and uses Jacquet exactness. No additional finite-length
or admissibility premise is inserted. Exactness detection then uses full
Jacquet exactness, images and cokernels, and zero detection. Only the middle
object must lie in the specified support category; the two outer smooth
objects are arbitrary.

## General scope and corrected complex

The general declarations apply to actual rational-point groups of connected
reductive groups over arbitrary nonarchimedean local fields, with the
canonical `pointTopology`. The field universe `u` and module universe `v`
are independent, with representation carriers at `max (u+1) v`. There is
no split or quasisplit restriction, and empty simple-root systems are
allowed. The relative Weyl quotients use the full denominator:
`W = N_G(T0)/Z_G(T0)` and `W_I = N_{L_I}(T0)/Z_G(T0)`;
the empty-subset Levi is the centralizer.

Corrected Theorem 3.6 concerns arbitrary smooth `E` in `Alg({I})`, without
a finite-length hypothesis. The corrected two-sided support conditions,
length-minimal representatives and chosen length order, and actual maps
on surviving grades remain those of the published construction. Its
terminal cokernel at removed-root degree `|S|-|I|` is retained as homology;
the theorem does not make the terminal module vanish. The route uses the
corrected filtration and makes no use of the invalid Proposition 3.2.
The construction and endpoint laws themselves need neither dynamic
finite-length input.

These proofs remove named implication gaps. Whole-category splitting,
graded vanishing, admissibility, Weyl conjugacy and the dynamic finite-length
inputs remain representation-theoretic obligations wherever retained;
canonical structural witnesses do not prove them.

## Whole rational GL Theorem 2.3 and classification

`GL.rationalTheorem23` proves the closed aggregate target.
That target internally quantifies the prime and primality instance, the
field `PadicField.{u} p`, supplied `TopologicalData`, and arbitrary matrix
witnesses `hx`, `hl`, `hp`. The GL scope remains `PadicField`; it does not
extend the general local-field finite-length results.

The target includes literal identification of the unadjusted canonical
operator, its support-dependent sign adjustment including
`(-1)^(N-B.length)`, and the required rank-zero identities. It treats every
homogeneous class, actual strong segment socles and special heads with sign
`(-1)^(Delta.degree-Delta.length)`, and the entire graded ring: multiplication,
unit, both involutions, equality of whole maps, the full polynomial
comparison and the full monomial basis including the empty monomial.
The rational-point exact K0 constructions are pulled back along the
continuous GL point/matrix equivalence.

The same published module also proves the supporting
`GL.rationalWholeGradedTheorem23Canonical`. It supplies the matrix witnesses
using `binaryProductExactness`, `gradedInductionRingLaws` and
`segmentPolynomialComparison` at carrier universe `max (u+1) v`, leaving
only the prime, primality, field and topology parameters. The polynomial
comparison applies
`A.SegmentPolynomialSurjectivity.segmentPolynomialComparison_of_socleExhaustion`
to `Langlands.Classification.multisegmentSocleExhaustion` (Zelevinsky 6.1(c)).
The ring laws use
`Langlands.Classification.twoFactorProductConstituentCommutativity`.
These are retained classification dependencies.

The aggregate proof with arbitrary `hx`, `hl`, `hp` and the supporting
supplied-witness theorem have distinct dependency closures. The aggregate
does not reach `multisegmentSocleExhaustion`, `binaryProductExactness`,
`gradedInductionRingLaws` or `segmentPolynomialComparison` through supplying
those witnesses; it still uses `aubertTheorem23` and `segmentSocleHead`.
Both proof closures and the target reach
`twoFactorProductConstituentCommutativity`. The
[proof Markdown](../../Langlands/Representation/Aubert/General/GeneralLinearRationalTheorem23Proof.md)
records its traversal at `c40a01345b2f4172fa41e07ff31644b40e695003`,
with the same counts as the earlier `430cc03` traversal. This update
does not rerun that inventory or claim classification independence.
The smaller [literal-operator inventory](gl-rational-comparison-dependencies.md)
alone does not describe the whole GL theorem's dependencies.

## The remaining reductions of this batch

Here `IndFl` and `JacFl` are
`Langlands.Aubert.General.DynamicInductionFiniteLengthStatement` and
`Langlands.Aubert.General.DynamicJacquetFiniteLengthStatement`; both are
taken at `.{u,max (u+1) v}`. `Weyl` means
`RationalInducedK0WeylConjugacyStatement.{u,v}`. `Whole` has the enlarged
carrier universe above, and `GradedVanishing` has universes `.{u,v}`.
Seven further reductions were prepared after the nine proofs above; the
Library proves all seven.

| Conclusion / retained inputs | Proof in the Library |
| --- | --- |
| Canonical Sharp class formula from `Whole`, `GradedVanishing`; internal `hfl` and object finite-length conditions retained. | `canonicalRationalSharpClassFormulaReduction` |
| Rational Sharp finite length from `IndFl`, `JacFl`. | `rationalSharpFiniteLengthReduction` |
| Canonical support retention from `Whole`. | `canonicalRationalSharpSupportRetentionReduction` |
| Canonical Sharp finite length from `IndFl`, `JacFl`, by the direct route through the existing helpers. | `canonicalRationalSharpFiniteLengthReduction` |
| Canonical Sharp irreducibility from `Whole`, `GradedVanishing`, `IndFl`, `JacFl`, `Weyl`. | `canonicalRationalSharpIrreducibleReduction` |
| Canonical cuspidal-series retention from the same five inputs. | `canonicalRationalSharpCuspidalSeriesReduction` |
| Canonical double-Sharp actual isomorphism from the same five inputs. | `canonicalRationalSharpInvolutionReduction` |

An implication statement in the Library is not its proof; the proofs are
named in the table.

The Family 1/2 reduction statements are five propositions. They reduce
induction compatibility, involutivity and Corollary 1.10(a) to `Weyl`;
contragredient commutation to induced-class Weyl conjugacy and both
admissibility targets at the enlarged universe; and Corollary 1.10(b) to
rank-one self-association, enlarged-universe `Whole` and `Weyl`.
The conclusions keep their internal finite-length binders and `hc`. The
Library proves all five (`canonicalRationalInductionCompatibilityReduction`,
`canonicalRationalInvolutivityReduction`, `canonicalRationalCorollary110aReduction`,
`canonicalRationalContragredientCommutationReduction`,
`canonicalRationalCorollary110bReduction`).

## Completion boundary

The six representation-theoretic bottleneck groups of the
[dependency matrix](general-program-dependency-matrix.md#bottlenecks)
remain the routes to discharge the retained premises; none is discharged
by the proofs in this update. The unconditional Sharp class formula
(`RationalSharpClassFormulaStatement`) and cuspidal-series statement
(`RationalSharpCuspidalSeriesStatement`) keep their obligations; the Library
has only conditional proofs of them (`rationalSharpClassFormula_of_inputs`,
`rationalSharpCuspidalSeries_of_supportRetention_of_irreducible`).
