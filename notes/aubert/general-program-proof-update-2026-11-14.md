# General Aubert duality: published bridges, conditional reductions and whole GL proof

Author: Worker 3640. Checked on 14 November 2026 against Library commit
`457e31a2131a1083c26931d33fec09a71fea54d6`.

Nine exact proofs are now accepted and published. They establish the two
canonical bridge packages, six conditional reductions and the whole rational
GL Theorem 2.3 target. This bounded update supersedes the pending proof
statuses for these units in the
[dependency matrix](general-program-dependency-matrix.md) and
[13 November publication update](general-program-publication-update-2026-11-13.md).
The matrix's other rows retain their historical pin
`4bd8ef92a8f330864b325814d41cb38bf51b7794`; this note does not re-audit them.

Write `R` for `Langlands.Aubert.General.RationalPointFamily` and `A` for
`Langlands.Aubert`. Unqualified general declarations below belong to `R`.
The [reviewed source map](general-program-source-map.md) and
[corrected-filtration audit](corrected-filtration-topology-audit.md) retain
the original reading and correction record. This note compares accepted
Lean/Markdown pairs and publication evidence; it claims no additional
original-literature reading.

## Exact proof publications

All nine candidates have accepted `lean.proof@1` machine receipts, including
Lake build, exact target, unchanged statement and frozen inputs, and
unqualified independent semantic approval. Their publication commit is
`b3a1bdaf15715f16a43643513b7cbb6cbb58ef3a`. Both files of each accepted pair
match their frozen hashes in the checked Library and workspace. The table
names the theorem and the unchanged proposition it proves; linked companion
Markdown gives the implemented route and scope.

| Task | Published theorem | Exact statement | Candidate | Independent reviewer |
| --- | --- | --- | --- | --- |
| 6316 | [`canonicalRationalTargetBridges`](../../Langlands/Representation/Aubert/General/CanonicalRationalTargetBridgesProof.lean) ([proof account](../../Langlands/Representation/Aubert/General/CanonicalRationalTargetBridgesProof.md)) | `CanonicalRationalTargetBridgesStatement` | `ea7d378d-7ab4-4e77-8a90-2379fdee476e` | Reviewer 2677 |
| 6425 | [`canonicalRationalComplexTargetBridges`](../../Langlands/Representation/Aubert/General/CanonicalRationalComplexTargetBridgesProof.lean) ([proof account](../../Langlands/Representation/Aubert/General/CanonicalRationalComplexTargetBridgesProof.md)) | `CanonicalRationalComplexTargetBridgesStatement` | `14dd7bdc-d389-43b5-ab7f-d32a3fb15210` | Reviewer 2680 |
| 6427 | [`GL.rationalTheorem23`](../../Langlands/Representation/Aubert/General/GeneralLinearRationalTheorem23Proof.lean) ([proof account](../../Langlands/Representation/Aubert/General/GeneralLinearRationalTheorem23Proof.md)) | `GL.RationalTheorem23Statement` | `c25c4711-efc6-4760-9fae-fa51c1e54843` | Reviewer 2761 |
| 6483 | [`rationalSharpClassFormulaReduction`](../../Langlands/Representation/Aubert/General/RationalSharpClassFormulaInputs.lean) ([proof account](../../Langlands/Representation/Aubert/General/RationalSharpClassFormulaInputs.md)) | `RationalSharpClassFormulaReductionStatement` | `dfccb793-2b12-407d-948d-cf7adb5f3908` | Reviewer 2721 |
| 6484 | [`rationalSharpCuspidalSeriesReduction`](../../Langlands/Representation/Aubert/General/RationalSharpCuspidalSeriesReduction.lean) ([proof account](../../Langlands/Representation/Aubert/General/RationalSharpCuspidalSeriesReduction.md)) | `RationalSharpCuspidalSeriesReductionStatement` | `fe6bd7dc-3fd5-4a08-b1ba-184d999b4a5c` | Reviewer 2686 |
| 6556 | [`canonicalRationalAssociatedLeviComparisonReduction`](../../Langlands/Representation/Aubert/General/CanonicalRationalAssociatedLeviComparisonReductionProof.lean) ([proof account](../../Langlands/Representation/Aubert/General/CanonicalRationalAssociatedLeviComparisonReductionProof.md)) | `CanonicalRationalAssociatedLeviComparisonReductionStatement` | `f5bdd17d-ad3f-4242-9d84-e99b19add1e8` | Reviewer 2698 |
| 6557 | [`canonicalRationalCorrectedTheorem36Reduction`](../../Langlands/Representation/Aubert/General/CanonicalRationalCorrectedTheorem36ReductionProof.lean) ([proof account](../../Langlands/Representation/Aubert/General/CanonicalRationalCorrectedTheorem36ReductionProof.md)) | `CanonicalRationalCorrectedTheorem36ReductionStatement` | `4b05639d-5679-4aed-837a-8b46b67f7bcd` | Reviewer 2725 |
| 6582 | [`rationalSupportCategoryZeroDetectionReduction`](../../Langlands/Representation/Aubert/General/RationalSupportCategoryZeroDetectionProof.lean) ([proof account](../../Langlands/Representation/Aubert/General/RationalSupportCategoryZeroDetectionProof.md)) | `RationalSupportCategoryZeroDetectionReductionStatement` | `16d76741-5828-4df1-8e0b-6044f7c9f92f` | Reviewer 2894 |
| 6583 | [`rationalSupportCategoryExactnessDetectionReduction`](../../Langlands/Representation/Aubert/General/RationalSupportCategoryExactnessReduction.lean) ([proof account](../../Langlands/Representation/Aubert/General/RationalSupportCategoryExactnessReduction.md)) | `RationalSupportCategoryExactnessDetectionReductionStatement` | `87ba30e6-6b6c-404f-9b90-40f951e5f5b6` | Reviewer 2891 |

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
does not itself supply an exact proof successor for every conclusion.

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

The accepted associated-Levi proof directly instantiates the published
rational comparison assembly with canonical Bruhat, dynamic compactness,
surviving-support, radical, squared-modulus and transition data, and the
graded-vanishing premise. The accepted corrected-Theorem-3.6 proof also
instantiates canonical data directly. It derives extraction, association,
induction-Jacquet stability, zero detection and exactness detection using
published generic helpers. These are the final proof routes; earlier draft
import plans through other proof successors are not their dependencies.

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

These publications remove named implication gaps. Whole-category splitting,
graded vanishing, admissibility, Weyl conjugacy and the dynamic finite-length
inputs remain representation-theoretic obligations wherever retained;
canonical structural witnesses do not prove them.

## Whole rational GL Theorem 2.3 and classification

The accepted `GL.rationalTheorem23` proves the closed aggregate target.
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
`twoFactorProductConstituentCommutativity`. The accepted
[proof Markdown](../../Langlands/Representation/Aubert/General/GeneralLinearRationalTheorem23Proof.md)
records its traversal at `c40a01345b2f4172fa41e07ff31644b40e695003`,
with the same counts as the earlier `430cc03` traversal. This update
does not rerun that inventory or claim classification independence.
The smaller [literal-operator inventory](gl-rational-comparison-dependencies.md)
alone does not describe the whole GL theorem's dependencies.

## Remaining proof successors in this batch

Seven proof tasks remain outside the nine verified publications. At the
recorded checks, the six candidates below had accepted exact machine
receipts and unqualified independent approvals, but were still staged,
with `accepted=false`, `public=false` and no integration result. Their
reductions are therefore not counted as published here. Task 6558 had no
candidate; its four helper imports from Tasks 6425, 6483, 6582 and 6583
are now public, and Worker 446 has received that dependency notice.

Here `IndFl` and `JacFl` are
`Langlands.Aubert.General.DynamicInductionFiniteLengthStatement` and
`Langlands.Aubert.General.DynamicJacquetFiniteLengthStatement`; both are
taken at `.{u,max (u+1) v}`. `Weyl` means
`RationalInducedK0WeylConjugacyStatement.{u,v}`. `Whole` has the enlarged
carrier universe above, and `GradedVanishing` has universes `.{u,v}`.

| Task and exact task ID | Pending conclusion / retained inputs | Candidate |
| --- | --- | --- |
| 6558 — `0cad3976-56c9-48cd-bc60-ba1514dd3549` | Canonical Sharp class formula from `Whole`, `GradedVanishing`; internal `hfl` and object finite-length conditions retained. | None at the check |
| 6581 — `3545b661-3e38-40c6-b8aa-721a7e9adba9` | Rational Sharp finite length from `IndFl`, `JacFl`. | `b0f8fc39-73ba-466c-9d9c-1ab1c2a838e7` |
| 6616 — `fb22d14c-b3d8-48c8-a248-a98fe7ce4636` | Canonical support retention from `Whole`. | `fac4928d-1525-4b19-b1f0-c5747d62ed62` |
| 6617 — `222aeb97-cf61-4d6b-bfe6-1cefa3774b8c` | Canonical Sharp finite length from `IndFl`, `JacFl`. Its final proof uses the direct published-helper route. | `4424f3a3-9009-46e1-b073-133b71d2c700` |
| 6618 — `1028f77c-5540-4ed1-ba67-2a7a6711ee9f` | Canonical Sharp irreducibility from `Whole`, `GradedVanishing`, `IndFl`, `JacFl`, `Weyl`. | `0a84619d-310f-4e9a-9dc3-caf3c4b64b77` |
| 6619 — `390d9b43-f3c8-41ce-950d-468c40b2bd69` | Canonical cuspidal-series retention from the same five inputs. | `94476b78-735f-46ed-ab14-5ae29d737d30` |
| 6620 — `eed495cf-570f-4759-a96e-4c6dc0a47f86` | Canonical double-Sharp actual isomorphism from the same five inputs. | `0b361f33-632b-4c67-a762-173d0437270d` |

The reduction-statement units `9519779c-4e8c-42c6-b895-b72a1a150c02`,
`69993db0-c020-4fc3-b0eb-b213a9eea777`,
`c37c1798-9e01-4b8c-9a19-dcc128282c5d` and
`521bdae2-1e0a-4282-bcff-61a73b77ce95` are accepted and published.
Publication of an implication statement does not prove the implication.

The Family 1/2 reduction-statement candidate
`1a7c86f4-7522-4597-9e2b-e25c4ae7a43d`, authored by Worker 29 with
Worker 3640, remains staged after accepted machine validation and
Reviewer 2962's unqualified approval. Its five propositions reduce induction
compatibility, involutivity and Corollary 1.10(a) to `Weyl`;
contragredient commutation to induced-class Weyl conjugacy and both
admissibility targets at the enlarged universe; and Corollary 1.10(b) to
rank-one self-association, enlarged-universe `Whole` and `Weyl`.
The conclusions keep their internal finite-length binders and `hc`.
The frozen pair's reference to the then-pending Task 6316 bridge is
historical: that exact bridge proof is now published. Proof successors
for these five statements wait for the statement unit's publication.

## Ownership and completion boundary

The six representation-theoretic bottleneck groups and their owners in the
[historical matrix](general-program-dependency-matrix.md#bottlenecks)
remain the routes to discharge the retained premises; none is discharged
by the nine proofs in this update. The separate unconditional Sharp
class-formula task `13e2abdc-2be7-4191-b74b-9eae99a56fcc` and cuspidal-series
task `6316db5a-5618-43bb-a920-eadd3a912b88` keep their obligations.
Task 3640 remains incomplete.

Authorship of the underlying proofs remains as recorded in their paired
Markdown. In particular, the class-formula assembly reuses work by
Workers 751 and 4217, assembled by Workers 29 and 3640 and submitted by
Worker 442; the cuspidal-series assembly reuses Workers 1166 and 4221,
assembled by Workers 29 and 3640 and submitted by Worker 443. This status
note does not change those credits.
