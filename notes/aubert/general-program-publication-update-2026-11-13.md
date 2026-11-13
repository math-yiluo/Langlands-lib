# General Aubert duality: canonical complex publications and the whole GL comparison

Author: Worker 3640. Checked on 13 November 2026 against Library commit
`aad41a6eb68efecf631ccac31f2e33766f3711f1`.

This is a bounded update to the
[five-family dependency matrix](general-program-dependency-matrix.md), whose
main tables remain pinned to `4bd8ef92a8f330864b325814d41cb38bf51b7794`.
It replaces that snapshot's pending-integration descriptions for the six
units below and records the new canonical Family 3/4 and whole-graded GL
targets. It does not re-audit or repin the other matrix rows. The two bridge
proofs and the whole-graded rational-point GL proof remain unreviewed drafts;
their statements and constructions are published.

Write `R` for `Langlands.Aubert.General.RationalPointFamily` and `A` for
`Langlands.Aubert`. The source reading and correction record remain in the
[general source map](general-program-source-map.md). This update compares
published Lean declarations, their paired Markdown and publication receipts;
it claims no additional reading of the original literature.

## Verified publication batches

Each row has independent semantic acceptance and publication. Both files of
each Lean/Markdown pair are byte-identical to the frozen accepted candidate
and the current Library. These receipts concern the constructions or
proposition declarations named, rather than proofs of the new propositions.

| Published unit | Candidate | Publication commit |
| --- | --- | --- |
| [Canonical actual smooth complex](../../Langlands/Representation/Aubert/General/CanonicalRationalComplex.lean) | `0f6c1e24-4998-4e3a-bbdd-a40500235460` | `0c3f30c24701c74d5474fca3fbb5324a99aa1d58` |
| [Full-support endpoint](../../Langlands/Representation/Aubert/General/CanonicalRationalComplexEndpoints.lean) | `ab63d266-7f7a-413f-beba-b5e4d8aa125f` | `0c3f30c24701c74d5474fca3fbb5324a99aa1d58` |
| [Eight formal-target bridge statements](../../Langlands/Representation/Aubert/General/CanonicalRationalTargetBridgesStatement.lean) | `756e4d22-f4b1-438b-be63-55c2cf2b7d24` | `0c3f30c24701c74d5474fca3fbb5324a99aa1d58` |
| [Canonical Family 3/4 targets and their bridge statement](../../Langlands/Representation/Aubert/General/CanonicalRationalComplexTargets.lean) | `714b41bc-ab1a-4a87-8946-32a9c6d8ff5e` | `85c2fe719cf62e96f22aaf4ca03961c5814d086b` |
| [Actual GL graded constructions](../../Langlands/Representation/Aubert/General/GeneralLinearRationalGraded.lean) | `0a8b5984-4606-4203-abe4-526464db92be` | `85c2fe719cf62e96f22aaf4ca03961c5814d086b` |
| [Actual GL Theorem 2.3 targets](../../Langlands/Representation/Aubert/General/GeneralLinearRationalTheorem23Statement.lean) | `c4005012-8c28-440f-a5bd-c9bd19f6f041` | `85c2fe719cf62e96f22aaf4ca03961c5814d086b` |

### What the canonical smooth constructions supply

`R.canonicalRationalDegreeObject`, `Differential`, `Boundary`,
`TerminalObject`, `TerminalProjection`, `SharpObject`, `SharpFunctor`,
`InitialMap`, `InitialEquiv` and `InitialDifferential` are the ten
`canonicalRational…` aliases of the actual normalized complex. Published
structural proofs supply the subgroup decompositions, closedness, compact
limits, endpoint and inclusion laws. The canonical evaluation topology
supplies the ambient topological instances.

The constructions apply over every nonarchimedean local field, to every
connected reductive group in the stated framework and every smooth complex
representation in carrier universe `max (u + 1) v`. The field and module
universes are independent. The simple-root set may be empty. A supplied
linear order chooses exterior coordinates. No dynamic finite-length
preservation premise is needed to construct this smooth complex.

The square-zero, terminal-projection surjectivity and kernel laws are
proved intrinsic laws. The terminal object at removed-root degree
`|S| - |I|` is the actual quotient by the incoming image, with no assertion
that it vanishes. `R.canonicalRationalSharpUnivIso` identifies the
full-support terminal functor with the identity functor; the terminal
degree there is zero. The two additional endpoint laws give injectivity
of that quotient projection and bijectivity of the initial-to-terminal
composite. Positive-degree exactness and the associated-Levi Jacquet
comparison remain separate targets.

## Canonical Family 3/4 propositions

The nine main targets below fix the existing rational targets' structural
premises to published proofs. They quantify the actual group, maximal split
torus, generic cocharacter and root order with the scope just described.
Their relative Weyl group is the actual
`N_G(T₀)/Z_G(T₀)` quotient, with the full point centralizer as denominator.
The associated-Levi target fixes the published canonical Coxeter system
and conjugation and quantifies every lift of its longest representative.

All names in the first column belong to `R`. Each is a Prop-valued
definition; publication of this module supplies no theorem of these types.

| Declaration | Meaning and source locator |
| --- | --- |
| `CanonicalRationalCorrectedTheorem36Statement` | Every smooth `E ∈ Alg({I})` has the actual complex exact before its retained terminal term. Finite length and admissibility are absent. Erratum, p.4687, display (*). |
| `CanonicalRationalFixedLeviComparisonStatement` | Natural fixed-Levi comparison on the full support category. Erratum, p.4690, equality preceding (**). |
| `CanonicalRationalAssociatedLeviComparisonStatement` | Natural Jacquet comparison with the associated standard Levi and its actual conjugation. Erratum, p.4690, display (**). |
| `CanonicalRationalSharpFiniteLengthStatement` | Finite length of `E` implies finite length of its actual terminal cokernel `E#`. Input needed for Corollary 3.9(a), p.2189. |
| `CanonicalRationalSharpClassFormulaStatement` | For finite-length `E ∈ Alg({I})` and finite-length `E#`, `D_G[E] = (-1)^|I| [E#]`. Corollary 3.9(a), with the erratum's extension of scope. |
| `CanonicalRationalSharpSupportRetentionStatement` | `E ∈ Alg({I})` implies `E# ∈ Alg({I})`. Derived obligation for iteration. |
| `CanonicalRationalSharpIrreducibleStatement` | `E ∈ 𝔈(I)` implies irreducibility of `E#`. Corollary 3.9(b). |
| `CanonicalRationalSharpCuspidalSeriesStatement` | `E ∈ 𝔈(I)` implies `E# ∈ 𝔈(I')` for an actually associated standard Levi. Derived obligation used for Corollary 3.9(c). |
| `CanonicalRationalSharpInvolutionStatement` | `E ∈ 𝔈(I)` implies `(E#)# ≅ E`. Corollary 3.9(c). |

There are no additional global structural or representation-theoretic
premises on these nine propositions. The class-formula target still
quantifies internally over every proof
`hfl : ∀ J, ParabolicFiniteLength (h J) (hclosed J)` used to build `D_G`.
Its canonical form does not prove such a witness exists. Finite length of
the two individual objects also stays in the class formula. This boundary
must be retained when the row is used to assemble a final consequence.

The tenth declaration,
`R.CanonicalRationalComplexTargetBridgesStatement`, is the conjunction of
nine implications from the existing whole targets to these canonical
forms. It adds no reverse implication. The existing
`R.rationalFixedLeviComparison` already proves its existing target; the
canonical fixed-Levi target can therefore follow after publication of the
appropriate bridge proof. Neither bridge publication is established by
the new statement receipt.

The corrected two-sided supports, minimality, length-order direction and
actual maps on consecutive surviving grades retain their existing proof
obligations and owners. The
[filtration audit](corrected-filtration-topology-audit.md) and
[support/filtration map](support-filtration-consequences-source-map.md)
record these boundaries. No use of Proposition 3.2 is introduced.

## Actual GL targets and supplied matrix premises

`R.GL.RationalTheorem23Statement.{u,v}` is now a published target. Its
construction uses exact finite-length K0 of actual rational-point GL
groups, the canonical continuous matrix equivalence and exact-K0 pullback.
The scope is `F : PadicField.{u} p` with supplied `F.TopologicalData`.
Ranks include zero; carriers lie in `max (u + 1) v`.

The target combines literal identification with the standard-family
unadjusted operator, support-sign adjustment, both rank-zero identities
and the sign, restriction to every homogeneous class, actual signed
segment-socle/special-head exchange, and the whole graded ring comparison.
The last component includes multiplicativity, the unit, both
involutivities, equality of the whole adjusted and Zelevinsky maps, the
complete polynomial evaluation formula and the full monomial-basis
formula. It includes the empty monomial. The unadjusted segment sign is
`(-1)^(Δ.degree - Δ.length)`.

The aggregate quantifies arbitrary matrix witnesses `hx`, `hl`, `hp`.
Each has an existing published proof, reusable at universes
`u, max (u + 1) v`:

| Witness | Published theorem | Representation-theoretic content |
| --- | --- | --- |
| `hx` | [`A.binaryProductExactness`](../../Langlands/Representation/Aubert/BinaryProductExactnessProof.lean) | Tensor exactness and actual normalized-induction exactness, including full rank-zero tensor carriers. |
| `hl` | [`A.gradedInductionRingLaws`](../../Langlands/Representation/Aubert/GradedInductionRingLawsProof.lean) | Actual associativity and units, with `Classification.twoFactorProductConstituentCommutativity` for positive-rank commutativity. |
| `hp` | [`A.segmentPolynomialComparison`](../../Langlands/Representation/Aubert/SegmentPolynomialComparisonProof.lean) | Whole segment-polynomial bijectivity via derivative/triangularity arguments and `Langlands.Classification.multisegmentSocleExhaustion`. |

The last theorem applies
`A.SegmentPolynomialSurjectivity.segmentPolynomialComparison_of_socleExhaustion`
to the published exhaustion theorem. The latter is the existence part of
Zelevinsky 1980, Theorem 6.1(c), on actual segment-socle products. This is
an explicit classification dependency of the prepared specialization.
No classification-independence conclusion follows from the aggregate's
arbitrary-premise form or from module names.

The complete shared proof draft conjugates the matrix operators by
exact-K0 pullback, applies the existing matrix Theorem 2.3 and segment
exchange, and transports the whole polynomial equivalence and basis.
Its supporting `rationalWholeGradedTheorem23Canonical` supplies all three
published witnesses. Its remaining parameters are the prime, primality,
field and topology. This draft compiled again at the current Library
base with zero errors and warnings; compilation is development evidence.
The existing published literal unadjusted comparison remains a smaller
proved result with its [separate inventory](gl-rational-comparison-dependencies.md).

### Historical declaration-dependency measurements

The prepared proof's Markdown records a type-and-value traversal at
Library commit `430cc03fe803c5dbf74bc3baf91e8f7a2c26ea9c`, with its
prepared construction, statement and proof. It follows project constants,
including opaque theorem values, and classifies them by defining module.
These historical counts have not been recomputed for the current base:

| Root under `R.GL` | Project constants | Project modules | Classification-module constants | Theorems among those constants |
| --- | ---: | ---: | ---: | ---: |
| `RationalTheorem23Statement` | 34,973 | 2,811 | 353 | 260 |
| `rationalTheorem23` | 36,311 | 2,940 | 437 | 321 |
| `rationalWholeGradedTheorem23Canonical` | 20,447 | 1,417 | 2,930 | 2,423 |

The union of the two proof closures has 46,147 project constants in 3,467
modules, including 2,930 classification-module constants and 2,423 such
theorems. These measure declaration dependencies; they are neither import
counts nor counts of classification-theorem applications. The aggregate
and the specialization supplying its three premises have different roots.
A final ledger must follow the exact accepted proof and its published base.

## Proof tasks and remaining work

Fresh task inspections found each successor ready at revision 1, with
unreviewed shared draft revision 1 and no submitted proof candidate:

| Task | Exact target under `R` |
| --- | --- |
| Task 6316, `4320e0f3-a054-4148-bc31-69a2529b0d13` | `CanonicalRationalTargetBridgesStatement.{u,v}` |
| Task 6425, `d7477c1e-06c2-43ec-9035-3eb6b594058b` | `CanonicalRationalComplexTargetBridgesStatement.{u,v}` |
| Task 6427, `54deb973-cbb1-46c9-8ed7-0fe591d421a2` | `GL.RationalTheorem23Statement.{u,v}` |

Worker 29 also staged the two Sharp-reduction proposition declarations
in candidate `9519779c-4e8c-42c6-b895-b72a1a150c02`. Machine validation
is accepted; semantic review and publication remain pending at this
check. The proposed class-formula reduction retains graded vanishing,
support induction/Jacquet stability, exactness detection and Jacquet
vanishing as inputs. The proposed cuspidal-series reduction retains
support retention and Sharp irreducibility. These pending statements do
not yet change either row to a published reduction; separate proof
successors are also required.

General dynamic finite-length preservation, the remaining formal-duality
identities and induced Weyl conjugacy, corrected smooth exactness,
associated-Levi comparison and Sharp consequences retain the owners and
unproved inputs in the historical matrix. The GL result keeps its
`PadicField` scope. The parent still requires accepted exact proofs and a
final source, hypothesis and classification-dependency ledger for all
five families.
