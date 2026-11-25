# General Aubert duality: canonical identities and Sharp reduction publications

The data below were checked on 16 November 2026 against Library commit
`b4005ae3c4a406e2d1193548306b79d7ab745811`, and the fixed-Levi addendum
against Library commit `a62c80eafd15a933bf75e7a7ff8577972c2945ae`.

Fourteen further exact proofs are in the Library: seven Sharp reductions,
five reductions for canonical formal identities, and the canonical Jacquet
compatibility and cuspidal eigenvalue targets. The module of the five Family 1/2
reduction statements is also in the Library. This update completes the
[14 November update](general-program-proof-update-2026-11-14.md). It adds the
new canonical proof statuses to the
[dependency matrix](general-program-dependency-matrix.md). Other matrix rows
retain their historical pin `4bd8ef92a8f330864b325814d41cb38bf51b7794`.

Write `R` for `Langlands.Aubert.General.RationalPointFamily`; unqualified
Aubert declarations below belong to `R`. These proofs prove the exact named
propositions, including their hypotheses. They do not discharge the
representation-theoretic inputs retained by those propositions.

## The commits where the proofs entered the Library

Each of the fourteen proofs in the next three sections was checked with a
Lake build, against its exact target, with its statement and inputs
unchanged; both files of each Lean/Markdown pair were unchanged at the
checked commit. They first appeared in the Library at these commits:

- the rational and canonical Sharp finite-length reductions:
  `ba00e0970dd9ba6222ccc056ca2ee7f06bcc8181`;
- the canonical Sharp class-formula, support-retention, irreducibility,
  cuspidal-series and involution reductions:
  `af5d652c2f2ff5b35b4ce4dbbf7cbec8bbf3e99e`;
- the five canonical formal identity reductions:
  `2016a0d994180c702214a75514a08546aa930f07`;
- canonical Jacquet compatibility and the cuspidal eigenvalue:
  `497ef49830025d23824f6b2e2b1d5d60b594f51e`.

The tables name exact theorem types; an implication statement is not
counted as its proof.

## Sharp consequences

| Published theorem and proof account | Exact proposition |
| --- | --- |
| [`canonicalRationalSharpClassFormulaReduction`](../../Langlands/Representation/Aubert/General/CanonicalRationalSharpClassFormulaReductionProof.lean) ([account](../../Langlands/Representation/Aubert/General/CanonicalRationalSharpClassFormulaReductionProof.md)) | `CanonicalRationalSharpClassFormulaReductionStatement` |
| [`rationalSharpFiniteLengthReduction`](../../Langlands/Representation/Aubert/General/RationalSharpFiniteLengthProof.lean) ([account](../../Langlands/Representation/Aubert/General/RationalSharpFiniteLengthProof.md)) | `RationalSharpFiniteLengthReductionStatement` |
| [`canonicalRationalSharpSupportRetentionReduction`](../../Langlands/Representation/Aubert/General/CanonicalRationalSharpSupportRetentionReductionProof.lean) ([account](../../Langlands/Representation/Aubert/General/CanonicalRationalSharpSupportRetentionReductionProof.md)) | `CanonicalRationalSharpSupportRetentionReductionStatement` |
| [`canonicalRationalSharpFiniteLengthReduction`](../../Langlands/Representation/Aubert/General/CanonicalRationalSharpFiniteLengthReductionProof.lean) ([account](../../Langlands/Representation/Aubert/General/CanonicalRationalSharpFiniteLengthReductionProof.md)) | `CanonicalRationalSharpFiniteLengthReductionStatement` |
| [`canonicalRationalSharpIrreducibleReduction`](../../Langlands/Representation/Aubert/General/CanonicalRationalSharpIrreducibleReductionProof.lean) ([account](../../Langlands/Representation/Aubert/General/CanonicalRationalSharpIrreducibleReductionProof.md)) | `CanonicalRationalSharpIrreducibleReductionStatement` |
| [`canonicalRationalSharpCuspidalSeriesReduction`](../../Langlands/Representation/Aubert/General/CanonicalRationalSharpCuspidalSeriesReductionProof.lean) ([account](../../Langlands/Representation/Aubert/General/CanonicalRationalSharpCuspidalSeriesReductionProof.md)) | `CanonicalRationalSharpCuspidalSeriesReductionStatement` |
| [`canonicalRationalSharpInvolutionReduction`](../../Langlands/Representation/Aubert/General/CanonicalRationalSharpInvolutionReductionProof.lean) ([account](../../Langlands/Representation/Aubert/General/CanonicalRationalSharpInvolutionReductionProof.md)) | `CanonicalRationalSharpInvolutionReductionStatement` |

For the retained-input table, abbreviate the following unchanged whole
propositions:

- `Whole`: `Langlands.CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement.{u, max (u + 1) v}`.
- `GradedVanishing`: `RationalCorrectedGradedVanishingStatement.{u,v}`.
- `IndFl` and `JacFl`: `Langlands.Aubert.General.DynamicInductionFiniteLengthStatement`
  and `Langlands.Aubert.General.DynamicJacquetFiniteLengthStatement`, both
  at `.{u, max (u + 1) v}`.
- `Weyl`: `RationalInducedK0WeylConjugacyStatement.{u,v}`.

| Published consequence | Retained antecedents, in curried order |
| --- | --- |
| Canonical Sharp class formula | `Whole`, `GradedVanishing` |
| Rational and canonical Sharp finite length | `IndFl`, `JacFl` |
| Canonical Sharp support retention | `Whole` |
| Canonical Sharp irreducibility, cuspidal-series retention and double-Sharp isomorphism | `Whole`, `GradedVanishing`, `IndFl`, `JacFl`, `Weyl` |

These inputs and their order agree with
[the canonical complex reductions](../../Langlands/Representation/Aubert/General/CanonicalRationalComplexReductionStatements.lean),
[the detection/finite-length reductions](../../Langlands/Representation/Aubert/General/RationalDetectionFiniteLengthReductionStatements.lean)
and [the canonical Sharp reductions](../../Langlands/Representation/Aubert/General/CanonicalRationalSharpReductionStatements.lean).
The conclusion of the class-formula reduction still quantifies its termwise
`hfl : ∀ J, ParabolicFiniteLength …` and finite length of both `E` and `E#`.
It gives `D_G[E] = (-1)^|I| [E#]` in the actual exact finite-length
Grothendieck group, with nonsplit short exact sequence relations retained.
The separate finite-length reductions do not prove either dynamic input.

The rational finite-length proof reuses an existing assembly. The canonical
finite-length proof supplies the standard induction–Jacquet finite-length
premise directly from the dynamic hypotheses, then applies the published
finite-product and quotient helper. It does not depend on the rational
finite-length reduction through a bridge. Both finite-length conclusions
apply to every finite-length smooth `E`, without a support hypothesis.

Support retention covers every smooth member of `Alg({I})`, without adding
finite length. The class-formula and three irreducible-consequence proofs
assemble extraction, support association, induction–Jacquet stability,
exactness detection and Jacquet vanishing from published helpers. The latter
three also obtain induction compatibility and involutivity from `Weyl`.
Their final routes are recorded in the linked proof accounts. Cuspidal-series retention includes an actual associated Levi
and conjugation witness. Double-Sharp concludes an actual module isomorphism
for a member of the specified cuspidal series; it is not inferred from
equality of arbitrary K0 classes.

## Canonical formal identity reductions

The statement module
[`CanonicalRationalTheorem17ReductionStatements`](../../Langlands/Representation/Aubert/General/CanonicalRationalTheorem17ReductionStatements.lean)
([account](../../Langlands/Representation/Aubert/General/CanonicalRationalTheorem17ReductionStatements.md)),
first appeared in the Library at `ba00e0970dd9ba6222ccc056ca2ee7f06bcc8181`.
Its five implications have these exact proofs:

| Published theorem and proof account | Exact proposition |
| --- | --- |
| [`canonicalRationalInductionCompatibilityReduction`](../../Langlands/Representation/Aubert/General/CanonicalRationalInductionCompatibilityReductionProof.lean) ([account](../../Langlands/Representation/Aubert/General/CanonicalRationalInductionCompatibilityReductionProof.md)) | `CanonicalRationalInductionCompatibilityReductionStatement` |
| [`canonicalRationalInvolutivityReduction`](../../Langlands/Representation/Aubert/General/CanonicalRationalInvolutivityReductionProof.lean) ([account](../../Langlands/Representation/Aubert/General/CanonicalRationalInvolutivityReductionProof.md)) | `CanonicalRationalInvolutivityReductionStatement` |
| [`canonicalRationalCorollary110aReduction`](../../Langlands/Representation/Aubert/General/CanonicalRationalCorollary110aReductionProof.lean) ([account](../../Langlands/Representation/Aubert/General/CanonicalRationalCorollary110aReductionProof.md)) | `CanonicalRationalCorollary110aReductionStatement` |
| [`canonicalRationalContragredientCommutationReduction`](../../Langlands/Representation/Aubert/General/CanonicalRationalContragredientCommutationReductionProof.lean) ([account](../../Langlands/Representation/Aubert/General/CanonicalRationalContragredientCommutationReductionProof.md)) | `CanonicalRationalContragredientCommutationReductionStatement` |
| [`canonicalRationalCorollary110bReduction`](../../Langlands/Representation/Aubert/General/CanonicalRationalCorollary110bReductionProof.lean) ([account](../../Langlands/Representation/Aubert/General/CanonicalRationalCorollary110bReductionProof.md)) | `CanonicalRationalCorollary110bReductionStatement` |

| Canonical conclusion | Retained antecedents, in curried order |
| --- | --- |
| Induction compatibility, involutivity and Corollary 1.10(a) | `Weyl` |
| Contragredient commutation | `RationalInducedClassWeylConjugacyStatement.{u,v}`, `Langlands.Aubert.General.RationalPointsFiniteLengthAdmissibleStatement.{u,max (u+1) v}`, `Langlands.Aubert.General.DynamicLeviFiniteLengthAdmissibleStatement.{u,max (u+1) v}` |
| Corollary 1.10(b) | `RationalRankOneSelfAssociationStatement.{u,v}`, `Whole`, `Weyl` |

The induction reduction uses the published geometric K0 expansion and the
rational induction assembly, then the second canonical bridge. Involutivity
and Corollary 1.10(a) use their published rational reductions and the fourth
and sixth bridges. Contragredient commutation reorders its three inputs for
the rational assembly and applies the first bridge. Corollary 1.10(b)
derives extraction and rank-one Jacquet modules from `Whole`, applies the
rational rank-one assembly and then the seventh bridge. These are
compositions of published proofs, not proofs of the retained antecedents.

Every canonical operator conclusion keeps its internal global `hiFl` and
`hrFl` at `.{u,max (u+1) v}`. Contragredient commutation also keeps its
per-group `hc : ContragredientPreservesFiniteLength`. Corollary 1.10(a)
retains irreducible Levi-cuspidal input and irreducibility of its induction;
Corollary 1.10(b) retains the maximal-subset and reducible-induction
conditions and concludes an actual two-constituent short exact sequence
in either order, with both signed exchange equalities.

## Canonical Jacquet compatibility and cuspidal eigenvalue

| Published theorem and proof account | Exact proposition |
| --- | --- |
| [`canonicalRationalJacquetCompatibility`](../../Langlands/Representation/Aubert/General/CanonicalRationalJacquetCompatibilityProof.lean) ([account](../../Langlands/Representation/Aubert/General/CanonicalRationalJacquetCompatibilityProof.md)) | `CanonicalRationalJacquetCompatibilityStatement` |
| [`canonicalRationalCuspidalEigenvalue`](../../Langlands/Representation/Aubert/General/CanonicalRationalCuspidalEigenvalueProof.lean) ([account](../../Langlands/Representation/Aubert/General/CanonicalRationalCuspidalEigenvalueProof.md)) | `CanonicalRationalCuspidalEigenvalueStatement` |

These theorems add no premise outside their named propositions. Their
propositions still bind `hiFl` and `hrFl`; neither finite-length statement
is discharged. Each proof applies its published rational-to-canonical
bridge to the corresponding published rational theorem.

Jacquet compatibility preserves every `Fintype` on the actual relative Weyl
group, every standard subset `J`, and every normalizer lift `n` of the
specified longest representative. With `J'` the associated subset, its
identity is `r_J.comp D = transport.comp (D_L'.comp r_J')`, with actual
conjugation transport in the stated direction. The cuspidal eigenvalue
retains irreducibility and Jacquet vanishing at every proper standard subset;
it gives `(-1)^|S|` times the class. Empty simple-root systems are included.

## Canonical fixed-Levi comparison: publication addendum

The Library proves `CanonicalRationalFixedLeviComparisonStatement.{u,v}` by
[`canonicalRationalFixedLeviComparison`](../../Langlands/Representation/Aubert/General/CanonicalRationalFixedLeviComparisonProof.lean)
([account](../../Langlands/Representation/Aubert/General/CanonicalRationalFixedLeviComparisonProof.md)),
which first appeared at Library commit
`e4a9b4d0164a5e0a9828dcaec5fa1cb7837ff8c6`. It was checked with a Lake build
against its exact target, with the statement and inputs unchanged.

The proof composes `canonicalRationalFixedLeviComparison_of_rational` with
`rationalFixedLeviComparison`. It proves the natural isomorphism
`D̃_{L_I} ∘ r_I ≅ r_I` on the full smooth support category for every standard
subset `I`, as in the erratum, printed p.4690, immediately before (**).
Here `D̃_{L_I}` is the full-support terminal functor of the actual Levi and
`r_I` the actual normalized Jacquet functor. It adds no hypothesis and has no
dynamic finite-length premise. The canonical topology and structural values
are supplied by the published bridge.

This fixed-Levi result does not close corrected Theorem 3.6 or the
associated-Levi comparison. Their `Whole` and `GradedVanishing` obligations
remain as recorded below.

## Scope, dependencies and remaining work

The general targets keep arbitrary nonarchimedean local fields, connected
reductive groups, canonical `pointTopology`, independent universes `u,v` and
representation carriers in `max (u+1) v`. They have no added split,
quasisplit or characteristic-zero restriction. Relative Weyl quotients retain
the full centralizer denominator `N_G(T0)/Z_G(T0)` and
`N_{L_I}(T0)/Z_G(T0)`, including `L_empty = Z_G(T0)`.

The [source map](general-program-source-map.md) and
[corrected-filtration audit](corrected-filtration-topology-audit.md) retain
the original reading and correction record. This update makes no additional
original-literature reading claim. The complex still has its actual terminal
cokernel in degree `|S|-|I|`. Corrected Theorem 3.6 concerns every smooth
member of `Alg({I})`; its reduction retains `Whole` and `GradedVanishing`.
The associated-Levi comparison retains `GradedVanishing`. None of the
publications here removes those premises, the two-sided corrected support,
the length-order requirement or the surviving terminal homology. Proposition
3.2 is not used as an established result.

These proofs do not discharge the representation inputs or change the
[bottlenecks](general-program-dependency-matrix.md#bottlenecks). The
unconditional Sharp class formula and cuspidal-series statements keep their
separate obligations; the Library has only conditional proofs of them.
The former matrix row listing targets with no published reduction is
superseded for zero/exactness detection, Sharp finite length, class formula
and cuspidal-series retention by the 14 November update and this one.

No new transitive classification audit is claimed here. In particular,
retaining `Weyl` or another representation input in an implication is not
evidence that its eventual proof avoids classification. The distinction
between the arbitrary-witness aggregate `GL.rationalTheorem23` and the
supplied-witness `GL.rationalWholeGradedTheorem23Canonical`, and their
recorded classification dependencies, remain those of the
[14 November GL account](general-program-proof-update-2026-11-14.md#whole-rational-gl-theorem-23-and-classification).
Only the itemized external structural boundary in the
[Renard Chapter V ledger](../renard/chapter-v-structural-inputs.md) is permitted
for completion; these reductions do not turn representation inputs into
structural assumptions.

The finite-length proofs use an existing assembly and published generic
helpers. This note does not claim completion of a main family.
