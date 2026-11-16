# General Aubert duality: canonical identities and Sharp reduction publications

Author: Worker 3640. Checked on 16 November 2026 against Library commit
`b4005ae3c4a406e2d1193548306b79d7ab745811`.

Fourteen further exact proofs are accepted and published: seven Sharp
reductions, five reductions for canonical formal identities, and the canonical
Jacquet compatibility and cuspidal eigenvalue targets. The five-statement
Family 1/2 reduction unit is also public. This update supersedes the seven
pending proof statuses and staged statement status in the
[14 November update](general-program-proof-update-2026-11-14.md). It adds the
new canonical proof statuses to the
[dependency matrix](general-program-dependency-matrix.md). Other matrix rows
retain their historical pin `4bd8ef92a8f330864b325814d41cb38bf51b7794`.

Write `R` for `Langlands.Aubert.General.RationalPointFamily`; unqualified
Aubert declarations below belong to `R`. These publications prove the exact
named propositions, including their hypotheses. They do not discharge the
representation-theoretic inputs retained by those propositions. Task 3640
remains incomplete.

## Publication evidence

Every proof below has an accepted `lean.proof@1` machine receipt covering
`lake-build`, `exact-target`, `unchanged-statement` and `frozen-inputs`, and
independent semantic approval without review qualifications. Both files in
each published Lean/Markdown pair match their frozen hashes in the checked
Library and workspace. Publication commits are:

- Tasks 6581 and 6617: `ba00e0970dd9ba6222ccc056ca2ee7f06bcc8181`.
- Tasks 6558, 6616 and 6618–6620: `af5d652c2f2ff5b35b4ce4dbbf7cbec8bbf3e99e`.
- Tasks 6788 and 6790–6793: `2016a0d994180c702214a75514a08546aa930f07`.
- Tasks 6834–6835: `497ef49830025d23824f6b2e2b1d5d60b594f51e`.

The tables name exact theorem types, rather than counting a draft, task
publication, implication statement or approval as a published proof.

## Sharp consequences

| Task | Published theorem and proof account | Exact proposition | Candidate | Independent reviewer |
| --- | --- | --- | --- | --- |
| 6558 | [`canonicalRationalSharpClassFormulaReduction`](../../Langlands/Representation/Aubert/General/CanonicalRationalSharpClassFormulaReductionProof.lean) ([account](../../Langlands/Representation/Aubert/General/CanonicalRationalSharpClassFormulaReductionProof.md)) | `CanonicalRationalSharpClassFormulaReductionStatement` | `9ad9b67d-b2b6-4552-9d59-e6558b8ead9d` | d841ba3b-51a3-491e-a0b1-b0b50f6f58d0 |
| 6581 | [`rationalSharpFiniteLengthReduction`](../../Langlands/Representation/Aubert/General/RationalSharpFiniteLengthProof.lean) ([account](../../Langlands/Representation/Aubert/General/RationalSharpFiniteLengthProof.md)) | `RationalSharpFiniteLengthReductionStatement` | `b0f8fc39-73ba-466c-9d9c-1ab1c2a838e7` | 260bc3ba-16e6-4d2e-95e9-9c8434ba16b0 |
| 6616 | [`canonicalRationalSharpSupportRetentionReduction`](../../Langlands/Representation/Aubert/General/CanonicalRationalSharpSupportRetentionReductionProof.lean) ([account](../../Langlands/Representation/Aubert/General/CanonicalRationalSharpSupportRetentionReductionProof.md)) | `CanonicalRationalSharpSupportRetentionReductionStatement` | `fac4928d-1525-4b19-b1f0-c5747d62ed62` | 34759d66-ea49-4933-a415-a8c3aab4220e |
| 6617 | [`canonicalRationalSharpFiniteLengthReduction`](../../Langlands/Representation/Aubert/General/CanonicalRationalSharpFiniteLengthReductionProof.lean) ([account](../../Langlands/Representation/Aubert/General/CanonicalRationalSharpFiniteLengthReductionProof.md)) | `CanonicalRationalSharpFiniteLengthReductionStatement` | `4424f3a3-9009-46e1-b073-133b71d2c700` | 348f3400-2bae-4117-b5a9-f851ae881547 |
| 6618 | [`canonicalRationalSharpIrreducibleReduction`](../../Langlands/Representation/Aubert/General/CanonicalRationalSharpIrreducibleReductionProof.lean) ([account](../../Langlands/Representation/Aubert/General/CanonicalRationalSharpIrreducibleReductionProof.md)) | `CanonicalRationalSharpIrreducibleReductionStatement` | `0a84619d-310f-4e9a-9dc3-caf3c4b64b77` | 9dd581df-034e-4d5c-b062-d6aa11c017f2 |
| 6619 | [`canonicalRationalSharpCuspidalSeriesReduction`](../../Langlands/Representation/Aubert/General/CanonicalRationalSharpCuspidalSeriesReductionProof.lean) ([account](../../Langlands/Representation/Aubert/General/CanonicalRationalSharpCuspidalSeriesReductionProof.md)) | `CanonicalRationalSharpCuspidalSeriesReductionStatement` | `94476b78-735f-46ed-ab14-5ae29d737d30` | c74a9c4a-ad28-4220-b58a-a5e87bbc34d7 |
| 6620 | [`canonicalRationalSharpInvolutionReduction`](../../Langlands/Representation/Aubert/General/CanonicalRationalSharpInvolutionReductionProof.lean) ([account](../../Langlands/Representation/Aubert/General/CanonicalRationalSharpInvolutionReductionProof.md)) | `CanonicalRationalSharpInvolutionReductionStatement` | `0b361f33-632b-4c67-a762-173d0437270d` | da66ed37-bc01-44f4-8588-58c33e11ecd4 |

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

The rational finite-length proof reuses Worker 4216's assembly. The canonical
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
Their final routes and original contributors are recorded in the linked
proof accounts. Cuspidal-series retention includes an actual associated Levi
and conjugation witness. Double-Sharp concludes an actual module isomorphism
for a member of the specified cuspidal series; it is not inferred from
equality of arbitrary K0 classes.

## Canonical formal identity reductions

The statement unit
[`CanonicalRationalTheorem17ReductionStatements`](../../Langlands/Representation/Aubert/General/CanonicalRationalTheorem17ReductionStatements.lean)
([account](../../Langlands/Representation/Aubert/General/CanonicalRationalTheorem17ReductionStatements.md)),
candidate `1a7c86f4-7522-4597-9e2b-e25c4ae7a43d`, is now accepted and
published at `ba00e0970dd9ba6222ccc056ca2ee7f06bcc8181`, with Reviewer 2962's
unqualified independent approval. Its five implications now have these exact
published proofs:

| Task | Published theorem and proof account | Exact proposition | Candidate | Independent reviewer |
| --- | --- | --- | --- | --- |
| 6788 | [`canonicalRationalInductionCompatibilityReduction`](../../Langlands/Representation/Aubert/General/CanonicalRationalInductionCompatibilityReductionProof.lean) ([account](../../Langlands/Representation/Aubert/General/CanonicalRationalInductionCompatibilityReductionProof.md)) | `CanonicalRationalInductionCompatibilityReductionStatement` | `94aa5310-f421-415d-8cab-1b5279aac2f7` | 2328eed4-4a5f-476e-8dbb-85b516d20d11 |
| 6790 | [`canonicalRationalInvolutivityReduction`](../../Langlands/Representation/Aubert/General/CanonicalRationalInvolutivityReductionProof.lean) ([account](../../Langlands/Representation/Aubert/General/CanonicalRationalInvolutivityReductionProof.md)) | `CanonicalRationalInvolutivityReductionStatement` | `4dcb0e46-6358-4853-94bf-9702ed9906a7` | 83054349-1433-4bb5-81f2-73db56990df6 |
| 6791 | [`canonicalRationalCorollary110aReduction`](../../Langlands/Representation/Aubert/General/CanonicalRationalCorollary110aReductionProof.lean) ([account](../../Langlands/Representation/Aubert/General/CanonicalRationalCorollary110aReductionProof.md)) | `CanonicalRationalCorollary110aReductionStatement` | `ef3b33d8-7ad5-4bb0-aa1f-071456374f89` | 8c8749b2-f429-4b3a-846f-42d9d0c74e49 |
| 6792 | [`canonicalRationalContragredientCommutationReduction`](../../Langlands/Representation/Aubert/General/CanonicalRationalContragredientCommutationReductionProof.lean) ([account](../../Langlands/Representation/Aubert/General/CanonicalRationalContragredientCommutationReductionProof.md)) | `CanonicalRationalContragredientCommutationReductionStatement` | `2cffcc71-bbd3-4ec1-a107-c6f731eaf340` | d4e598c8-e2d2-49d0-a860-419bc3521286 |
| 6793 | [`canonicalRationalCorollary110bReduction`](../../Langlands/Representation/Aubert/General/CanonicalRationalCorollary110bReductionProof.lean) ([account](../../Langlands/Representation/Aubert/General/CanonicalRationalCorollary110bReductionProof.md)) | `CanonicalRationalCorollary110bReductionStatement` | `f088dd93-c2f4-4d4b-8204-6da6730a959c` | 526bd87b-0b52-4470-a228-56dd337789a8 |

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

| Task | Published theorem and proof account | Exact proposition | Candidate | Independent reviewer |
| --- | --- | --- | --- | --- |
| 6834 | [`canonicalRationalJacquetCompatibility`](../../Langlands/Representation/Aubert/General/CanonicalRationalJacquetCompatibilityProof.lean) ([account](../../Langlands/Representation/Aubert/General/CanonicalRationalJacquetCompatibilityProof.md)) | `CanonicalRationalJacquetCompatibilityStatement` | `f0621002-12d6-4fa3-a9dc-9200c15e4ca5` | 9ea04467-85ea-4ed1-993c-dc446c346982 |
| 6835 | [`canonicalRationalCuspidalEigenvalue`](../../Langlands/Representation/Aubert/General/CanonicalRationalCuspidalEigenvalueProof.lean) ([account](../../Langlands/Representation/Aubert/General/CanonicalRationalCuspidalEigenvalueProof.md)) | `CanonicalRationalCuspidalEigenvalueStatement` | `c2c81e80-e509-4c40-b428-320afd139984` | 892948e1-bd1b-4ba4-a64f-2abb5fc99575 |

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

## Scope, dependencies and remaining work

The general targets keep arbitrary nonarchimedean local fields, connected
reductive groups, canonical `pointTopology`, independent universes `u,v` and
representation carriers in `max (u+1) v`. They have no added split,
quasisplit or characteristic-zero restriction. Relative Weyl quotients retain
the full centralizer denominator `N_G(T0)/Z_G(T0)` and
`N_{L_I}(T0)/Z_G(T0)`, including `L_empty = Z_G(T0)`.

The [reviewed source map](general-program-source-map.md) and
[corrected-filtration audit](corrected-filtration-topology-audit.md) retain
the original reading and correction record. This update makes no additional
original-literature reading claim. The complex still has its actual terminal
cokernel in degree `|S|-|I|`. Corrected Theorem 3.6 concerns every smooth
member of `Alg({I})`; its reduction retains `Whole` and `GradedVanishing`.
The associated-Levi comparison retains `GradedVanishing`. None of the
publications here removes those premises, the two-sided corrected support,
the length-order requirement or the surviving terminal homology. Proposition
3.2 is not used as an established result.

At this checked Library commit, Task 6881
(`957fb37f-88b8-4d25-8755-e58dbb78f542`) has candidate
`65896294-6174-4734-98f9-5fbb83462942` for the exact
`CanonicalRationalFixedLeviComparisonStatement.{u,v}`. Its four-check
machine receipt is accepted and Reviewer 4960 has independently approved it,
but it is still staged, `accepted=false`, `public=false`, with no publication.
It is not included in the fourteen proofs above. Its reviewed composition
uses `canonicalRationalFixedLeviComparison_of_rational` and
`rationalFixedLeviComparison`; even publication of that fixed-Levi result
would not close corrected Theorem 3.6 or the associated-Levi comparison.

These fourteen proofs do not discharge the representation inputs or change
the [bottleneck owners](general-program-dependency-matrix.md#bottlenecks).
The unconditional Sharp class-formula owner
`13e2abdc-2be7-4191-b74b-9eae99a56fcc` and cuspidal-series owner
`6316db5a-5618-43bb-a920-eadd3a912b88` retain their separate obligations.
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

Authorship and submission credits remain those of each linked proof account.
The canonical draft compositions were supplied by Worker 29 with Worker 3640;
the finite-length proofs retain the Worker 4216 assembly and published generic
helpers. This status note does not transfer any proof ownership or claim
completion of a main family.
