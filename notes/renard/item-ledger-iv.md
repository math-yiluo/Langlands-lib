# Renard 2026, Chapter IV: item-by-item coverage ledger

Worker 1222, executor of the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`, revision 1. This note is the Chapter IV part of
the item ledger that the task contract requires, in the format of the published
[Chapter V](item-ledger-v.md), [Chapter VI](item-ledger-vi.md) and
[Chapter VII](item-ledger-vii.md) ledgers (status codes as there). It lists every headed
item of Chapter IV and the unheaded assertions found, with printed / PDF pages
(PDF = printed + 6), Lean declarations and proof status. The original survey used Library
`9951a27f5fd8ebbdc4bbe68eb6be65b1d0c2eb4a`, with the later IV.1.4 Remark 1 and IV.2.2
Proposition statements at `24a49431a1a304ab4190fc6ef1f7e7d21c2d41be`. On 14 November 2026,
the six formerly statement-only rows were updated against published proofs in Library
`e13a307a22881999a6db8ebc753d4d0b6dd359e5`; the evidence, hypotheses and implemented routes
appear below. Other row statuses retain the original survey date and scope.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. Chapter IV is printed
pp.87–102 / PDF pp.93–108.

Worker 1222 read each item in the source and the docstring and Markdown of each matched
declaration. The original proof-status scan sought theorems whose type is exactly the
statement. The six updates additionally check the published proof files and, for the five
records available in this instance, their acceptance and publication evidence. Unless
another namespace is written, statements are in
`Langlands.Renard.CompactRepresentation` (abbreviated `CR`).

## IV.1 Compact representations

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| IV.1.1 Theorem (i)–(iv): representations of a compact t.d. group | 88 / 94 | `CR.CompactGroupSmoothRepresentationStatement` | P: `compactGroupSmoothRepresentation` |
| IV.1.1 Corollary: `M(K)` semisimple, canonical isotypic decomposition `V = ⊕ V(σ)` | 88 / 94 | `CR.CompactGroupIsotypicDecompositionStatement` | P: `compactGroupIsotypicDecomposition`. That `V(σ)` is a sum of copies of `σ` follows from Theorem (iii) |
| IV.1.1 multiplicity `m(σ) = dim V(σ)/dim V_σ` | 89 / 95 | `CR.CompactGroupMultiplicityStatement` | P: `compactGroupMultiplicity` |
| IV.1.2 Proposition: admissibility criterion | 89 / 95 | `CR.AdmissibleFiniteMultiplicityStatement` | P: `admissibleFiniteMultiplicity` |
| IV.1.3 Definition: compact representations | 89 / 95 | `Langlands.HasCompactSmoothDualCoefficients` (coefficient form, equivalent by the Theorem below) | D |
| IV.1.3 subquotients of compact representations are compact | 89 / 95 | `HasCompactSmoothDualCoefficients.of_injective`, `.of_surjective` | P |
| IV.1.3 Theorem: compact iff all coefficients have compact support | 89 / 95 | `CR.CompactRepresentationCoefficientCriterionStatement` | P: `compactRepresentationCoefficientCriterion` |
| IV.1.3 Proposition: compact of finite type implies admissible | 90 / 96 | `CR.CompactFiniteTypeAdmissibleStatement` | P: `compactFiniteTypeAdmissible` |
| IV.1.3 Lemma: for `G` countable at infinity, a nonzero compact representation forces a compact centre | 90 / 96 | `CR.CompactRepresentationCompactCenterStatement` (hypotheses `[SigmaCompactSpace G]` and `Nontrivial π`) | P: `compactRepresentationCompactCenter`. The printed Lemma omits "nonzero"; see clarification C1 |
| IV.1.4 Theorem: `V = V(τ) ⊕ V(τ)^⊥` | 90 / 96 | `CR.CompactIsotypicComplementStatement` | P: `compactIsotypicComplement` |
| IV.1.4 (IV.1.4.1) `W ⊗ W̃ ≃ End(W)_0` for admissible `W` | 91 / 97 | [SmoothEndomorphismTensorProof](../../Langlands/Representation/CompactCoefficient/SmoothEndomorphismTensorProof.md) | St: step of the IV.1.4 Proposition, proved there |
| IV.1.4 Proposition (i)–(ii) and the formal degree `d(τ)` | 91–92 / 97–98 | `CR.CompactCoefficientFormalDegreeStatement` | P: `compactCoefficientFormalDegree` |
| IV.1.4 Remark 1: `d(τ)` depends on the Haar measure, precisely `d_{cμ}(τ) = d_μ(τ)/c` | 92 / 98 | `CR.CompactFormalDegreeHaarScalingStatement`: `κ` satisfies the identity (ii) for `μ` exactly when `cκ` satisfies it for `cμ`, for every smooth `τ`. The displayed degree formula follows by taking inverses | P: [`compactFormalDegreeHaarScaling`](../../Langlands/Representation/CompactCoefficient/CompactFormalDegreeHaarScalingProof.md) |
| IV.1.4 Remark 3: forward reference to IV.3.3 | 92 / 98 | — | X |
| IV.1.4 Remark 2: for compact `G` with the Haar measure normalized by `∫_G dμ_G = 1`, the formal degree of an irreducible smooth representation is its dimension | 92 / 98 | `CR.CompactGroupFormalDegreeStatement` (hypothesis `μ Set.univ = 1`) | P: `compactGroupFormalDegree`. Without the normalization the formal degree is `dim τ / μ(G)` (Remark 1 row) |
| IV.1.5 Theorem (i)–(iii): idempotents `e_{K,τ}` | 92 / 98 | `CR.CompactProjectionDistributionStatement` | P: `compactProjectionDistribution` |
| IV.1.5 Proposition (i)–(ii): `π(e_τ)` is a `G`-equivariant projector, natural in `V` | 93 / 99 | `Langlands.CompactCoefficientProjectorStatement` (Bernstein–Zelevinsky form: a natural equivariant idempotent family with range the isotypic part and kernel the annihilator, which is `π(e_τ)`) | C: proved (`compactCoefficientProjector`) |
| IV.1.5 Proposition (iii) and Remark 1 | 93–94 / 99–100 | `CR.CompactIsotypicComplementStatement` | P |
| IV.1.5 exactness of `V ↦ π(e_τ)·V` (IV.1.5.1) | 93 / 99 | — | St: step of (iii), covered by its proof |
| IV.1.5 Remark 2: `π(e_τ) π(e_τ′) = 0` for `τ ≇ τ′`; Remark 3: `e_τ` in the centre of `M(G)` | 94 / 100 | `Langlands.CompactCoefficientProjectorStatement` (orthogonality and naturality are conclusions) | C: proved |
| IV.1.6 Corollary: compact representations are semisimple | 94 / 100 | `CR.CompactPartSemisimpleStatement` (in `CR.CompactBlockDecompositionStatements`) | P: `compactBlockDecomposition` |
| IV.1.6 Notations `M(G)_τ`, `[M(G) \ τ]`, `M(G)_c`, `M(G)_nc`; `M(G)_c` semisimple with projective-injective simples | 94 / 100 | `CR.compactPart`, `CR.isotypicPart`, `CR.avoidingPart`; `CR.CompactPartSemisimpleStatement` | D; P |
| IV.1.6 Proposition: irreducible compact `τ` is projective and injective in `M(G)` | 94 / 100 | `CR.CompactProjectiveInjectiveStatement` | P |
| IV.1.7 decompositions `M(G) = M(G)_τ × [M(G) \ τ]`, finite and full products | 95 / 101 | `CR.IsotypicSplittingStatement` and the other conjuncts of `CR.CompactBlockDecompositionStatements` | P |
| IV.1.7 Proposition: `M(G) = M(G)_c × M(G)_nc` iff (KF) | 95 / 101 | `CR.CompactSplittingCriterionStatement` | P: `compactSplittingCriterion` |

## IV.2 Unitary representations

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| IV.2.1 `V̄`, `π^h` and Definition: hermitian representations | 96 / 102 | hermitian forms in [HermitianRepresentationStatements](../../Langlands/Representation/Unitary/HermitianRepresentationStatements.md) | D |
| IV.2.1 Remark 1: `π^h ≅ π` implies hermitian; converse for admissible `π` | 97 / 103 | `CR.HermitianOfSelfDualStatement`, `CR.SelfDualOfHermitianStatement` | P (`hermitianOfSelfDual`, `selfDualOfHermitian`). The printed one-line argument for the first assertion is incomplete; see clarification C2 |
| IV.2.1 Remark 2: uniqueness of the form up to a scalar | 97 / 103 | `CR.HermitianFormUniquenessStatement` | P: `hermitianFormUniqueness` |
| IV.2.1 (IV.2.1.1)–(IV.2.1.2): normalized induction `i_H^G` and its compatibility with `~` and `h` | 97 / 103 | `CR.CompactQuotientNormalizedInductionDualityStatement` | P: [`compactQuotientNormalizedInductionDuality`](../../Langlands/Representation/Unitary/CompactQuotientNormalizedInductionDualityProof.md), carried Library theorem |
| IV.2.2 Definition: unitary representations; uniqueness of the positive form up to a positive scalar | 97 / 103 | `IsUnitarizable`; `CR.HermitianFormUniquenessStatement` | D; C |
| IV.2.2 Corollary (ii): admissible unitary representations are semisimple | 98 / 104 | `Langlands.AdmissibleUnitarySemisimplicityStatement` (every invariant subspace has an invariant complement) | P: `admissibleUnitarySemisimplicity` |
| IV.2.2 Proposition: for a `G`-stable `V₁`, `V₁^⊥` is `G`-stable and `V = V₁ ⊕ V₁^⊥` | 98 / 104 | `Langlands.AdmissibleUnitaryOrthogonalComplementStatement`, specifying the actual orthogonal complement | P: [`Langlands.admissibleUnitaryOrthogonalComplement`](../../Langlands/Representation/Unitary/AdmissibleOrthogonalComplementProof.md) |
| IV.2.2 Corollary (i): `dim End_G(V) = 1` iff irreducible | 98 / 104 | `CR.UnitaryAdmissibleEndomorphismStatement` | P: `unitaryAdmissibleEndomorphism` |
| IV.2.3 (IV.2.3.1)–(IV.2.3.2): the invariant positive form on `i_H^G τ` | 98–99 / 104–105 | `CR.CompactQuotientUnitaryInductionStatement` | P: [`compactQuotientUnitaryInduction`](../../Langlands/Representation/Unitary/CompactQuotientUnitaryInductionProof.md) |

## IV.3 Square-integrable representations

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| IV.3.1 Definition: `L²(G, χ, dg*)₀`, its invariant positive form | 99 / 105 | `Langlands.Induction.CentralL2` and its form `centralL2Form` | D |
| IV.3.1 Remark: `L²(G, χ, dg*)₀` is the space of smooth vectors of its completion | 99 / 105 | `CR.CentralL2SmoothVectorsStatement` | P: [`centralL2SmoothVectors`](../../Langlands/Representation/MatrixCoefficient/CentralL2SmoothVectorsProof.md) |
| IV.3.2 Definition: square integrable modulo the centre, essentially square integrable | 99 / 105 | `Langlands.IsSquareIntegrableModCenter` and the predicates of [UnitarySquareIntegrableStatements](../../Langlands/Representation/Compact/UnitarySquareIntegrableStatements.md) | D |
| IV.3.2 Remark: one nonzero square-integrable coefficient suffices for irreducible `π` | 100 / 106 | `CR.SquareIntegrableCoefficientCriterionStatement`, which also assumes `π` admissible | P (`squareIntegrableCoefficientCriterion`) with the added hypothesis; see clarification C3 |
| IV.3.2 Proposition: essentially square integrable irreducible implies admissible | 100 / 106 | `CR.EssentiallySquareIntegrableAdmissibleStatement` | P |
| IV.3.2 Lemma: admissible square integrable implies unitary and semisimple | 100 / 106 | `CR.SquareIntegrableUnitarySemisimpleStatement` | P |
| IV.3.3 Lemma (i)–(ii): Schur orthogonality and the formal degree | 101 / 107 | `CR.SchurOrthogonalityStatement` | P: `schurOrthogonality` |
| IV.3.3 Corollary: linear independence of coefficients; the compact case | 102 / 108 | `CR.CoefficientLinearIndependenceStatement`, `CR.CompactCoefficientLinearIndependenceStatement` | P |
| IV.3.3 Remark: the same with `A ⊂ Z(G)` cocompact | 102 / 108 | `CR.CocompactCentralSquareIntegrableStatements` | P: [`cocompactCentralSquareIntegrable`](../../Langlands/Representation/Compact/CocompactCentralSquareIntegrableProof.md) |
| IV.3.4 Notes | 102 / 108 | — | X |

## Source clarifications

- **C1. IV.1.3 Lemma (printed p.90 / PDF p.96).** The Lemma reads "supposons qu'il existe une
  représentation compacte `(π, V)` de `G`. Alors le centre de `G` est compact." Read
  literally, it is false: the zero representation is compact for every `G`, and the discrete
  group `ℤ` is countable at infinity with non-compact centre `ℤ`. The proof passes to an
  irreducible subquotient and picks a nonzero vector, so it uses a nonzero representation. The
  published statement makes this explicit with `Nontrivial π`. Its Markdown
  ([CompactRepresentationCriterionStatements](../../Langlands/Representation/Compact/CompactRepresentationCriterionStatements.md))
  gives the same reading. Countability at infinity is the hypothesis `[SigmaCompactSpace G]`.
- **C2. IV.2.1 Remark 1 (printed p.97 / PDF p.103).** For the first assertion, Renard writes
  that "the canonical duality between `V` and `V^h` gives such a form". The form
  `B₀(x, y) = e(x)(y)` given by an isomorphism `e` is invariant, sesquilinear and
  nondegenerate, but it need not be hermitian. For example, take the trivial group on `ℂ²`
  and `e` given by a non-hermitian invertible matrix. The assertion itself holds and is
  proved (`hermitianOfSelfDual`). The published
  [HermitianRepresentationStatements](../../Langlands/Representation/Unitary/HermitianRepresentationStatements.md)
  records a complete route through admissibility and the generalized eigenspaces of
  `B₀* = B₀(T ·, ·)`.
- **C3. IV.3.2 Remark (printed p.100 / PDF p.106).** The source assumes only that `π` is
  irreducible. The published statement also assumes admissibility, for the reasons given in
  its Markdown
  ([SquareIntegrableCoefficientCriterionStatement](../../Langlands/Representation/MatrixCoefficient/SquareIntegrableCoefficientCriterionStatement.md)):
  the published square-integrability predicate includes admissibility, and the proof uses
  irreducibility of the smooth dual. For the groups of the book the extra hypothesis is
  automatic by the VI.2.2 Theorem (`RationalPointsIrreducibleAdmissibleStatement`, proof task
  `173e44ba`). For a general t.d. group the Remark without admissibility is not stated.

## Proof-publication update, 14 November 2026

The following five exact proof records are independently accepted and public. Each has
accepted machine validation for `lake-build`, `exact-target`, `unchanged-statement` and
`frozen-inputs`, with no reviewer qualifications. Their frozen Lean/Markdown pairs still
equal the files at the update's Library commit `e13a307a22881999a6db8ebc753d4d0b6dd359e5`.
The theorem names and links are in the corresponding rows above.

| Item | Accepted proof record | Independent reviewer | Published Library commit |
| --- | --- | --- | --- |
| IV.1.4 Remark 1 | `91ee69d3-815d-4155-8774-e9c45467978b` | Reviewer 746 | `51e4d8972659f1ffcf0ca89e8eee9540a30b52d3` |
| IV.2.2 Proposition | `7f378503-003f-448b-805a-ab518c4c2315` | Reviewer 736 | `51e4d8972659f1ffcf0ca89e8eee9540a30b52d3` |
| IV.2.3 | `dbfe5c3f-6375-4511-b33e-deb54dcc5494` | Reviewer 42 | `b128d289028bf75629e9e364ecf151c484b27a85` |
| IV.3.1 Remark | `2a372f49-7294-4240-b742-1d5dc2cec511` | Reviewer 41 | `b128d289028bf75629e9e364ecf151c484b27a85` |
| IV.3.3 Remark | `237d0820-b6ed-4a7e-9931-ae2fcf534325` | Reviewer 77 | `b128d289028bf75629e9e364ecf151c484b27a85` |

For IV.2.1, the carried published
[`CR.compactQuotientNormalizedInductionDuality`](../../Langlands/Representation/Unitary/CompactQuotientNormalizedInductionDualityProof.lean)
by Worker 142 has exactly the unchanged target statement as its type. Its current Library
declaration and paired proof Markdown supply the evidence recorded here; the original
proof-review receipt was not recovered in this instance. A development check inspected
the theorem at independent universes `uG` and `v`, using only `propext`, `Classical.choice`
and `Quot.sound`. All six proof modules also compile at the update's Library base with
zero errors or warnings. These development checks do not create new proof-acceptance
receipts.

The six proof links document the implemented arguments in detail. Their scope and routes
are:

- **IV.1.4 Remark 1.** For arbitrary smooth complex `τ` and nonzero `c : ℝ≥0`, the theorem
  proves the equivalence of the two `κ` identities under rescaling of Haar measure.
  Algebraic linear functionals reduce rescaling of the integrated action to rescaling
  scalar Bochner integrals. The formula for `d = κ⁻¹` is the resulting formal-degree
  consequence; it is not a separately named theorem in this module.
- **IV.2.1.** For a Hausdorff locally compact nonarchimedean group and any closed
  cocompact subgroup `H`, the theorem supplies a positive smooth half-modulus and proves
  smooth-dual naturality for every smooth complex coefficient object. Hermitian duality
  is expressed through supplied equivariant antilinear models. The proof constructs a
  relative quotient measure, applies integral duality, tests naturality on pairings and
  obtains the hermitian clause by pointwise antilinear postcomposition.
- **IV.2.2 Proposition.** The hypotheses are admissibility, compact-open cofinality and
  a supplied invariant positive form. The conclusion specifies the orthogonal, its
  stability and `IsCompl V₁ V₁^⊥`. Surjectivity of the smooth-dual map for the restricted
  positive form gives `s ∈ V₁` with `v - s ∈ V₁^⊥`. Renard instead projects inside
  finite-dimensional compact-open fixed spaces.
- **IV.2.3.** With the same closed cocompact subgroup setting and a positive half-modulus,
  every supplied invariant positive coefficient form gives the pointwise pairing in
  `renardSpace`. Every nonzero positive invariant functional produces the stated induced
  form, and the proof also constructs one to prove unitarizability. Finite translates
  establish strict positivity; `RelativeQuotientMeasure` supplies existence without an
  `InvariantFunctionalStatement` premise.
- **IV.3.1 Remark.** For a unitary central character and a Haar measure on `G/Z(G)` that
  is also right invariant, the smooth vectors of the canonical Hilbert completion are
  exactly the image of `CentralL2`. Finite compact-open coset averages approximate a fixed
  vector. A pointwise Cauchy argument and Fatou's lemma then produce its smooth
  square-integrable representative.
- **IV.3.3 Remark.** The target retains a closed central subgroup `A`, compact `Z(G)/A`,
  and Haar measures on both quotients that are also right invariant. It proves all five
  clauses: convergence equivalence, admissibility, unitarity and semisimplicity, Schur
  orthogonality, and coefficient independence, with the specified central-character
  hypotheses. Proper projection `G/A → G/Z(G)` pushes Haar measure forward, allowing
  transport of the published centre-quotient results. Comparison of the two Haar measures
  on compact-open-invariant coefficient norms proves convergence equivalence.

## Summary

The six formerly open proof rows now have proofs of their published propositions.
The other rows retain their original statuses and scope; this update is a focused
publication audit of those six rows. In particular, C1–C3 remain in force: the
IV.1.3 Lemma needs a nonzero representation, the printed argument of IV.2.1 Remark 1 is
incomplete, and the IV.3.2 Remark is stated with an additional admissibility hypothesis.
These distinctions remain relevant to exact source coverage and whole-book completion.
