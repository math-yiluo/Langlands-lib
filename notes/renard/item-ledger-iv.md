# Renard 2026, Chapter IV: item-by-item coverage ledger

Worker 1222, executor of the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`, revision 1. This note is the Chapter IV part of
the item ledger that the task contract requires, in the format of the published
[Chapter V](item-ledger-v.md), [Chapter VI](item-ledger-vi.md) and
[Chapter VII](item-ledger-vii.md) ledgers (status codes as there). It lists every headed
item of Chapter IV and the unheaded assertions found, with printed / PDF pages
(PDF = printed + 6), Lean declarations and proof status at Library commit
`9951a27f5fd8ebbdc4bbe68eb6be65b1d0c2eb4a`. Two statements were published later, at Library
`24a49431a1a304ab4190fc6ef1f7e7d21c2d41be`; their rows (IV.1.4 Remark 1 and the IV.2.2
Proposition) say so. A published statement is not a proof; every row keeps the proof status
explicit.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. Chapter IV is printed
pp.87–102 / PDF pp.93–108.

Worker 1222 read each item in the source and the docstring and Markdown of each matched
declaration. Proof status comes from a scan for theorems whose type is exactly the
statement. Unless another namespace is written, statements are in
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
| IV.1.4 Remark 1: `d(τ)` depends on the Haar measure, precisely `d_{cμ}(τ) = d_μ(τ)/c` | 92 / 98 | `CR.CompactFormalDegreeHaarScalingStatement`: `κ` satisfies the identity (ii) for `μ` exactly when `cκ` satisfies it for `cμ`, for every smooth `τ`. The published [CompactFormalDegreeStatements](../../Langlands/Representation/CompactCoefficient/CompactFormalDegreeStatements.md) records that the remark is not stated there | S: Task 5758 (candidate `6b60fb4f`, published at Library `24a49431`) |
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
| IV.2.1 (IV.2.1.1)–(IV.2.1.2): normalized induction `i_H^G` and its compatibility with `~` and `h` | 97 / 103 | `CR.CompactQuotientNormalizedInductionDualityStatement` | S: task `3a4ab626` |
| IV.2.2 Definition: unitary representations; uniqueness of the positive form up to a positive scalar | 97 / 103 | `IsUnitarizable`; `CR.HermitianFormUniquenessStatement` | D; C |
| IV.2.2 Corollary (ii): admissible unitary representations are semisimple | 98 / 104 | `Langlands.AdmissibleUnitarySemisimplicityStatement` (every invariant subspace has an invariant complement) | P: `admissibleUnitarySemisimplicity` |
| IV.2.2 Proposition: for a `G`-stable `V₁`, `V₁^⊥` is `G`-stable and `V = V₁ ⊕ V₁^⊥` | 98 / 104 | `Langlands.AdmissibleUnitaryOrthogonalComplementStatement`. The published `AdmissibleUnitarySemisimplicityStatement` concludes only that some invariant complement exists; the orthogonal complement is the route of its proof ([AdmissibleSemisimplicityStatement](../../Langlands/Representation/Unitary/AdmissibleSemisimplicityStatement.md)) | S: Task 5760 (candidate `9085ff98`, published at Library `24a49431`) |
| IV.2.2 Corollary (i): `dim End_G(V) = 1` iff irreducible | 98 / 104 | `CR.UnitaryAdmissibleEndomorphismStatement` | P: `unitaryAdmissibleEndomorphism` |
| IV.2.3 (IV.2.3.1)–(IV.2.3.2): the invariant positive form on `i_H^G τ` | 98–99 / 104–105 | `CR.CompactQuotientUnitaryInductionStatement` | S: task `e551f0b6` |

## IV.3 Square-integrable representations

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| IV.3.1 Definition: `L²(G, χ, dg*)₀`, its invariant positive form | 99 / 105 | `Langlands.Induction.CentralL2` and its form `centralL2Form` | D |
| IV.3.1 Remark: `L²(G, χ, dg*)₀` is the space of smooth vectors of its completion | 99 / 105 | `CR.CentralL2SmoothVectorsStatement` | S: task `e8c4b2ed` |
| IV.3.2 Definition: square integrable modulo the centre, essentially square integrable | 99 / 105 | `Langlands.IsSquareIntegrableModCenter` and the predicates of [UnitarySquareIntegrableStatements](../../Langlands/Representation/Compact/UnitarySquareIntegrableStatements.md) | D |
| IV.3.2 Remark: one nonzero square-integrable coefficient suffices for irreducible `π` | 100 / 106 | `CR.SquareIntegrableCoefficientCriterionStatement`, which also assumes `π` admissible | P (`squareIntegrableCoefficientCriterion`) with the added hypothesis; see clarification C3 |
| IV.3.2 Proposition: essentially square integrable irreducible implies admissible | 100 / 106 | `CR.EssentiallySquareIntegrableAdmissibleStatement` | P |
| IV.3.2 Lemma: admissible square integrable implies unitary and semisimple | 100 / 106 | `CR.SquareIntegrableUnitarySemisimpleStatement` | P |
| IV.3.3 Lemma (i)–(ii): Schur orthogonality and the formal degree | 101 / 107 | `CR.SchurOrthogonalityStatement` | P: `schurOrthogonality` |
| IV.3.3 Corollary: linear independence of coefficients; the compact case | 102 / 108 | `CR.CoefficientLinearIndependenceStatement`, `CR.CompactCoefficientLinearIndependenceStatement` | P |
| IV.3.3 Remark: the same with `A ⊂ Z(G)` cocompact | 102 / 108 | `CR.CocompactCentralSquareIntegrableStatements` | S: task `8e03231f` |
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

## Summary

Every headed item and every unheaded assertion found in Chapter IV is stated or under review.
Two items were stated by Worker 1222's candidates, both published at Library `24a49431`:
IV.1.4 Remark 1 (`6b60fb4f`, proof Task 5758) and the IV.2.2 Proposition in its
orthogonal-complement form (`9085ff98`, proof Task 5760). The published statement for the
IV.2.2 Corollary (ii) gives only the existence of an invariant complement. The IV.3.2 Remark
is stated only for admissible `π` (C3). All published items are proved except six
statements with open proof tasks: the two statements just named,
`CompactFormalDegreeHaarScalingStatement` (IV.1.4 Remark 1, Task 5758) and
`AdmissibleUnitaryOrthogonalComplementStatement` (IV.2.2 Proposition, Task 5760), and four
earlier ones, `CompactQuotientNormalizedInductionDualityStatement` (IV.2.1),
`CompactQuotientUnitaryInductionStatement` (IV.2.3), `CentralL2SmoothVectorsStatement`
(IV.3.1 Remark) and `CocompactCentralSquareIntegrableStatements` (IV.3.3 Remark). The source clarifications are
C1–C3 above: the IV.1.3 Lemma needs a nonzero representation, the printed argument of
IV.2.1 Remark 1 is incomplete, and the IV.3.2 Remark is stated with an admissibility
hypothesis.
