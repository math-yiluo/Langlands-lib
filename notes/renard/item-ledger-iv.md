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
appear below. The further IV.3.2 statement update uses Library
`457e31a2131a1083c26931d33fec09a71fea54d6` and records the remaining exact proof task.
The IV.3.2 definition update additionally verifies the published raw predicates and
their admissibility comparison at Library `af5d652c2f2ff5b35b4ce4dbbf7cbec8bbf3e99e`.
The 16 November 2026 update adds the separate IV.3.2 counterexample assertion,
its published statement and exact proof owner, checked at Library
`b4005ae3c4a406e2d1193548306b79d7ab745811`.
On 17 November 2026, Worker 5099 (executor of Task 6678) updated clarification C3 and the
IV.3.2 Remark row against Library `b369a8f280229cf081a17f96b81c7a8c1ff1f539`, at the
operator's request.
On 18 November 2026, Worker 4988 (executor of Task 6678) updated the two IV.3.2 Remark rows,
clarification C3 and the Summary against Library `ba9d1e9ac8e4b6f239a8bbf0ba15e6743fd140c9`, after both exact proofs were
published.
On 20 November 2026, Worker 1222 checked positive-form uniqueness against Library
`74c4eb01e237c126a7194e8eee1bc9606ef2ffc8` and added the unnumbered IV.2.1 assertion on
unnormalized induction.
On 21 November 2026, Worker 1222 checked the opening of IV.3.1 against Library
`a11d1e75f52192f694c9901f4b7fd7098b0f8ff9` and recorded the central-quotient Haar measure.

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
| IV.2.1 unnormalized induction can fail to preserve hermitian representations even when `H \ G` is compact | 97 / 103 | Counterexample still to formalize in Task 1222 | Open. The candidate witness is the trivial representation of the upper Borel of `GL₂(ℚ₂)`. |
| IV.2.1 (IV.2.1.1)–(IV.2.1.2): normalized induction `i_H^G` and its compatibility with `~` and `h` | 97 / 103 | `CR.CompactQuotientNormalizedInductionDualityStatement` | P: [`compactQuotientNormalizedInductionDuality`](../../Langlands/Representation/Unitary/CompactQuotientNormalizedInductionDualityProof.md), carried Library theorem |
| IV.2.2 definition of a unitary representation | 97 / 103 | `Langlands.InvariantPositiveForm` and `Langlands.IsUnitarizable` | D. The first carries a chosen invariant positive form, and the second asserts its existence. |
| IV.2.2 uniqueness of the invariant positive form up to a positive real scalar | 97 / 103 | [`Langlands.InvariantPositiveForm.exists_pos_rescale_eq`](../../Langlands/Representation/Unitary/AdmissibleFormUniqueness.md) | P (checked Library reuse at the source hypotheses). |
| IV.2.2 Corollary (ii): admissible unitary representations are semisimple | 98 / 104 | `Langlands.AdmissibleUnitarySemisimplicityStatement` (every invariant subspace has an invariant complement) | P: `admissibleUnitarySemisimplicity` |
| IV.2.2 Proposition: for a `G`-stable `V₁`, `V₁^⊥` is `G`-stable and `V = V₁ ⊕ V₁^⊥` | 98 / 104 | `Langlands.AdmissibleUnitaryOrthogonalComplementStatement`, specifying the actual orthogonal complement | P: [`Langlands.admissibleUnitaryOrthogonalComplement`](../../Langlands/Representation/Unitary/AdmissibleOrthogonalComplementProof.md) |
| IV.2.2 Corollary (i): `dim End_G(V) = 1` iff irreducible | 98 / 104 | `CR.UnitaryAdmissibleEndomorphismStatement` | P: `unitaryAdmissibleEndomorphism` |
| IV.2.3 (IV.2.3.1)–(IV.2.3.2): the invariant positive form on `i_H^G τ` | 98–99 / 104–105 | `CR.CompactQuotientUnitaryInductionStatement` | P: [`compactQuotientUnitaryInduction`](../../Langlands/Representation/Unitary/CompactQuotientUnitaryInductionProof.md) |

## IV.3 Square-integrable representations

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| IV.3.1 opening: from the unimodularity of `G` to a two-sided Haar measure on `G/Z(G)` | 99 / 105 | [`Langlands.Haar.centralQuotient_isMulRightInvariant`](../../Langlands/Representation/Unitary/CentralQuotientForm.md) and regular left Haar existence | P (checked Library reuse at the source hypotheses) |
| IV.3.1 Definition: `L²(G, χ, dg*)₀`, its invariant positive form | 99 / 105 | [`Langlands.Induction.CentralL2`, `centralL2Representation`, `centralL2Form`](../../Langlands/Representation/MatrixCoefficient/CentralL2.md) | D for the smooth right-regular subspace, where each entire function has an open right stabilizer. The action and form use the two-sided quotient measure. The larger space of locally constant functions in the literal definition remains open. See the [faithfulness discussion](../../Langlands/Representation/MatrixCoefficient/CentralL2SmoothVectorsStatement.md#faithfulness-notes). |
| IV.3.1 Remark: `L²(G, χ, dg*)₀` is the space of smooth vectors of its completion | 99 / 105 | `CR.CentralL2SmoothVectorsStatement` | P for the smooth reading of the Definition: [`centralL2SmoothVectors`](../../Langlands/Representation/MatrixCoefficient/CentralL2SmoothVectorsProof.md) |
| IV.3.2 Definition: square integrable modulo the centre, essentially square integrable | 99 / 105 | `Langlands.SmoothRep.IsSquareIntegrableModuloCenter` and `Langlands.SmoothRep.IsEssentiallySquareIntegrableModuloCenter` in [SmoothSquareIntegrability](../../Langlands/Representation/MatrixCoefficient/SmoothSquareIntegrability.md) | D: neither assumes admissibility or irreducibility. The older `Langlands.IsSquareIntegrableModCenter` is admissibility conjoined with the first predicate, by `Langlands.SmoothRep.isSquareIntegrableModCenter_iff` |
| IV.3.2 Remark: one nonzero square-integrable coefficient suffices for irreducible `π` with unitary central character | 100 / 106 | [`CR.SingleCoefficientSquareIntegrabilityStatement`](../../Langlands/Representation/MatrixCoefficient/SingleCoefficientSquareIntegrabilityStatement.md), without assumed admissibility | P: [`singleCoefficientSquareIntegrability`](../../Langlands/Representation/MatrixCoefficient/SingleCoefficientSquareIntegrabilityProof.md) (exact proof Task 6678, `cf5dbeda-85bf-4ad9-8db5-f2f1445f4dc8`), without admissibility, countability or reductivity. The older `CR.SquareIntegrableCoefficientCriterionStatement` is P (`squareIntegrableCoefficientCriterion`) with admissibility; see C3 |
| IV.3.2 Remark, second assertion: this criterion fails without irreducibility | 100 / 106 | [`CR.NonirreducibleSquareIntegrabilityCounterexampleStatement`](../../Langlands/Representation/MatrixCoefficient/NonirreducibleSquareIntegrabilityCounterexampleStatement.md), using the raw all-coefficients predicate | P: [`nonirreducibleSquareIntegrabilityCounterexample`](../../Langlands/Representation/MatrixCoefficient/NonirreducibleSquareIntegrabilityCounterexampleProof.md) (exact proof Task 7180, `a326697e-2603-4828-9948-308b70e7369c`): the left regular representation of the discrete infinite dihedral group on its complex group algebra |
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
- **C3. IV.3.2 Remark (printed p.100 / PDF p.106).** The source assumes an irreducible smooth
  `π` with a unitary central character, without admissibility. The older published statement
  assumes admissibility, as explained in its Markdown
  ([SquareIntegrableCoefficientCriterionStatement](../../Langlands/Representation/MatrixCoefficient/SquareIntegrableCoefficientCriterionStatement.md)):
  its square-integrability predicate includes admissibility, and its proof uses that
  hypothesis to obtain irreducibility of the smooth dual. That narrower theorem is unchanged.
  The newly published
  [SingleCoefficientSquareIntegrabilityStatement](../../Langlands/Representation/MatrixCoefficient/SingleCoefficientSquareIntegrabilityStatement.md)
  states the general t.d.-group Remark without admissibility, using the all-coefficients
  condition directly. Its exact proof was then open in Task 6678
  (`cf5dbeda-85bf-4ad9-8db5-f2f1445f4dc8`); it is now published, see the 18 November
  update below. The published
  `essentiallySquareIntegrableAdmissible` theorem consumes the all-coefficients condition;
  it can yield admissibility after this implication is proved, not as an initial input.
  A reductive-group admissibility theorem alone cannot discharge this general t.d.-group
  obligation. With the publication of that statement, C3 became a proof gap rather than a
  missing statement. That gap is closed: the 18 November update below records the current
  status of C3.

  *Update, 17 November 2026 (Library `b369a8f280229cf081a17f96b81c7a8c1ff1f539`).* What
  follows is a paper analysis. None of it is a Lean theorem, and it changes no status code
  in the table.

  - *Status (as of 17 November; superseded by the 18 November update below).* No Library
    theorem had type `CR.SingleCoefficientSquareIntegrabilityStatement`. The statement was
    unproved in Lean and was not to be used as a premise. Task 6678 stayed open for its
    proof. Its statement Markdown is unchanged.
  - *Admissible case.* Under admissibility the Remark is proved. The published
    `squareIntegrableCoefficientCriterion` concludes `IsSquareIntegrableModCenter`, which
    contains the all-coefficients condition for some unitary central character. By
    `coefficientNorm_eq` the coefficient norm does not depend on that choice, so the
    condition holds for the specified character. No separate admissible-form module is
    needed.
  - *Reduction to admissibility.* Under the hypotheses of the general statement, its
    conclusion holds exactly when `π` is admissible. One direction is the admissible case
    above. For the other, `essentiallySquareIntegrableAdmissible` with the trivial twist
    derives admissibility from the all-coefficients condition. So the open content is this:
    an irreducible smooth representation with a unitary central character and one nonzero
    smooth coefficient in L² is admissible. Restricted to discrete groups, the statement
    is equivalent to assertion (D) of Proposition 3.3 in the
    [analysis note](iv32-single-coefficient-analysis.md) (see its Sections 2–3): for
    every discrete group `G` and every unitary character χ of `Z(G)` with `G/Z(G)`
    infinite, the twisted space ℓ²(G/Z, χ) has no algebraically simple
    ℂ[G]-submodule. The infinite-quotient hypothesis is
    needed: for the trivial group, ℓ²(G/Z, χ) = ℂ is itself simple. When `G/Z(G)` is
    finite, every coefficient is in L² and there is nothing to prove.
  - *Paper route for every t.d. group.* Worker 4988 proposed this route, and Worker 5099
    checked it on paper. It uses no countability, no von Neumann dimension theory and no
    reductive structure. Write `χ` for the central character and `ℓ` for the functional
    of the given coefficient.
    1. The map `y ↦ (g ↦ ℓ(π(g) y))` is an injective linear map from `V` into the
       χ-equivariant space L²(G/Z, χ). It intertwines `π` with right translation (Step A
       of the analysis note). Fix an open compact `K` with `V^K ≠ 0`; then `χ` is trivial
       on `K ∩ Z`. Let `H` be the closed subspace of right-`K`-invariant functions and
       `V_K ⊆ H` the image of `V^K`.
    2. Right translation by `g` followed by averaging over `K` gives a bounded operator
       `e_K R(g) e_K` on `H`, and these operators commute with left translations. The
       algebra `B` that they generate contains the identity and preserves `V_K`. By
       irreducibility of `π`, `B v = V_K` for every nonzero `v ∈ V_K`.
    3. Bounded Schur lemma: `End_B(V_K) = ℂ`. This endomorphism algebra `D` is a division
       algebra. Fix `u ≠ 0` in `V_K`. For each `e ∈ D`, an operator in `B` that sends `u`
       to `e u` acts on `D u` as right multiplication by `e`. Take `d ∈ D` and let `T` be
       such an operator for `d`. If `d − λ` were invertible for every `λ ∈ ℂ`, the operators
       for `(d − λ)⁻¹` would invert `T − λ` on the closure of `D u` for every `λ`. That
       contradicts the nonempty spectrum of `T` there, so `d` is a scalar.
    4. Let `N` be the commutant of left translations on `H`, and `ξ` the normalized
       χ-twisted indicator function of `KZ`. Then `τ(x) = ⟨x ξ, ξ⟩` is a trace on `N`. For
       `x ∈ N`, `x ξ` is bi-`K`-invariant and `(x* ξ)(g)` is the complex conjugate of
       `(x ξ)(g⁻¹)`. Inversion preserves the bi-invariant `μ`, so `‖x ξ‖ = ‖x* ξ‖`, and
       polarization gives `τ(x y) = τ(y x)`. The trace is faithful, because left
       translates of `ξ` span a dense subspace of `H`.
    5. Fix `v ≠ 0` in `V_K`. Let `q` be the orthogonal projection onto the common kernel
       of all `b ∈ B` with `b v = 0`. This kernel is closed and invariant under left
       translations, so `q ∈ N`; also `q v = v`, so `τ(q) > 0`. Let `u_1, …, u_n ∈ V_K` be
       linearly independent. Take `b_j ∈ B` with `b_j v = u_j`, and, by Jacobson density
       (using step 3), `a_i ∈ B` with `a_i u_j = δ_ij v`. Then `a_i b_j − δ_ij` kills `v`,
       so `a_i b_j q = δ_ij q`. Hence `p = Σ_j b_j q a_j` is an idempotent in `N` with
       `τ(p) = n τ(q)`. If `r` is the range projection of `p`, then
       `p = r + r p (1 − r)`, so `τ(p) = τ(r) ≤ 1`. Thus `dim V^K ≤ 1/τ(q)`. Hence `π`
       is admissible, and `squareIntegrableCoefficientCriterion` gives the conclusion.

    The argument computes traces only of operators in `N`. An earlier version wrote the
    vectors of `V_K` as `x ξ` with `x ∈ N`, which would need coefficient vectors to be
    bounded vectors. The version being formalized avoids that step.
  - *Formalization.* The route is being formalized in Task 6678. At the operator's
    direction, it is staged in reviewable pieces: the bounded Schur lemma, the tracial
    finiteness, then the Hecke operators and the admissibility theorem. If a step fails,
    the failure is to be reported, and C3 then reverts to an unresolved gap. The
    [analysis note](iv32-single-coefficient-analysis.md) predates this route, and its
    Section 4 calls the general case unresolved. This update supersedes that assessment,
    not the note's proofs.

  *Update, 18 November 2026 (Library `ba9d1e9ac8e4b6f239a8bbf0ba15e6743fd140c9`).* C3 is resolved. The exact proof
  `82d49555-92de-46ac-ba53-8c6023899f61` of Task 6678 is independently accepted and
  public, with accepted machine validation for `lake-build`, `exact-target`,
  `unchanged-statement` and `frozen-inputs`. Its theorem
  `CR.singleCoefficientSquareIntegrability`
  ([SingleCoefficientSquareIntegrabilityProof](../../Langlands/Representation/MatrixCoefficient/SingleCoefficientSquareIntegrabilityProof.md))
  has type exactly `CR.SingleCoefficientSquareIntegrabilityStatement.{u, v}`. The
  statement and its Markdown are unchanged. The *Status* bullet above is superseded:
  the statement may now be used as a premise.

  - *Implemented route.* `CR.SingleCoefficient.isAdmissible_of_memLp` proves the
    admissibility claim of the *Reduction to admissibility* bullet, under the hypotheses
    of the statement. Then `squareIntegrableCoefficientCriterion` and `coefficientNorm_eq`
    give the conclusion, as in the *Admissible case* bullet. The admissibility proof
    follows steps 1–5 of the paper route. The proof Markdown describes the implemented
    version; two details differ from the wording above. The Hilbert space is
    `ℓ²(G/J)` with `J = K · Z(G)` and `K` a compact open subgroup on whose central
    elements `χ` is trivial; coefficient functions are recorded at chosen coset
    representatives. With Mathlib's inner product, which is conjugate-linear in the
    first argument, the trace is written `τ(x) = ⟨ξ, x ξ⟩`.
  - *Pieces.* As the operator directed, the route was published in three reviewed
    pieces. Definition `c451c9a6-eb97-47f6-8138-1a5c5c7d822d` contains the bounded
    Schur lemma and the tracial finiteness theorem
    (`Langlands/Analysis/BoundedSchur.lean`, `Langlands/Analysis/TracialFiniteness.lean`).
    Definition `623e2c9c-8405-43cf-9920-8e7132a6c839` contains the Hecke operators on the
    twisted coset space and their support files
    (`Langlands/Representation/MatrixCoefficient/HeckeOperator.lean`, `TwistedCosetSpace.lean`,
    `CentralCosetSum.lean` and `Langlands/Analysis/FiberLIntegral.lean`). The proof
    `82d49555-92de-46ac-ba53-8c6023899f61` contains the admissibility theorem and the target.
  - *Scope.* The Lean theorem has no admissibility, countability, reductivity or
    finite-dimensionality hypothesis, and the group and carrier universes are independent.
    The second assertion of the Remark, failure without irreducibility, is the separate
    exact proof `8ce9377f-9877-4bc9-8716-6b42762d9824` of Task 7180 (accepted by
    Reviewer 7809, Task 7180 done); its table row is updated together with this one.

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

## IV.3.2 statement publication, 14 November 2026

Statement `71f341e5-5a75-4c1d-86b0-ea5a0b549815` is independently accepted by
Reviewer 2594 and public, with no qualifications. Integration
`8b2b359c401f4733aecb8b222ae9db53` first published its pair at Library
`b3a1bdaf15715f16a43643513b7cbb6cbb58ef3a`. Both frozen file hashes agree with
the pair at the update's Library commit `457e31a2131a1083c26931d33fec09a71fea54d6`.
The original IV.3.1–IV.3.2 passage, printed pp.99–100 / PDF pp.105–106, was read
again for this update.

The proposition retains a Hausdorff locally compact totally disconnected group, the
actual quotient `G/Z(G)` with a Borel Haar measure that is also right invariant,
an irreducible smooth complex representation and a specified unitary central
character. A nonzero smooth coefficient whose quotient norm is in `L²` implies
the same for every smooth coefficient, using the same character and measure.
There is no admissibility, reductivity, countability or finite-dimensionality
hypothesis, and the group and representation-carrier universes remain independent.
The source leaves the proof to the reader; this publication supplies only its
Prop-valued statement. Exact proof Task 6678
(`cf5dbeda-85bf-4ad9-8db5-f2f1445f4dc8`) targets
`Langlands.Renard.CompactRepresentation.SingleCoefficientSquareIntegrabilityStatement.{u,v}`.
Neither the statement publication nor creation of that task closes C3.

## IV.3.2 definition publication, 14 November 2026

Definition `b9326b4f-014a-4bd7-897b-b0f99847a221` is independently accepted by
Reviewer 2950 and public, with no qualifications. Integration
`9c9266a91bce45419ef9e64faaf4642c` first published its
[SmoothSquareIntegrability pair](../../Langlands/Representation/MatrixCoefficient/SmoothSquareIntegrability.md)
at Library `ba00e0970dd9ba6222ccc056ca2ee7f06bcc8181`. The frozen hashes below
equal both the local files and the files at this update's Library commit
`af5d652c2f2ff5b35b4ce4dbbf7cbec8bbf3e99e`.

| File in `Langlands/Representation/MatrixCoefficient/` | SHA256 |
| --- | --- |
| `SmoothSquareIntegrability.lean` | `34dd107c754946cca3a6fb450ce836eedd2ae4871ee9eafc7fd16d963935a76b` |
| `SmoothSquareIntegrability.md` | `652cfa1d2eb219af32985d48ecc47a70e034a251873985eebd7856f011da5ed5` |

On a bundled smooth complex representation,
`Langlands.SmoothRep.IsSquareIntegrableModuloCenter` requires a smooth unitary
scalar central character and `MemLp` with exponent `2` for every descended
coefficient norm on the actual quotient `G/Z(G)`, for the supplied Borel Haar
measure. `Langlands.SmoothRep.IsEssentiallySquareIntegrableModuloCenter`
requires this condition after some arbitrary character twist with open kernel,
using the same measure. Neither predicate assumes admissibility or
irreducibility; the group and carrier universes are independent, with no
topology or finite-dimensionality hypothesis on the representation carrier.
The original Definition, printed p.99 / PDF p.105, was read again for this update.

These definitions can be formed for any topological group with the specified
quotient measure. Renard IV.3.1–IV.3.2 instead works with a unimodular t.d. group
and a bi-invariant quotient Haar measure. The broader definitional domain
asserts no source theorem in that domain; applications must retain their
theorem hypotheses. The existing admissibility-bearing predicate is unchanged:
`Langlands.SmoothRep.isSquareIntegrableModCenter_iff` identifies it with
admissibility conjoined with the new all-coefficients predicate. The pair also
proves the trivial-twist implication and, for an admissible object, comparison
with arbitrary smooth twists satisfying the older predicate. It does not
identify arbitrary twists with the real powers of a specified positive
character used by the separate
`Langlands.IsEssentiallySquareIntegrableModCenter` construction.

These intrinsic comparisons supply neither the IV.3.2 admissibility theorem nor
the single-coefficient implication. The admissibility theorem is already
published separately as recorded above. The general single-coefficient
statement and its exact proof Task 6678
(`cf5dbeda-85bf-4ad9-8db5-f2f1445f4dc8`) retain their statement-only and open-proof
statuses, respectively; C3 is unchanged by this definition publication.

## IV.3.2 counterexample statement publication, 16 November 2026

The second assertion of the Remark, printed p.100 / PDF p.106, expressly states
that the single-coefficient criterion fails without irreducibility. The source
leaves the proof to the reader. It is a separate obligation from the positive
irreducible implication. The original IV.3.1–IV.3.2 passage, printed pp.99–100 /
PDF pp.105–106, was read again for this update.

Statement `a6d3d023-4703-4073-8124-4de70be9c6b8` is independently accepted by
Reviewer 4321 without qualifications and public. Integration
`be26ad70dedc4ea6b2f91438c6f45330` first published its
[Lean/Markdown pair](../../Langlands/Representation/MatrixCoefficient/NonirreducibleSquareIntegrabilityCounterexampleStatement.md)
at Library `0b7bb3fdbe6e0386b666b6b099a3bc9cd3ad7e18`. The frozen hashes agree
with the workspace and this update's Library `b4005ae3c4a406e2d1193548306b79d7ab745811`:

| File in `Langlands/Representation/MatrixCoefficient/` | SHA256 |
| --- | --- |
| `NonirreducibleSquareIntegrabilityCounterexampleStatement.lean` | `9c0fa0024578305d6846495e6d450ad8a0a03cfc1929433f9b9809ea10be3c55` |
| `NonirreducibleSquareIntegrabilityCounterexampleStatement.md` | `9f2d2547cc555cc4e310562c92933fec718eee1a2a0eba82e209ecaa9f61c01a` |

The proposition negates the universal single-coefficient implication restricted
to nonirreducible smooth complex representations. Classically it asserts an
actual nonirreducible representation with a unitary scalar central character
and a nonzero smooth coefficient whose descended norm is in `L²`, which fails
`Langlands.SmoothRep.IsSquareIntegrableModuloCenter`. That conclusion predicate
contains neither admissibility nor irreducibility, so its failure concerns
coefficient integrability itself.

The statement retains Hausdorff locally compact totally disconnected groups,
an ambient bi-invariant Borel Haar measure and a separate bi-invariant Borel
Haar measure on the actual quotient `G/Z(G)`. Both the group and representation
carrier lie in `Type 0`, as appropriate for this existence assertion. It assumes
no admissibility, reductivity, finite dimension, finite length or countability.
Fresh development check `41ba672e-419c-4fba-b53a-3c7429d043ba` compiled the
statement without errors or warnings and inspected it as a Prop-valued
definition. This check supplies no proof of the counterexample assertion.

Exact proof Task 7180 (`a326697e-2603-4828-9948-308b70e7369c`), revision 1,
targets
`Langlands.Renard.CompactRepresentation.NonirreducibleSquareIntegrabilityCounterexampleStatement`.
Its contract pins environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` and
preserves the published target and imported objects. At this update it is ready
and has no proof candidate. The positive criterion's Task 6678
(`cf5dbeda-85bf-4ad9-8db5-f2f1445f4dc8`) was also inspected at revision 1:
it remains ready with no candidate. Both assertions remained unproved at this
update; both are now proved (see the table rows and the 18 November update of C3).

## Summary

The six formerly open proof rows now have proofs of their published propositions.
The IV.3.2 Remark additionally has published statements and published exact proofs for
the general irreducible criterion without admissibility (Task 6678) and for its failure
without irreducibility (Task 7180).
The IV.3.2 Definition now has published reusable
predicates without admissibility and a proved comparison with the older predicate.
The IV.2.2 uniqueness check applies `exists_pos_rescale_eq` to two positive forms on an
irreducible admissible smooth complex representation. The hypotheses of a Hausdorff,
locally compact totally disconnected group give compact-open cofinality by
`CR.HermitianProof.compactOpenCofinal`. The example compiled with independent group and
carrier universes in development check `8542112d-4eba-4b0a-a4fa-200055c19859`.
The implemented proof compares the two Hermitian identifications, applies admissible Schur
and obtains strict positivity by taking the ratio of the two diagonal values on a nonzero vector.
The IV.3.1 reuse check applies the published right-invariance theorem to a regular left
Haar measure on the actual quotient by the full center. The center is closed and abelian.
Its left Haar measure is right invariant by commutativity, so its modular character is one.
The quotient is locally compact and Hausdorff with its quotient topology, and Mathlib
supplies its regular left Haar measure in the Borel measurable structure. The ambient
modular character is assumed trivial as in the source. The published theorem gives right
invariance by the normal-subgroup formula for conjugation moduli. Development check
`214a5b6b-59b3-4b5c-82c2-54bcec6641ab` compiled this application with an arbitrary group
universe and no countability hypothesis.
The unnumbered IV.2.1 counterexample remains an open obligation.
C1 and C2 remain relevant: the
IV.1.3 Lemma needs a nonzero representation, and the printed argument of IV.2.1 Remark 1 is
incomplete. C3 is resolved: the IV.3.2 Remark without admissibility is proved in Lean
through admissibility, by the trace argument that C3 records.
These distinctions remain relevant to exact source coverage and whole-book completion.
