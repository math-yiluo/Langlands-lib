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
`179f569bc35e58b829420ce0590c9f4d0ff43c21`. Other statuses retain their historical
survey scope. The status codes, the abbreviation of
task identifiers and the method of checking are those of the Chapter VI ledger.
All declarations below are in `Langlands.Aubert.General.RepresentedParabolic`
(abbreviated `RP`) unless another namespace is written. The focused source maps
[root-exponent-tempered-progress](root-exponent-tempered-progress.md) and
[parabolic-functors-tempered-progress](parabolic-functors-tempered-progress.md) give
more detail for VII.1–VII.2.

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
| VII.1.2 Theorem (Casselman's criterion) | 221 / 227 | `RP.ArbitraryParabolicCasselmanCriterionStatement`; necessity `RP.ArbitraryParabolicCasselmanNecessityStatement` | S: task 2e8d370f; necessity P: `arbitraryParabolicCasselmanNecessity`. Derived: the condition is the strictly positive root cone, which the source proof establishes, not the printed coroot chamber `^G_P[𝔞*_M]^+`; the two differ (for example for `SL_3`). This source discrepancy is documented in the statement's Markdown; the printed chamber form is not stated |
| VII.1.3 Theorem | 224 / 230 | `RP.MaximalLeviSupercuspidalReducibilityStatement` (and the reduction `RP.MaximalLeviSupercuspidalReducibilityFromInputsStatement`) | S: task 004e00e1; reduction P. Derived: an arbitrary maximal rational parabolic, with "`M = M'` and `ρ^w = ρψ`" expressed through a normalizing element of `G(F)` |
| VII.1.3 Corollary (i)–(iii) | 226 / 232 | `RP.MaximalLeviBlockStatements` | S: task f4046ca6. Derived: (ii) is stated as the nonvanishing criterion behind faithfulness (the passage to faithfulness of `r_D` uses the Bernstein decomposition of `M(M)` and A.VIII.1); (iii) is stated as `i_P^G` full, faithful and essentially surjective between the blocks. G: the functor `r_D` and the unit isomorphism `π → i_P^G r_D(π)` are not stated |

## VII.2 Tempered representations

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| VII.2.1 Definition | 227 / 233 | `IsNormalizedExponentTempered` | D (normalized parameter; see the progress note for the corrected sign convention) |
| VII.2.1 Remark 1, first assertion (full-group exponents unitary) | 227 / 233 | `NormalizedTemperedFullGroupExponentStatement` | P: `normalizedTemperedFullGroupExponent` |
| VII.2.1 Remark 1, second assertion (central character unitary) | 227 / 233 | `NormalizedTemperedCentralCharacterStatement` (nonzero representations) | P: `normalizedTemperedCentralCharacter` |
| VII.2.1 Remark 2 (square-integrable implies tempered) | 227 / 233 | `RP.SquareIntegrableNormalizedTemperedStatement` | S: task 1ebce298 |
| VII.2.1 Remark 3 (standard parabolics suffice) | 227 / 233 | `NormalizedTemperedStandardReductionStatement` | P: `normalizedTemperedStandardReduction` |
| VII.2.2 Lemma | 227–228 / 233–234 | `RP.LeviInductionNormalizedTemperedStatement` | P: `leviInductionNormalizedTempered` |
| VII.2.3 Lemma | 229 / 235 | `RP.UnitaryJacquetPartTemperedStatement` | P: `unitaryJacquetPartTempered` |
| VII.2.4 Proposition | 229 / 235 | `RP.TemperedInductionUnitaryReciprocityStatement`, `RP.TemperedJacquetUnitaryRestrictionStatement` | P: `temperedInductionUnitaryReciprocity`, `temperedJacquetUnitaryRestriction` |
| VII.2.4 Lemma | 230 / 236 | `RP.TemperedSquareIntegrableUnitaryPartStatement` | S: task f0ff1d42 |
| VII.2.5 Proposition | 230 / 236 | `RP.TemperedGeometricLemmaStatement` | P: `temperedGeometricLemma` |
| VII.2.6 Theorem | 231 / 237 | `RP.TemperedIrreducibleDiscreteSeriesStatement`, `RP.TemperedIrreducibleDiscreteSeriesUniquenessStatement`; step `RP.NormalizedTemperedSubrepresentationStatement` | S: task 225f7d3d; step P: `normalizedTemperedSubrepresentation` |
| VII.2.6 Corollary | 232 / 238 | `RP.TemperedIrreducibleUnitarizableStatement` | S: task 225f7d3d |
| VII.2.6 Remark (without irreducibility the Corollary can fail) | 232 / 238 | `RP.TemperedReducibleNotUnitarizableStatement` | S: Task 5685 (candidate `9492bbaa`) |

## VII.3 Intertwining operators of induced representations

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| VII.3.1 Definition (Bruhat order `≤_{PQ}`) | 232 / 238 | `Langlands.Geometric.BruhatLE` (on actual double cosets), `IsBruhatRefinement` | D |
| VII.3.1: `1̄` is the least element when `P = Q` and the greatest when `Q = P̄` | 232–233 / 238–239 | `RP.BruhatIdentityExtremesStatement` | S: Task 5685 |
| VII.3.2 filtrations and their comparisons | 233–234 / 239–240 | `RP.PQSupportGradedStatement`; support subfunctors in `Intertwining/PQRegularity` | P: `pqSupportGraded` |
| VII.3.3 Lemma (`PQ`-regularity) | 234 / 240 | `RP.PQRegularityLemmaStatement`; `IsPQRegular` | S: task d935ffb6 |
| VII.3.4 Proposition and preceding integral identification | 235–236 / 241–242 | `RP.PQIntertwiningOperatorStatement` (derived: the integral replaced by an arbitrary identification); explicit integral form `RP.PQIntegralIntertwiningOperatorStatement` | Derived form P: `pqIntertwiningOperator`; integral form P: [`pqIntegralIntertwiningOperator`](../../Langlands/Representation/Intertwining/PQIntegralIntertwiningOperatorProof.md) |
| VII.3.5 Proposition (i) | 237 / 243 | `RP.PQIntertwiningCompositionStatement` | P: [`pqIntertwiningComposition`](../../Langlands/Representation/Intertwining/PQIntertwiningCompositionProof.md) |
| VII.3.5 Proposition (ii) | 237 / 243 | `RP.PQIntertwiningInnerLeviStatement` | P: [`pqIntertwiningInnerLevi`](../../Langlands/Representation/Intertwining/PQIntertwiningInnerLeviProof.md) |
| VII.3.5 Proposition (iii) | 237 / 243 | `RP.PQIntertwiningOuterLeviStatement` | P: [`pqIntertwiningOuterLevi`](../../Langlands/Representation/Intertwining/PQIntertwiningOuterLeviProof.md) |
| VII.3.5 opening assertion "`d(P, Q)` is the length of the element `w ∈ W(A_M)` with `w · P = Q`" | 236 / 242 | `Langlands.GroupScheme.MinimalParabolicDistanceLengthStatement` (minimal `M`, corrected form) | S: Task 5687 (candidate `5d306e19`). For non-minimal `M` the printed assertion is a source issue (I1 below) |

## VII.4 The Langlands classification

| Item | Pages | Lean | Status |
| --- | --- | --- | --- |
| VII.4.1 Definition (Langlands triplet) | 241 / 247 | `IsLanglandsTriplet`, chambers `Langlands.GroupScheme.restrictedCorootChamber` (`LanglandsClassification/LanglandsTriplet`) | D |
| VII.4.1 Lemma | 241 / 247 | `RP.LanglandsTripletOppositeRegularityStatement`; proved steps `RP.LanglandsTripletOppositePieceSeparationStatement`, `RP.LanglandsTripletOppositeRegularityReductionStatement` | S: task 78bf8d31; steps P |
| VII.4.2 Theorem (i)–(iii) | 243 / 249 | `RP.LanglandsQuotientUniqueStatement`, `RP.LanglandsQuotientInjectiveStatement`, `RP.LanglandsQuotientExhaustiveStatement`, conjunction `RP.LanglandsClassificationStatement` | S: task 717df3ca |
| VII.4.2 sentence after (i): `J(P, σ, ψ)` is characterized by `ℜ(ψ) ∈ ℜ(Exp(A_M, r_{P̄}^G(π)))` | 243 / 249 | `RP.LanglandsQuotientExponentCharacterizationStatement` | S: Task 5653 |

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
  `MinimalParabolicDistanceLengthStatement` (candidate `5d306e19`, proof Task 5687); the non-minimal case is
  a source issue with the counterexample above.

## Genuine gaps of Chapter VII

1. VII.1.2: the printed coroot-chamber form of Casselman's criterion (see the row; the
   source proof establishes the root-cone form, which is stated).
2. VII.1.3 Corollary: the functor `r_D`, its faithfulness as stated by the source, and the
   unit isomorphism `π → i_P^G r_D(π)`. Stating them needs the projection of `r_P^G`
   onto the component `M(M)_D`, which is not constructed.

Update at Library `9951a27f`: the former gap 3 (VII.3.5, minimal-`M` form of the opening
assertion) is stated by the published `MinimalParabolicDistanceLengthStatement` (candidate
`5d306e19`, proof Task 5687). For non-minimal `M`, and for the length relative to `P_∅` when
`P ≠ P_∅`, the printed assertion fails as written (I1). `6a38904d` (VII.4.2 sentence after
(i)) is published, with proof Task 5653. `9492bbaa` (VII.2.6 Remark and the VII.3.1 extremes
of the Bruhat order) is published, with proof Task 5685.
