# Jacquet exponents and Langlands quotients: source map

Author: Worker 19, task `616fab20-3cae-49ab-94f4-d28791b2b93f`.
Opposite-induction documentation contributed by Worker 264.
Relative-family coverage updated on 24 October 2026 against Library commit
`3f303847f99b2a44e2f0074b9cca983bab26eb3e`. This update records publication of
the generic comparison/head, supported all-regular comparison, and relative
recovery statements, with their exact proof tasks. It also records the existing
flattened-Levi equivalence and canonical head, the independently approved but
unpublished cosocle statement, and the remaining semistandard construction.
The reviewed scope audit of S78 Lemma 5.3 remains applicable.
Exact publication receipts appear below. Declaration names refer to this
Library tree; receipts identify earlier commits where contributions entered
it. Review approval alone does not make an unpublished candidate a Library
dependency.

This note maps the original theorems behind Silberger's Langlands quotient
theorem for `GL_n` to the Lean proposition definitions that state them, and
lists the constructions still needed for the families that are not yet stated.
The theorem families are proposition definitions (`def` returning `Prop`);
none of those families is proved here. The construction section also names
actual definitions and their intrinsic compatibility lemmas. This note proves
nothing.

Worker 3's [Silberger reading note](../henniart/silberger.md) gives the
statement of S78 Theorem 4.1, the translation of `-iλ` into decreasing
`|det|` exponents for upper block parabolics, and the proof outline of
S78 §§5–7. This note does not repeat them; it adds the Casselman and
Silberger 1979 inputs and the Lean side.

## Originals and reading extent

| Key | Original | Source ID |
| --- | --- | --- |
| S78 | A. J. Silberger, *The Langlands quotient theorem for p-adic groups*, Math. Ann. 236 (1978), 95–104. Project file `Silberger (1978), The Langlands quotient theorem for p-adic groups.pdf`; PDF page 1 is printed p.95. | `provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354` |
| S79 | A. J. Silberger, *Introduction to harmonic analysis on reductive p-adic groups*, Princeton University Press and University of Tokyo Press, 1979. Central-Library file `Silberger--Introduction to harmonic analysis on reductive p-adic groups (book)--1979.pdf`; PDF page = printed page + 6. | `silberger-1979-harmonic-analysis` |
| C95 | W. Casselman, *Introduction to the theory of admissible representations of p-adic reductive groups*, draft of 1 May 1995. Central-Library folder `Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/`; printed and PDF pages coincide. | `casselman-1995-admissible-representations` |
| W03 | J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d’après Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333; SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`; PDF page = printed page − 234. | `waldspurger-2003-plancherel` |
| K94 | S. S. Kudla, *The local Langlands correspondence: the non-archimedean case*, §§0–1.1, printed pp.367–368, and §2.2, pp.372–374; SHA256 `0e1f9bc9986fc136081f0eed1aaafb50302acacb5a23e9538581f2f5b533198b`. | `kudla-1994-local-langlands-nonarchimedean` |
| L-UBC | R. P. Langlands, *On the Classification of Irreducible Representations of Real Algebraic Groups*, UBC Digital Mathematics Archive retypesetting (77 pages). Project file `Langlands original classification manuscript- Lemma 4.4 cited by Silberger 1978.pdf`. | `provided-02bc3867bc46a71e44607fdb9cbc2464a31753e4e31b0025a8db239a91034861` |
| BZ77 | I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive p-adic groups. I*, Ann. Sci. ENS (4) 10 (1977), 441–472. Central-Library file `Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`; PDF page = printed page − 439. | `bernstein-zelevinsky-1977-induced-i` |

S78 was read in full, with page images for the formulas and proofs.
From S79, the front matter and pp.1–9, p.25, pp.35–36, pp.90–92, pp.119–129,
pp.177–194, pp.287–292 and pp.307–311 were read; this is not a reading of
the whole book. From C95, pp.13, 16–24, 27–29, 44–45 and 47–51 were read. From
L-UBC, the title page and pp.60–62 (Lemma 4.4 and its proof) were read. From
BZ77, §1.2 and §1.7, p.443, the normalization on p.444, §§2.1–2.7,
pp.446–447, and Corollary 2.13(c) with §2.15(3), p.449, were read for
the multiplicity families below.
Formula-bearing pages in the original reading ranges were checked visually.
For the two exponent criteria, W03 §§I.1–I.3 (pp.239–243), Theorem I.4.1
(p.245), Lemmas II.1.1 and II.1.5 (pp.251–252), Proposition III.1.1
(p.263), and §III.2 with Proposition III.2.2 (pp.265–266) were read from
the retained text. K94 §§0–1.1, pp.367–368, and §2.2, pp.372–374, were read
for the induction convention, analytic temperedness, quotient and block
classification. The expanded K94 reading was checked in page images.

L-UBC is not a scan of the 1973 IAS preprint, so S78's citation of
"[3], Lemma 4.4, p.87" is a locator in that preprint, not in this PDF.
C95's 1995 draft is not identified with the Casselman preprint in S78's
bibliography.

## Normalizations the statements must keep

- **Normalized induction and Jacquet modules.** S78 p.96 uses
  `I(P,σ) = Ind_P^G(δ_P^(1/2) σ)`. The Library's
  `normalizedParabolicInduced` (in `Langlands.Representation.Induction.Parabolic`)
  uses the same `δ_P^(1/2)`. The Library's `normalizedOppositeParabolicInduced`
  (in `Langlands.Representation.Induction.OppositeParabolic`) induces from the
  actual lower block parabolic with the inverse `(T.leviHalfModulus B)⁻¹` of
  the same upper half modulus, inflated along the opposite Levi projection.
  Reading this scalar as `δ_(P̄)^(1/2)` needs a separate Haar-modulus
  comparison, which the module does not prove. The upper-radical version
  `Langlands.GLBlockModulusHaarStatement` is now proved by
  `Langlands.glBlockModulusHaar` in
  `Langlands.Group.GL.BlockModulusHaarProof`. The Library's
  `normalizedJacquet` (in
  `Langlands.Representation.Jacquet.Parabolic`) acts on the coinvariants of the
  **upper** block unipotent radical by `m·[v] = δ_P(m)^(-1/2) [ρ(m) v]`, with
  the full block modulus `leviModulus`.
- **Opposite parabolic in S78's exponents.** S78 §2, p.97, defines class
  exponents through the Jacquet module of the **opposite** parabolic, written
  `δ_P^(1/2) π(P̄)`. For `GL_n`, a block-reversing permutation conjugates
  this to the upper parabolic with reversed block sizes and transports the
  test chamber, as detailed below.
- **Casselman's minimal modulus.** C95 Theorem 4.4.6, p.45, prints
  `|χ δ_∅^(-1/2)(a)| < 1` for characters of the unnormalized Jacquet module.
  Passing to normalized exponents requires identifying the restriction of the
  minimal-parabolic modulus `δ_∅` to `A_Θ` with the modulus of `P_Θ`.
- **Removed directions.** C95 Theorem 4.4.6 tests only
  `a ∈ A_Θ^- \ A_∅(O) A_Δ`, so compact and central directions are excluded and
  the case `P = G` is vacuous. S78's short summary ("for all p-pairs, tends to
  zero") must not be read literally at `P = G`.
- **Weak versus strict.** S78 p.98 and S79 Lemma 4.5.3, pp.185–186, state
  temperedness with the weak inequality `|χ(a)| ≤ 1`; the page image confirms
  the non-strict sign. Including `P = G` in S79 Lemma 4.5.3 forces a unitary
  central exponent. A weak inequality is never S78's regularity condition.
- **Scalar versus generalized central characters.** C95 Theorem 5.4.1,
  pp.49–50, is projectivity for a **fixed scalar** central character. It does
  not apply in the larger category with a generalized central character.
- **Contragredients.** The Library's contragredient uses the inverse group
  element, so a scalar central character becomes its inverse, without complex
  conjugation. S79 Corollary 3.2.8, p.125, also replaces the parabolic by its
  opposite when comparing class exponents; that is a separate Jacquet-module
  compatibility.
- **Equal exponents.** Blocks with equal real exponents are not in S78's
  regular chamber relative to each other. They are first grouped into one
  tempered block by the separate `GL_n` tempered classification. S79
  Lemma 4.5.15, p.191, gives complete reducibility and temperedness of
  tempered induction for general reductive groups, not irreducibility.

The upper Haar comparison is Worker 117's independently accepted proof
`3008bd3f-5a63-44c7-aa33-d84249d03f88` version 1, published at
`9488f8128fc175e4f17b08d2a86eac54056fa753` with integration receipt
`d3d0eb9b1fc1484991942b6d554b4f4d`. Its closing theorem has exactly the published
statement as its type and covers every block shape. This status does not itself
supply the opposite or relative refinement Haar comparisons.

## Families and their Lean status

"Not yet stated" means that the Library has no source-faithful proposition for
the family yet. It is not a placeholder assertion.

| Family and original | Lean status |
| --- | --- |
| **Central characters.** C95 p.18 (finiteness under a subgroup), Prop. 2.1.3 p.19, Prop. 2.1.9(a)–(b) p.21 (generalized decomposition, finite support, uniform power); twist and inverse-element dual action pp.21–22. | `CentralExponentPrerequisitesStatement` and `IsCenterFinite` in `Langlands.Representation.Exponents.CentralStatement`, over `centralCharacterSpace` and `generalizedCentralCharacterSpace` of `Langlands.Representation.Exponents.Central`. |
| **Finite length.** S79 Thm 5.4.1.6, pp.291–292 (finite generation p.25, admissibility pp.35–36). The fixed central character is a step in the proof, not a hypothesis. | `GLAdmissibleFiniteLengthStatement` in `Langlands.Representation.Classification.FiniteLengthStatement`, specialized to `GL_n` over every finite extension of `Q_p`. |
| **Fixed central character splitting.** C95 Thm 5.3.1 (stated p.48, proved p.49), Thm 5.4.1 with Prop. 5.4.2, pp.49–50, and Cor. 5.4.4, pp.50–51; used in S78 Cor. 5.4, p.100. | `GLFixedCentralCharacterSplittingStatement` and `HasCompactSmoothCoefficientsModCenter` in `Langlands.Representation.Classification.FixedCentralSplittingStatement`: sections of surjections onto, and retractions of injections out of, an admissible representation with compactly supported coefficients modulo the center, all with one fixed scalar central character. |
| **Square-integrability prerequisites.** C95 pp.21–22 and §2.5, pp.28–29, including Prop. 2.5.3 (one coefficient suffices for an irreducible representation). | `GLSquareIntegrabilityPrerequisitesStatement` in `Langlands.Representation.Classification.SquareIntegrabilityStatement`: Haar-measure independence, unitary twists, the contragredient, and Prop. 2.5.3, over the analytic `IsSquareIntegrableModCenter`. |
| **Jordan–Hölder multiplicities.** S78 §1, p.97 (`[π_2, π_1]`, the number of factors of a composition series of `π_1` equivalent to `π_2`); BZ77 §1.2, p.443 (`JH^0(π)` with multiplicities). Both treat the number as well defined without stating the Jordan–Hölder theorem. | `ObjectRepFiltration.factorMultiplicity`, `HasJordanHolderMultiplicity` and `JordanHolderMultiplicityIndependenceStatement` in `Langlands.Representation.Filtration.MultiplicityStatement`, over any field and monoid. `HasJordanHolderMultiplicity A τ m` asks for one composition series with exactly `m` factors equivalent to `τ`; the independence statement makes `m` unique. |
| **Root/weight cone.** S78 Lemma 7.1, p.103; L-UBC Lemma 4.4, pp.61–62. Weight coefficients strictly positive; complementary root coefficients nonnegative and subtracted. | `RootWeightConeDecompositionStatement` in `Langlands.Representation.Classification.RootWeightConeStatement`. Only the support set is asserted unique. Its actual block-parabolic specialization is published as `GLParabolicRootWeightConeStatement` in `Langlands.Representation.Classification.ParabolicConeStatement`: a unique consecutive coarsening, strictly decreasing averaged determinant exponents, nonpositive within-fiber residual partial sums, and upper-parabolic/embedded-Levi containments over every commutative ring. Central shifts are unrestricted; only the coarser shape is asserted unique. |
| **Square-integrability exponent criterion.** C95 Thm 4.4.6, p.45; W03 Prop. III.1.1, p.263. Related S79 Thm 4.4.4, pp.177–180 (coefficients on bounded central strips), Thm 4.5.10, pp.188–189 (unitary central character, modulo the center). | Published: `GLSquareIntegrableExponentCriterionStatement` in `Langlands.Representation.Classification.SquareIntegrableExponentStatement`. For a nonzero admissible scalar-central-character representation: analytic square-integrability iff the central character is unitary and every normalized Jacquet exponent is strictly bounded by one on the closed negative chamber outside compact/central directions. |
| **Tempered exponent criterion.** S78 p.98; S79 Lemma 4.5.3 and Cor. 4.5.4, pp.185–186, Lemma 4.5.6, p.187; W03 Prop. III.2.2, pp.265–266. | Published: `GLTemperedExponentCriterionStatement` in `Langlands.Representation.Classification.TemperedExponentStatement`. For an admissible scalar-central-character representation: analytic `L^(2+ε)` temperedness iff every normalized Jacquet exponent has norm at most one on the entire closed negative chamber. The one-block condition forces unitarity when the representation is nonzero. The analytic bridge is derived in the paired Markdown. |
| **Tempered unitarity and induction.** S79 Cor. 4.5.13, p.190, and Lemma 4.5.15, p.191. | `GLTemperedInductionPrerequisitesStatement`, comprising `GLTemperedUnitarityStatement` and `GLTemperedInductionStatement` in `Langlands.Representation.Classification.TemperedInductionStatement`, is published. It states irreducible analytic tempered unitarity, and unitarizability of arbitrary irreducible tempered block-Levi input together with complete reducibility and analytic temperedness of its actual normalized induction. It assumes no tensor decomposition and asserts no general induction irreducibility. |
| **Discrete-series temperedness and Jacquet quotients.** S79 Thm 4.5.10(1)–(2), pp.188–189, and Thm 4.5.18(1)–(2), p.193; class-exponent identification in Lemma 3.2.2(2), p.121, and Thm 3.2.4, pp.122–123. | Published: `GLDiscreteSeriesJacquetPrerequisitesStatement` in `Langlands.Representation.Classification.DiscreteSeriesJacquetStatement`. Its components state analytic temperedness of irreducible square-integrable product-Levi representations and, for discrete-series Levi input and irreducible tempered `π`, equivalence of subquotient occurrence in the actual opposite normalized Jacquet module with a surjective intertwiner from that whole module. |
| **Discrete-series support and tempered Jacquet summands.** S79 Cor. 4.5.11, pp.189–190, and Thm 4.5.18, p.193. | `GLTemperedDiscreteSeriesPrerequisitesStatement` in `Langlands.Representation.Classification.TemperedSupportStatement` states support and the both-inductions summand clause; the Jacquet quotient equivalence is stated separately in the preceding row. The support clause embeds an irreducible tempered representation into normalized opposite induction from discrete-series Levi data. The summand clause retains discrete-series input and equates its subquotient occurrence in the actual opposite normalized Jacquet module with complete reducibility of both opposite normalized inductions and occurrence of the original representation as a direct summand of each. These are proposition definitions with proofs still open. Cor. 4.5.11's prescribed weakly critical-exponent refinement is now published separately; see the status below. |
| **Cuspidal Jacquet multiplicities.** S78 §2, pp.97–98; S79 Thm 5.4.1.1, pp.287–288, Thm 3.3.1, pp.126–127, §5.4.4, pp.307–311. For discrete-series data the quoted result covers only the maximal tempered summand. | The quasicuspidal case is stated for `GL_n`: `PadicQuasicuspidalJacquetTheorems` in `Langlands.Representation.CuspidalSupport.JacquetInductionStatement` (Bernstein–Zelevinsky 1977, Cor. 2.13; its `AssociatedJacquetFiltrationTheorem` gives a filtration of the normalized Jacquet module of quasicuspidal induction with one Weyl-transported quotient per minimal conjugating permutation). This is the `GL_n` counterpart of S79 Thm 5.4.1.1. Published: `GLCuspidalJacquetMultiplicityPrerequisitesStatement` in `Langlands.Representation.Classification.CuspidalJacquetMultiplicityStatement`. For irreducible cuspidal input and associated standard positive-rank Levis, it gives the full upper and opposite normalized Jacquet composition lengths and each constituent's exact `HasJordanHolderMultiplicity`, counted by the actual minimal conjugating permutations and their representation-equivalence subtype. It assumes neither finite length nor a decomposition. The non-cuspidal discrete-series formula applies to the unitary central part and is now stated separately in the following row. |
| **Discrete-series Jacquet multiplicities.** S79 Thm 5.4.1.1, pp.287–288, and §5.4.4, pp.307–311; weak-exponent comparison on p.187; C95 Prop. 2.1.9, p.21. | Published: `GLDiscreteSeriesJacquetMultiplicityStatement` in `Langlands.Representation.Classification.DiscreteSeriesMultiplicityStatement`. For associated standard positive-rank GL Levis and irreducible square-integrable input, the actual unitary central parts of both normalized Jacquet modules of upper induction are admissible, have the Weyl-count lengths and exact constituent multiplicities, and contain exactly the invariant subspaces with finite tempered composition factors. It neither bounds the full Jacquet length nor imposes one scalar central character on the tempered sum. The identification with tempered composition factors is stated; its full-center/split-center and analytic justifications are documented as derived steps. The representation-theoretic proofs remain open. |
| **Full-dual exponents and class comparison.** S79 §2.4, pp.90–92; Lemmas 3.2.1–3.2.2, Thm 3.2.4 and Cor. 3.2.5(1), pp.120–123; Lemma 4.5.6 and Cor. 4.5.7, pp.187–188. | Published: `GLDualJacquetExponentPrerequisitesStatement` in `Langlands.Representation.Exponents.DualJacquetStatement`. For irreducible admissible positive-rank GL_n sources, its four components state finite smooth dual spectrum, finite uniform nilpotence indices and spanning of the full dual; dual occurrence iff an actual irreducible admissible opposite Jacquet constituent has the prescribed scalar split-center character; analytic temperedness of such a constituent iff that character is unitary for a tempered source; and tempered opposite-inducing support retaining a prescribed unitary character. The arbitrary constituent carrier has its own universe. These statements use the published full transpose dual construction, not the inverse-element contragredient, and do not prove the comparisons. |
| **Weak-critical predicates and support refinement.** S79 §0.3, pp.5–6, and the paragraph before Cor. 4.5.11 through Cor. 4.5.12(3), pp.189–190. | Published constructions: `Exponents.ConjugateBlockPair` and its actual scalar restriction in `Langlands.Representation.Exponents.ParabolicPair`, and `PadicField.TopologicalData.IsWeaklyCriticalDualJacquetExponent`, `IsWeaklyCriticalDualJacquetPair`, `IsWeaklyMinimalDualJacquetPair` in `Langlands.Representation.Exponents.WeakCritical`. Weak criticality requires an occurring unitary exponent and tests strict uniform-index decrease over every proper finer concrete conjugate pair and every extending unitary exponent. Minimality is separately defined; its intrinsic implication to criticality is proved. The converse and prescribed discrete-series support are published proposition definitions in `GLWeaklyCriticalTemperedRefinementStatement`, described below; their proofs remain open. |
| **Multiplicity comparison.** S78 Prop. 5.1, p.99, Lemmas 5.2–5.6, pp.99–101: generic parameters first, then every regular positive one. | The unique-head conclusion of Prop. 5.1 is included in the published regular family below. Lemma 5.2's type-A genericity is now stated as `GLRelativeGenericParameterStatement` in `Langlands.Representation.Classification.RelativeGenericityStatement`: for nested standard block partitions and every real fine-block vector `v₀`, the actual regular coarse parameters whose fine-Weyl stabilizers of `v₀ − t` lie in the coarse Levi Weyl group form an open dense set. This linear-algebraic specialization imposes no representation hypotheses. The representation-theoretic generic family is published as `GLRelativeGenericComparisonStatement` in `Langlands.Representation.Classification.RelativeJacquetMultiplicityStatement`: actual inner constituents have equal inner/ambient opposite-Jacquet multiplicities, with positivity equivalent to an inner quotient, and actual generic inner quotients induce representations with kernel-unique irreducible heads. The [reviewed scope audit](silberger-lemma53-scope.md) gives a GL₂ obstruction to unrestricted Lemma 5.3; this derived target keeps the constituent restriction and documents why its generic summation argument permits arbitrary fine real vectors. `GLRelativeRegularComparisonStatement` in `Langlands.Representation.Classification.RelativeRegularComparisonStatement` is also published: the p.99 positive-root and intermediate discrete-series support data give positive equal multiplicities and a strong head for every strictly decreasing coarse parameter. The continuation and tempered-exponent cone argument remain proof obligations. |
| **Recovery of inducing data.** S78 Props. 5.7–5.9, pp.101–102, Prop. 6.1 and Cor. 6.2, pp.102–103. | Published: `GLRegularLanglandsDataUniquenessStatement` in `Langlands.Representation.Classification.RegularLanglandsStatement` states the ordered block form of Prop. 6.1: isomorphic arbitrary irreducible quotients recover the order, ranks, real exponents and tempered blocks after rank transport. The published `GLRegularLanglandsTensorRecoveryStatement` in `Langlands.Representation.Classification.RegularLanglandsTensorRecoveryStatement` isolates the fixed-shape, fixed-exponent consequence: isomorphic arbitrary irreducible quotients recover equivalence of the actual untwisted tensors of irreducible analytically tempered blocks. It is derived from Prop. 6.1, whose concluding route uses Prop. 5.8 and then Prop. 5.7; it is not unrestricted Prop. 5.7. Published: `GLRelativeRecoveryStatement` in `Langlands.Representation.Classification.RelativeRecoveryStatement` conjoins supported recovery (Prop. 5.7, whose competing inner quotient need not be tempered) and arbitrary-tempered quotient reflection (Prop. 5.8, with no support premise on the coarse input). Both use actual outer quotient maps. `GLRelativeCosocleMultiplicityStatement` has independent approval but is not published in this pinned tree; its status and actual head carriers are detailed below. Semistandard conjugacy (Cor. 6.2) remains unstated. |
| **Exhaustion.** S78 Prop. 7.2, pp.103–104. | Published: `GLRegularLanglandsExhaustionStatement` in `Langlands.Representation.Classification.RegularLanglandsStatement`: every irreducible admissible smooth positive-rank `GL_n` representation is the head of a regular tempered standard module. The representation-level intermediate `GLMaximalConeJacquetQuotientStatement` in `Langlands.Representation.Classification.MaximalConeStatement` is independently accepted and published as contribution `548a0480-4a37-4eef-ab27-086c3e403491`. It selects an actual dual exponent, a globally maximal numerical cone coarsening, its restricted occurring character and an irreducible quotient of the whole opposite Jacquet module that becomes analytically tempered after removing the actual real Levi twist. The statement assumes no tensor factorization and retains arbitrary ambient central twists. Its proof remains open, separately from final exhaustion. |
| **Regular-chamber quotient theorem.** S78 Thm 4.1(1)–(3), p.99, proof §§5–7. | Published: `GLRegularLanglandsQuotientStatement` in `Langlands.Representation.Classification.RegularLanglandsStatement`, the conjunction of unique-head existence, ordered inducing-data uniqueness and exhaustion. The actual upper standard module uses irreducible analytically tempered blocks with strictly decreasing real determinant exponents. All central twists are allowed; one-block regularity is vacuous. Head existence and equality of irreducible quotient kernels are conclusions, not datum fields. |

The two exponent-criterion pairs were independently accepted and published in
Library commit `9a0767626050f3346ad5f25e37cef39f38a5c0dc` and remain present in
the pinned tree above. Their exact contribution versions are respectively
`a16df17b-16a5-4ab5-92b5-e7e1905f3a73` version 1 (square-integrability) and
`63b8c0f4-201b-4e9c-a0b5-50fc1bee907b` version 1 (temperedness). These are
provenance receipts; downstream Lean files import the declarations by name.
The tempered-induction contribution `c537a77e-a4d1-4f3d-b204-55c85d9ff278`
version 1 is independently accepted and published at
`8b1acb7e020811a7961329d198d300fc9f01e5fa`. Its paired Markdown documents the
analytic bridge on both `GL_n` and its actual product Levi, with a proved
Haar-existence helper for the Levi central quotient.
The discrete-series Jacquet contribution
`820310ba-eb40-493f-a4fc-5ec9b8fa246b` version 1 is independently accepted and
published at `e3c2fa98be720f63c6981efbbdf15cd223329e76`; the regular quotient
contribution `f230e502-ddf4-4a2a-a2e9-b6c701272d51` version 1 is independently
accepted and published at `2f8d1873fbaeb581719bc35dbf6f5c9f2d4a8df4`.
The support/summand contribution `f490f06d-c2c8-4618-ac7c-6d7bceab3750`
version 1 is independently accepted and published at
`6c3030e24467888afeb3d4e60546c2301ce4f38d`.
The actual parabolic-cone contribution
`b47f086e-f36d-4aff-85b2-3d237d457424` version 1 is independently accepted
and published at `67dfb8a24d65657a6bf35da262b1009383d873d5`.
The cuspidal multiplicity contribution
`dcb679fc-8b35-4155-bf59-f1a12f4d4d4a` version 1 and relative genericity
contribution `49ee1f52-e0da-4ea4-9656-e3a2ea6c8da0` version 1 are independently
accepted and published at `f1b212cc117b9c34dced95c0ac88e6328827334d`.
Their exact integration receipts are respectively
`4b88ece5e4394eb7a3d41ae3e20dbdbc` and `de00eff0143048778d9887f08a268f82`.
The same commit publishes the independently accepted algebraic construction
`75808046-dba5-4d84-acb8-5f6b2ab94a81` version 1,
`Langlands.Representation.Exponents.UnitaryPart`, with integration receipt
`a943f08eaf554518ad849a583b8ea067`. The three Lean/Markdown pairs in the pinned
Library match their frozen contribution hashes.
The uniform nilpotence construction `e104c69a-52aa-4bb3-b5d8-95d4ba981085`
version 1 and discrete-series multiplicity statement
`dbcb4645-47a3-4e40-a6e1-72c67a4b8c5e` version 1 are independently accepted
and published at `aee7fdb7f6d4283cce4db9035fd9478c923d4926`, with integration
receipts `ebc40b7389c14bf6ac135b5ec78c6586` and
`685a1c198fc54ade90d77062fd77dbde`, respectively.
The full-dual construction `986c54a5-280c-473a-9a79-e9a5c6945646` version 1
is independently accepted and published at
`9ff0d4f8edaf10dd32d87468c3045da6ec3ee5c6`; concrete parabolic pairs
`4272f030-43d9-44cb-b64a-8eed2c6bcc59` version 1 are independently accepted
and published at `ac106a0cb63f5fca8c452213147e8926dd2575af`.
The dual comparison statements `09ef0897-cd46-418e-bcef-9f8a809ec1a0`
version 1 and weak-critical construction
`80787e7f-fad3-4f24-8d7c-36fb42f09368` version 1 are independently accepted
and published at `b263cfa454b11d485198ae46d8290f32435e48c6`, with integration
receipts `c6257995b9b1419f8e73bfa1161a2acf` and
`1e4a38df13c445a5a92ee6420819e86a`. These six Lean/Markdown pairs in the
pinned Library match their frozen contribution hashes.
These publication statuses do not constitute proofs of the proposition
families. The construction units include their intrinsic algebraic and
coordinate laws only.

The support family `3daaab4e-3930-4f66-adae-36f87a7e30d3` version 1 is
independently accepted and published at
`a6c8885e0e4bfcf4ee6d5a4b9a84a6d195085302`, with integration receipt
`579add5eed7847cf9d3125a6aea3b8bd`. Its entry is
`Langlands.GLWeaklyCriticalTemperedRefinementStatement` in
`Langlands.Representation.Exponents.WeakCriticalStatement`. For an irreducible
analytically tempered source it states existence of a standard pair minimal
among all concrete conjugate pairs, discrete-series opposite-inducing support with a prescribed critical character, and criticality
iff minimality for all such pairs. The source route uses Cor. 4.5.11 to supply
the discrete-series class-exponent premise of Cor. 4.5.12(3). Exact Prop
inspection, machine validation, independent review and publication have
passed. The Lean/Markdown pair in the pinned Library matches the frozen
contribution hashes. This publishes the proposition family, not its proof.

## Tensor recovery, real Levi twists and maximal-cone status

The fixed-parameter tensor recovery statement is contribution
`722cffa6-afa3-4fdd-a6f0-095a7bfd87a4` version 1, authored by Workers 19 and 47,
independently approved by Reviewer 1626 and published with integration receipt
`780708401cef4db6989b66704aaf1dff`. The actual real Levi character and twist
construction is contribution `d3f6b7e1-475c-471a-9249-cc6e2ae0485d` version 1,
independently approved by Reviewer 1638 and published with integration receipt
`7a66500a61d746818803be2009cc3583`. Both pairs were verified in Library
`4750a03e101b9ad45fc1a4d90a6a3d02d69c73e9` and remain unchanged in the pinned
snapshot. Their published Lean/Markdown hashes match the workspace pairs.

The tensor recovery target keeps independent field and carrier universes,
positive total rank, a fixed ordered shape and `StrictAnti` exponent, actual
analytic temperedness of every irreducible factor, and weak irreducible
quotient premises. The quotient targets may differ and are related by an
actual smooth isomorphism. Its conclusion is equivalence of the untwisted
product-Levi tensors. It assumes no head or canonical quotient. Its separate
exact proof task `d2bdfb40-719d-4b6b-a907-94d3e6ae182d` must prove this target
without assuming full inducing-data uniqueness. The published helper
`PadicField.TopologicalData.blockIsoOfTensorEquiv` then recovers individual
factor isomorphisms; that helper does not prove tensor recovery.

`Langlands.Representation.Twist.LeviRealPower` constructs
`T.leviRealPowerCharacter B t` and `T.leviRealPowerTwist B t` for arbitrary
real vectors and arbitrary actual representations of the product Levi. It
proves determinant-product and block-scalar formulas, open kernel,
zero/addition/inverse laws, cancellation and preservation and reflection of
smoothness. At block scalars the character has exponents `B.size i * t i`.
Neither a tensor decomposition nor a temperedness certificate is required.
The empty rank-zero shape is included. These intrinsic laws supply the
negative real twist used by the maximal-cone target, not its temperedness
conclusion.

The maximal-cone statement contribution `548a0480-4a37-4eef-ab27-086c3e403491`
version 1 has terminal machine acceptance `e0b9b5fc-214f-4178-a5d2-94edbd031671`
and unqualified independent Reviewer 1655 approval in review
`7268291c-6ef3-4b52-9961-ccb858f81cfc`. It is published at Library
`2da3640f8f3978d2ba6ce703d6c26cf1941ba234`, with integration receipt
`84bbaaa905d74daeae75494e72aabdbf`. Its published pair matches the independently
reviewed hashes. Exact recovery check `e11eb0d2-b670-4d0b-9274-3776b02a1898`
returned zero diagnostics and confirmed a Prop-valued definition with independent
`uF` and `uV`. Its separate exact proof task is
`b291a31b-9606-4ffc-b9d8-ce62346cfa09`; that task excludes circular use of final
Langlands exhaustion. These receipts establish publication of the statement,
not a proof of its assertion.

The maximality compares the selected coarsened block count with every numerical
cone coarsening of every actual dual exponent, without assuming a quotient or
temperedness for competitors. Character restriction is pointwise composition
with the consecutive grouping map. The selected representation is a quotient
of the whole normalized opposite Jacquet module, and removing its determinant
exponents gives `IsTemperedModCenter` for every Borel Haar measure on the full
Levi central quotient. The published Haar-existence construction makes this
quantification nonvacuous. The assertion includes arbitrary ambient real central
twists. Its exact source is the selection argument in S78 Proposition 7.2,
pp.103–104; the original final inequality on p.104 is `≤ 1`. The one-way
weak-coefficient-to-integrability bridge uses S79 Theorem 4.5.1 and definition,
pp.183–184, Lemma 4.5.3, pp.185–186, and W03 I.1(5), p.241, II.1.1, p.251, and
III.2/III.2.2, pp.265–266. This is derived source correspondence, not a proof.

## Relative comparison and recovery publications

The following version-1 statement contributions are independently accepted
and published at `3f303847f99b2a44e2f0074b9cca983bab26eb3e`. All six Lean/Markdown
files match their frozen reviewed hashes. The module prefix in the table is
`Langlands.Representation.Classification`.

| Module and exact aggregate | Contribution | Independent reviewer | Integration receipt | Separate exact proof task |
| --- | --- | --- | --- | --- |
| `RelativeJacquetMultiplicityStatement`: `Langlands.GLRelativeGenericComparisonStatement` | `6cb00363-e978-467e-a954-698e5f27378c` | Reviewer 1979 | `fb051d7e5734471b981cdc154435c88e` | `9c878f57-a3a7-4cbc-8657-a44eed8c51cf` |
| `RelativeRegularComparisonStatement`: `Langlands.GLRelativeRegularComparisonStatement` | `a5f4fcae-6a2b-4cc1-bdae-e7ec69b44afd` | Reviewer 1989 | `16c732e7806a4049a37982feebc2521e` | `b8ecf398-d8ff-48bd-a6b3-5da6557b7655` |
| `RelativeRecoveryStatement`: `Langlands.GLRelativeRecoveryStatement` | `647f664c-4790-4afc-8210-a09e938c8e3e` | Reviewer 1991 | `7dcf1ceb825a4ba7bccd1def7f59d974` | `9f88af41-d438-475e-ae54-6ef33bcfb8ed` |

These are statement publications, not proofs. Their exact proof tasks preserve
all independent universes and the reviewed hypotheses. The generic statement
has three independent universes (field, fine input, coarse constituent), the
supported regular statement has four (adding the middle input), and recovery
has six (also separating the competing and outer quotient carriers).

The generic target retains actual subquotient occurrence in the specified
inner induction. Its conclusion supplies two finite composition series with
one common multiplicity; it does not merely equate possibly false predicates.
The head component strengthens uniqueness of the target isomorphism class to
equality of all irreducible quotient kernels. For the all-regular target the
fine parameter is a strictly positive combination of scalar roots, expressed
in determinant coordinates as `e_j/d_j - e_(j+1)/d_(j+1)`. The actual middle
discrete-series quotient and its coarse tempered quotient remain hypotheses.
Its common multiplicity is positive. Both families use the fine twist
`-v₀ + t|fine`, actual upper induction, and positive-upper-half-normalized
opposite Jacquet modules.

Recovery retains the distinction in the original between supported and
arbitrary inputs. `GLSupportedRelativeRecoveryStatement` recovers the
untwisted coarse representation from a common irreducible outer quotient;
the competitor is any irreducible admissible fine inner quotient.
`GLTemperedRelativeQuotientReflectionStatement` starts with arbitrary
irreducible tempered coarse input. A common quotient of its outer induction
and the fine ambient induction must yield an actual fine-to-coarse
surjection. The target assumes neither that surjection nor middle support.
The direct continuation/extraction and tempered-exponent cone argument on
S78 p.102 is therefore a separate proof obligation; the supported comparison
cannot supply a missing support premise.

The cosocle candidate `ea29bd47-14f9-42c7-adf8-7bf5262b62a5` version 1 has
machine acceptance `15dfce51-513b-47b9-9f3a-6f6936753e38` and independent
Reviewer 2000 approval in review `01ed4a00-d84c-46af-b67d-0e86b011b2d8`.
At this update its publication is still pending, so it is not a Library
dependency. Its proposed pair is
`Langlands/Representation/Classification/RelativeCosocleMultiplicityStatement`,
and its exact proposition is `Langlands.GLRelativeCosocleMultiplicityStatement`.
It states the Proposition 5.9 equality in the two existing canonical heads,
for arbitrary tempered coarse input and any actual regular-positive outer
irreducible quotient. There is no fine/middle support premise on the coarse
input and no fine-ambient quotient premise. One natural number, possibly zero,
is the Jordan–Hölder multiplicity on both sides; both finite series are
conclusions. The field, fine, middle, coarse and outer quotient carriers have
five independent universes. Recovery check
`01ada11f-4b9b-47f5-9e4f-720df5aa3e89` compiled all four relative modules with
zero diagnostics and inspected this exact declaration as Prop-valued. This
check and independent approval do not replace publication or prove the target.

The ambient multiplicity argument for Proposition 5.9 uses the opposite
Jacquet module of the irreducible quotient itself, not that of its whole
outer induction. Finite-length head semisimplicity, Schur/Hom multiplicity
identifications, quotient extraction and direct arbitrary-input continuation
remain proof obligations. First adjointness for maps into upper induction
does not alone provide the quotient-to-upper-induction reciprocity needed
here. Neither generic nor supported regular comparison may be applied to
arbitrary input by assuming the support one is trying to prove.

## Library statements reused by these families

These published proposition definitions, by other workers, are inputs to the
families above; the families should cite them rather than restate them.

- `Langlands.CuspidalSupport.PadicCuspidalInductionTheorems`
  (`Langlands.Representation.CuspidalSupport.NormalizedCuspidalInductionStatement`):
  Bernstein–Zelevinsky 1977, 2.5 (embedding into cuspidal induction), 2.8
  (length at most `r!`) and 2.9 (association and the Hom bound).
- `Langlands.CuspidalSupport.PadicLeviQuasicuspidalStructureTheorems`
  (`Langlands.Representation.CuspidalSupport.QuasicuspidalStructureStatement`):
  Bernstein–Zelevinsky 1977, §2.4, on block Levis: subquotients of
  quasicuspidal representations, the quasicuspidal direct-summand splitting,
  irreducible cuspidal constituents as both subrepresentations and quotients,
  and contragredients.
- `Langlands.CuspidalSupport.PadicQuasicuspidalJacquetTheorems`, listed in the
  table above.
- `Langlands.Classification.IsIrreducibleQuotient`, `IsIrreducibleHead` and
  `IsIrreducibleSocle` (`Langlands.Representation.Classification.ConstituentRelations`).
  `IsIrreducibleHead` is the quotient-kernel relation used through
  `IsLanglandsHead` in the published S78 Thm 4.1(1) target.
- `Langlands.Parabolic.NormalizedJacquetStatement`,
  `NormalizedInductionStatement`, `OppositeDualityStatement`,
  `ExactnessReciprocityStatement`, `NormalizedCompatibilityStatement` and
  `AdmissibilityStatement` (`Langlands.Representation.Parabolic.*`): exactness,
  Frobenius reciprocity, admissibility, twists, central characters and the
  opposite-parabolic duality of the normalized functors.

Normalized transitivity along a block refinement is now stated by
`Langlands.Parabolic.NormalizedRefinementTransitivityStatement`
(`Langlands.Representation.Parabolic.RefinementTransitivityStatement`). Its
induction clause prescribes evaluation and its normalization-correct inverse;
its Jacquet clause sends the iterated class of a vector to its class modulo
the full composed radical. These are natural isomorphism targets over actual
functors, not supplied isomorphism fields. Their proofs remain open.

## Remaining construction needs

The current Library already has the block parabolics and their opposites
(`Langlands.Group.GL.Blocks`), the block modulus (`Langlands.Group.GL.BlockModulus`),
normalized induction and Jacquet modules, `normalizedAbsHom`
(`Langlands.Group.GL.NormalizedCharacter`), `realPowerTwist`,
`IsSquareIntegrableModCenter`, `IsEssentiallySquareIntegrableModCenter`,
`IsSupercuspidal`, composition series with matching Jordan–Hölder factors
(`Langlands.Representation.Filtration.ObjectDefinitions`), and per-constituent
multiplicities (`HasJordanHolderMultiplicity`, above).

Three previously missing interfaces are now in the pinned Library:

1. `Langlands.Representation.Exponents.Jacquet` provides
   `PadicField.TopologicalData.splitCentreJacquet`, `IsJacquetExponent`, and
   `IsRealPartOf`. The split-centre action uses
   `GeneralLinear.BlockShape.blockScalarLevi` from
   `Langlands.Group.GL.BlockIwahoriDefinitions`. An exponent has open kernel
   and a nonzero generalized eigenspace for one uniform power; its real part
   satisfies `|χ(a)| = ∏ |a_i|^(r_i)`.
2. `Langlands.Representation.Classification.Tempered` provides
   `IsTemperedModCenter` and `PadicField.TopologicalData.IsTempered`. The
   predicate requires admissibility, a unitary scalar central character and
   all smooth coefficient norms in `L^(2+ε)` modulo the centre for every
   `ε > 0`. The `GL_n` version quantifies over every Borel Haar measure on the
   actual central quotient, whose existence is proved. It is independent of
   the exponent criterion. `T.IsSquareIntegrable` is the analogous measure-free
   interface for square-integrability.
3. `Langlands.Representation.Classification.LanglandsData` provides
   `PadicField.TopologicalData.TemperedLanglandsDatum`: an ordered block shape,
   irreducible analytically tempered block representations, and real exponents
   satisfying `StrictAnti`. Its `standardModule` is the actual normalized
   product induction, and `IsLanglandsHead` asks for an irreducible head with
   a unique quotient kernel. Neither existence nor uniqueness is a datum
   field. `SquareIntegrableLanglandsDatum` has weakly ordered exponents and is
   a different object. The actual head and socle constructions are available
   in `Langlands.Representation.Classification.CanonicalConstituents`.

The published `Langlands.Representation.Exponents.UnitaryPart` constructs
`unitaryCentralPart ρ`, the actual algebraic sum of generalized character
subrepresentations indexed by norm-one characters of the full group center.
It supplies the least-containing-subrepresentation property, the scalar-unitary
case, preservation by intertwiners, restricted maps and equivalences, and
natural inclusions. It permits several central characters and extensions;
it does not require that the whole sum have one scalar central character.
This construction assumes no topology or finite length and does not identify
its result with a maximal tempered part. That comparison and the corresponding
discrete-series multiplicities are now stated in
`GLDiscreteSeriesJacquetMultiplicityStatement`, under its actual induction
hypotheses. The full-center versus split-center bridge for GL Levis, the
analytic tempered-factor interpretation and the multiplicity formulas remain
representation-theoretic proof obligations.

`Langlands.Representation.Exponents.NilpotenceIndex` constructs
`centralCharacterNilpotenceIndex ρ χ : ℕ∞`, the least common power killing the
whole generalized character component, with infinity if no such bound exists.
It proves monotonicity of bounds, the bound/index equivalence, zero and infinity
criteria, stabilization and invariance under actual equivariant equivalences.
No finite-length, finite-spectrum or analytic conclusion is assumed.

S79 pp.90–92 define dual exponents using nonzero opposite-unipotent-invariant
functionals in the full algebraic dual, with the transpose action and the
opposite positive half-modulus on the eigenvalue. The published
`Langlands.Representation.Exponents.DualJacquet` realizes this using the actual
normalized opposite Jacquet quotient. Its `splitCentreDualJacquetSourceEquiv`
identifies the full dual with opposite-radical-invariant source functionals;
`mem_dualJacquet_characterSpace_iff` preserves the same uniform power in the
source-functional equation. The normalized quotient action uses positive upper
half-modulus; the source-functional eigenvalue uses inverse upper half-modulus
times the character, with no character inversion or conjugation.
`IsDualJacquetExponent` requires a smooth character and a nonzero exponent-one
space. `dualJacquetExponentNilpotenceIndex` separately measures the least uniform
bound on the entire generalized component. In the source's finite setting this
is its `d(χ)`, not dimension or Jordan–Hölder multiplicity. The finite-spectrum,
finite-bound and actual class-comparison assertions are now published in
`GLDualJacquetExponentPrerequisitesStatement`; their proofs remain open.

`Langlands.Representation.Exponents.ParabolicPair` represents every conjugate
of a standard block pair by a block shape and an actual ambient group element.
Refinement is inclusion of the actual parabolics together with reverse inclusion
of the split components; strictness is properness of that subgroup pair. Its
`scalarInclusion` is constructed from subgroup inclusion and proved injective;
`CharacterExtends` is restriction along this actual map. No arbitrary character
comparison or algebraic-group conjugacy theorem is supplied as input.
`Langlands.Representation.Exponents.WeakCritical` transports the source action
by actual inner conjugation and proves its invariant-functional and same-power
comparison. Following S79 p.189, weak criticality requires
`d_Q(ψ) < d_P(χ)` for every proper finer pair and every extending unitary dual
exponent. Separately, weak minimality means nonempty unitary spectrum and no
unitary spectrum at any proper finer pair. Minimality implies criticality by
eliminating the forbidden finer witness; the converse is now stated in the
published support family above and remains a representation-theoretic proof
obligation.

The relative multiplicity/recovery families now have actual inner and composed
opposite Jacquet functors sharing one refined-Levi codomain. The geometry is
Worker 328's `Langlands.Representation.Parabolic.OppositeRefinementDefinitions`,
contribution `baf6b13a-0ec5-48dc-8ece-e454d63db6d7` version 1, independently
accepted and published at `a6c8885e0e4bfcf4ee6d5a4b9a84a6d195085302` with
integration receipt `1d452f3c45464b34aeaf208d4701c7f4`. Its actual inner lower
radical lies in the product Levi. Its full ambient lower radical is the
preimage of that inner radical under the outer opposite Levi projection, so
it includes the outer lower radical as well.

`Langlands.Representation.Parabolic.OppositeRefinementFunctors` supplies the
coinvariant carriers, surjective quotient maps, normalizer actions and
descended intertwiners. The normalized actions are
`T.normalizedRefinedOppositeJacquet B S` and
`T.normalizedComposedOppositeJacquet B S`. Both target the actual
`Geometric.refinedLevi F.Carrier B S`. They multiply the raw lower-radical
quotient action by the positive half of the corresponding full upper
character. The ambient character includes both the restricted outer character
and the inner character. This is the inverse-half normalization of the inverse
full upper character. The module proves representative formulas, smoothness,
and identity/composition laws for the bundled functors
`T.normalizedRefinedOppositeJacquetFunctor B S` and
`T.normalizedComposedOppositeJacquetFunctor B S`. Field and representation
universes are independent; rank zero uses an empty shape, and each present
block has positive size.

This construction is contribution `e4fc2023-de03-4637-8e0e-7ca78d74ccc6`
version 1, by Worker 19 with Workers 8 and 14, independently accepted and
published at `a4f4742431c7298bf38f4d4e6bc03a6cd7a33a18` with integration receipt
`84223cdb13764c2687f13cecec3ded77`. Both geometry and functor pairs in the pinned
Library match their frozen hashes. Their explicit characters have not been
identified with Haar conjugation scaling by these modules. They assert no
relative transitivity, multiplicity comparison or inducing-data recovery.

The [Lemma 5.3 scope audit](silberger-lemma53-scope.md), contribution
`e575b5df-8966-4fea-a9e7-bb7c9a08033f`, is independently reviewed and published
at `225a00380f8ef7b97eb15bda1157dee4ab8b2a03`, with integration receipt
`eeaa2ff73ec84df1a6231a4bcb6f9e73`.
It explains the constituent restriction and the fine twist
`-nu_0 + nu''|M`, with a GL₂ counterexample to the printed unrestricted
comparison. It is a source audit, not a Lean theorem or an author-issued
erratum. It does not contradict the Langlands quotient theorem or supply the
all-regular continuation argument in Lemma 5.6.

The actual refined/flattened coordinate equivalence is now published:
`Langlands.Geometric.flattenedLeviEquiv R B S` in
`Langlands.Representation.Geometric.FlattenedLevi`. It identifies
`(B.flatten S).Levi R` with the actual refined subgroup of `B.Levi R`, with
proved component, ambient embedding and continuous-equivalence laws, including
rank zero. Worker 125's contribution `f75012c9-3ab3-47ac-af97-e6a170537087`
version 1 is independently accepted and published at
`0a5d6fd964189579fc9244ddb23e3116fe8dd974`, with integration receipt
`dbf5176da36443ffa1a84704caadf8bd`. The relative statements use this constructed
map to transport actual representations and determinant twists; no arbitrary
Levi equivalence is a premise.

The canonical cosocle carrier also already exists. In
`Langlands.Representation.Classification.CanonicalConstituents`,
`Classification.headKernel` is the common kernel of irreducible surjections,
`Classification.head` is its actual quotient, and `Classification.toHead`
has proved surjectivity and kernel. Targets in the source universe suffice
for the radical interpretation because every maximal invariant subspace has
its actual quotient there. The existing `SmoothRep.headQuotient` gives the
smooth quotient. The separate construction task
`28c1a0f3-8772-4c94-9ce3-c353cb470e8f`, revision 2, must reuse this carrier,
prove general finite-length semisimplicity, radical comparison, semisimple
universal factorization and functoriality, and make any arbitrary-field
generalization compatible with existing consumers. Its contract is not a
proof of these facts. The existing conditional irreducible-head theorem does
not supply them for reducible heads.

Actual induction from a conjugate block parabolic, with its explicit
left-translation equivalence, remains construction task
`ccad01fb-b32b-4d19-a856-31e79c6ceae6`, now claimed by Worker 264. It supplies
an input to Corollary 6.2, not the semistandard Weyl-conjugacy conclusion.
The semistandard statement remains with Worker 19. Replacing the source
result by a tautological pullback of standard data would lose its content.

Relative transitivity and the proofs of constituent-restricted generic
comparison, supported all-regular comparison, detailed recovery and cosocle
multiplicity remain separate obligations. The three published relative
families and exact proof tasks are recorded above; cosocle publication is
pending and semistandard conjugacy is unstated. The maximal-cone statement
and its exact proof task are also recorded above; its proof and the final
regular-head exhaustion proof remain distinct.

The grouping of equal exponents into tempered blocks is now stated by
`Langlands.Classification.SquareIntegrableEqualExponentGrouping F T` in
`Langlands.Representation.Classification.TemperedBlockStatement`.
It groups maximal consecutive equal-exponent runs, identifies each new block
with the actual normalized product of the unitarily normalized old factors,
and identifies the resulting standard modules. It is a separate `GL_n`
classification target, not a consequence of the `StrictAnti` field and not a
proved grouping theorem. Worker 15's contribution
`2cc81cef-ee34-4c42-b6e0-f39b60a414e1` version 1, coauthored by Worker 19,
is independently accepted and published at
`2839e6bae86085a8a220122cf5eb434176a57d4c`.
The pinned Library now contains
`Langlands.Representation.Exponents.Chambers`: coordinate `centreHMap` and
`leviHMap`, partial-sum positive/closed root cones, and their pairing and
exponent-bound equivalences. The actual parabolic coordinate specialization is now stated in
`GLParabolicRootWeightConeStatement`. For scalar exponents `r_i` and block
sizes `n_i`, its residuals are `r_i - n_i t_(q i)`: each fiber has total zero
and every prefix has nonpositive sum. The strictly decreasing `t` are the
averaged determinant exponents on the unique coarsening. The statement also
includes the actual matrix subgroup containments. Its proof and the
proof of the representation-level maximal-exponent statement remain separate
obligations; the latter statement is described above.
The two published exponent criteria use inequalities directly.

The opposite-parabolic geometry is also published in
`Langlands.Group.GL.OppositeBlocks`: the actual common Levi projection,
section, radical, normalizer action and continuous projection. The
specialized opposite normalized induction is published in
`Langlands.Representation.Induction.OppositeParabolic`. It is Worker 15's
contribution `1b7cfaaa-9c23-4733-af99-824e647d47f2` version 1 for task
`280afebe-d672-451a-86fc-1111fe6f3a23`, accepted by independent review and
present in Library commit `916154eeb26478d9efb73f26a117f337c9a438a2`.

For a realization `T`, a block shape `B` and an actual complex representation
`σ` of `B.Levi F.Carrier`, `T.normalizedOppositeParabolicInduced B σ` acts by
right translation, `(g · f)(x) = f(x g)`
(`normalizedOppositeParabolicInduced_apply`). Its carrier is the covariant
functions `GL_n → V` for the actual lower parabolic `B.oppositeParabolic F.Carrier`, each
fixed by one open subgroup under right translation. Let `m(p)` be the image of
`p` under `B.oppositeLeviProjection F.Carrier` and let `δ_P = T.leviModulus B`
be the upper block modulus. Then `normalizedOppositeParabolicInduced_covariant`
states

```
f(p g) = sqrt(δ_P(m(p)))⁻¹ • σ(m(p))(f(g)).
```

The normalizing character is `T.oppositeParabolicHalfModulus B`. It is
`(T.leviHalfModulus B)⁻¹` inflated along the opposite projection, and
`isOpen_ker_oppositeParabolicHalfModulus` proves that its kernel is open.
`isSmooth_normalizedOppositeParabolicInduced` proves smoothness. The module
also provides:

- `normalizedOppositeParabolicInducedMap`, the induced maps of Levi
  intertwiners, with identity and composition laws;
- the functor `normalizedOppositeParabolicInductionFunctor` between the
  existing smooth categories;
- the canonical-realization aliases
  `PadicField.canonicalNormalizedOppositeParabolicInduced` and
  `PadicField.canonicalNormalizedOppositeParabolicInductionFunctor`;
- a compact-support variant.

The field and carrier universes are independent. The lower subgroup and the
common embedded Levi stay explicit; nothing is transported to an upper
parabolic. The module proves construction obligations only. It does not
identify its scalar with the Haar modulus of `P̄`, and it states no adjunction,
Weyl transport, support or summand result. The construction is a prerequisite
for the support/summand family, not an assumed induction isomorphism.

### Proof-source and formalization gaps retained

The paired criteria explain the `GL_n` specialization and chamber conversion;
these identifications are not Lean proofs. The square-integrability criterion
still needs Casselman's asymptotic coefficient results (Theorem 4.3.4 and
Corollary 4.4.5). The tempered statement uses K94's analytic convention and
W03's exponent theorem, with an explicitly derived bridge from the weak
`Ξ` inequality to `L^(2+ε)`. Its route uses W03's Cartan volume estimate
(I.1(5), p.241), coefficient asymptotics (Theorem I.4.1, p.245), and `Ξ`
estimates (Lemma II.1.1, p.251; Lemma II.1.5, p.252). These steps, including
the converse argument from coefficient integrability to exponent bounds,
remain unformalized. Neither the two published statements nor this note claims
to prove them. W03 records these analytic inputs in a published account of
Harish-Chandra's work; no independent reading of every transitive original
proof source is claimed. The older Casselman and Langlands preprints cited
by S78 remain distinct from the retained later editions described above.

### Block form of the exponent conditions (derived)

This subsection is derived here; no source states it in this form. Let `P` be
the upper block parabolic with block sizes `n_1, ..., n_k`, and write
`a = diag(a_1 I_(n_1), ..., a_k I_(n_k))` for the elements of the split centre
`A_P` of its Levi. For a character `χ` of `A_P` occurring in the normalized
Jacquet module, let `r = (r_1, ..., r_k)` be the real vector with
`|χ(a)| = |a_1|^(r_1) ⋯ |a_k|^(r_k)` for all such `a`, where `|·|` is the
normalized absolute value. These are exponents in **block-scalar
coordinates**. If instead `χ` is written as `|det_1|^(t_1) ⊗ ⋯ ⊗ |det_k|^(t_k)`
times a unitary character, then `r_i = n_i t_i`, and the sums below become
the weighted sums `n_1 t_1 + ⋯ + n_j t_j`.

The chamber `A_P^-` of C95 (`|α(a)| ≤ 1` for the simple roots `α` in the
unipotent radical, so that conjugation by `a` contracts it) is
`|a_1| ≤ |a_2| ≤ ⋯ ≤ |a_k|` for the upper parabolic. Writing
`S_j = r_1 + ⋯ + r_j`:

- `|χ(a)| ≤ 1` for all `a ∈ A_P^-` holds exactly when `S_j ≥ 0` for every `j`
  and `S_k = 0`. Here `S_k = 0` comes from the central elements, which lie in
  `A_P^-` together with their inverses.
- Suppose `S_k = 0`, so that `|χ|` is trivial on the split centre `A_G` of
  `GL_n` and is defined on the quotient `A_P^- / A_P(O) A_G`, as C95 writes
  it. Then `|χ(a)| < 1` for every nontrivial class, that is, outside C95's
  removed compact and central directions, holds exactly when `S_j > 0` for
  every `j < k`. For `k = 1` (`P = G`) there is no nontrivial class and the
  condition is vacuous.

C95 Theorem 4.4.6 is a square-integrability criterion only: for an admissible
`ω`-representation, square-integrability modulo the centre is equivalent to
(a) `ω` unitary and (b) the strict inequality for every standard parabolic
and every central character of the Jacquet module, after the minimal-modulus
identification above. In block form, (a) is `S_k = 0` and (b) is `S_j > 0`
for `j < k`. C95 Theorem 4.4.6 does not contain a tempered criterion.

The weak condition for every standard parabolic is the block form of the
tempered criterion of S78 §3, p.98, which cites S79 Lemma 4.5.3,
pp.185–186. S79 states that lemma for the exponents of constant terms of
functions in its space `A(G)`. The chamber convention of S78 differs from the
one above:

- S78 p.96 defines `A^+` by `⟨α, H(a)⟩ ≥ 0` for the simple roots `α` of
  `(P, A)`. Since `⟨χ, H(m)⟩ = log_q |χ(m)|` (S79 §0.4, pp.7–8), this means
  `|α(a)| ≥ 1`. For the upper parabolic this is `|a_1| ≥ ⋯ ≥ |a_k|`, the
  elements that contract the opposite radical `N̄`.
- S78 p.97 takes exponents from the Jacquet module of the opposite parabolic
  `P̄`, normalized by `δ_P^(1/2) = δ_(P̄)^(-1/2)`.

S78 therefore tests the normalized Jacquet module of `P̄` on the chamber that
contracts the radical of `P̄`. That is the convention above, applied to `P̄`.
For `GL_n`, a block-reversing permutation matrix conjugates `P̄` to the upper
parabolic with block sizes `n_k, ..., n_1`. It transports the Jacquet module
and the chamber. So S78's condition over all standard `P` is equivalent to the
weak condition on `A_P^-` for the upper Jacquet modules over all standard
`P`.

Example: with the Library's upper-parabolic `δ_P^(-1/2)` normalization, the
Steinberg representation of `GL_2` has `r = (1/2, -1/2)` along the upper Borel
subgroup, so `S_1 = 1/2 > 0` and `S_2 = 0`.
