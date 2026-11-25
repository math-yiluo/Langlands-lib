# Jacquet exponents and Langlands quotients: source map

The relative generic, regular, recovery and cosocle statements, the
conjugate-induction and general cosocle constructions, the semistandard
statement and the dominance-corrected maximal-cone selection statement are in
the Library. The proofs that the Library has of the statement families are
listed in [Proofs in the Library](#proofs-in-the-library); the proof-status
sentences below have been checked against the Library. The scope audit of S78
Lemma 5.3 remains applicable. Declaration names refer to the Library; where a
commit is named, it is the Library commit where the declaration first appeared.

The 42 primary Lean/Markdown pairs cited here, including the general cosocle
construction, were compared with the versions that first entered the Library.
All 42 Lean files were unchanged. The superseded maximal-cone version is
recorded separately and is not counted. Four paired Markdown
files have later documentation changes: `TemperedExponentStatement`
corrects the Waldspurger I.4.1 page to 245; `DiscreteSeriesJacquetStatement`
and `TemperedInductionStatement` link the published support family;
`RelativeCosocleMultiplicityStatement` links the proved general cosocle
construction. The remaining 38 Markdown files were unchanged. These checks
establish file identity and documented changes, not the truth of unproved
proposition definitions.

This note maps the original theorems behind Silberger's Langlands quotient
theorem for `GL_n` to the Lean proposition definitions that state them, and
lists the constructions needed for the families.
The theorem families are proposition definitions (`def` returning `Prop`);
none of those families is proved here. The construction section also names
actual definitions and their intrinsic compatibility lemmas. This note proves
nothing.

The [Silberger reading note](../henniart/silberger.md) gives the
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
| K03 | T. Konno, *A note on the Langlands classification and irreducibility of induced representations of p-adic groups*, Kyushu J. Math. 57 (2003), 383–409. Central-Library file `Konno--A note on the Langlands classification and irreducibility of induced representations of p-adic groups--2003.pdf`; SHA256 `71931493382f2c8aa60734e27328db9a0f39c3af0b9c47bf746adcfa47fc0b42`. | `konno-2003-langlands-classification` |

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

For the new maximal-cone investigation, K03's introduction and pp.394–397
were read from the retained text; p.396 was checked visually. Lemma 3.4 and
Theorem 3.5(i) use dominance maximality of the positive part. The latter
chooses a subrepresentation of a weak character component of the opposite
Jacquet module. A whole-module quotient variant therefore needs an explicit
derived argument. K03's introduction also says S78 Lemma 5.3 is false; that
observation is separate from the new maximal-cone report. No reading of the
whole K03 article or verification of its entire proof is claimed here.

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
  `Langlands.GLBlockModulusHaarStatement` is proved by
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

The upper Haar comparison `glBlockModulusHaar` first appeared in the Library
at commit `9488f8128fc175e4f17b08d2a86eac54056fa753`. Its closing theorem has
exactly the statement as its type and covers every block shape. It does not
itself supply the opposite or relative refinement Haar comparisons.

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
| **Discrete-series support and tempered Jacquet summands.** S79 Cor. 4.5.11, pp.189–190, and Thm 4.5.18, p.193. | `GLTemperedDiscreteSeriesPrerequisitesStatement` in `Langlands.Representation.Classification.TemperedSupportStatement` states support and the both-inductions summand clause; the Jacquet quotient equivalence is stated separately in the preceding row. The support clause embeds an irreducible tempered representation into normalized opposite induction from discrete-series Levi data. The summand clause retains discrete-series input and equates its subquotient occurrence in the actual opposite normalized Jacquet module with complete reducibility of both opposite normalized inductions and occurrence of the original representation as a direct summand of each. These are proposition definitions; the Library proves the support clause (`GLTemperedDiscreteSeriesSupportStatement`, see below) and this note records no proof of the summand clause or of the whole family. Cor. 4.5.11's prescribed weakly critical-exponent refinement is stated separately; see the status below. |
| **Cuspidal Jacquet multiplicities.** S78 §2, pp.97–98; S79 Thm 5.4.1.1, pp.287–288, Thm 3.3.1, pp.126–127, §5.4.4, pp.307–311. For discrete-series data the quoted result covers only the maximal tempered summand. | The quasicuspidal case is stated for `GL_n`: `PadicQuasicuspidalJacquetTheorems` in `Langlands.Representation.CuspidalSupport.JacquetInductionStatement` (Bernstein–Zelevinsky 1977, Cor. 2.13; its `AssociatedJacquetFiltrationTheorem` gives a filtration of the normalized Jacquet module of quasicuspidal induction with one Weyl-transported quotient per minimal conjugating permutation). This is the `GL_n` counterpart of S79 Thm 5.4.1.1. Published: `GLCuspidalJacquetMultiplicityPrerequisitesStatement` in `Langlands.Representation.Classification.CuspidalJacquetMultiplicityStatement`. For irreducible cuspidal input and associated standard positive-rank Levis, it gives the full upper and opposite normalized Jacquet composition lengths and each constituent's exact `HasJordanHolderMultiplicity`, counted by the actual minimal conjugating permutations and their representation-equivalence subtype. It assumes neither finite length nor a decomposition. The non-cuspidal discrete-series formula applies to the unitary central part and is now stated separately in the following row. |
| **Discrete-series Jacquet multiplicities.** S79 Thm 5.4.1.1, pp.287–288, and §5.4.4, pp.307–311; weak-exponent comparison on p.187; C95 Prop. 2.1.9, p.21. | Published: `GLDiscreteSeriesJacquetMultiplicityStatement` in `Langlands.Representation.Classification.DiscreteSeriesMultiplicityStatement`. For associated standard positive-rank GL Levis and irreducible square-integrable input, the actual unitary central parts of both normalized Jacquet modules of upper induction are admissible, have the Weyl-count lengths and exact constituent multiplicities, and contain exactly the invariant subspaces with finite tempered composition factors. It neither bounds the full Jacquet length nor imposes one scalar central character on the tempered sum. The identification with tempered composition factors is stated; its full-center/split-center and analytic justifications are documented as derived steps. The representation-theoretic proofs remain open. |
| **Full-dual exponents and class comparison.** S79 §2.4, pp.90–92; Lemmas 3.2.1–3.2.2, Thm 3.2.4 and Cor. 3.2.5(1), pp.120–123; Lemma 4.5.6 and Cor. 4.5.7, pp.187–188. | Published: `GLDualJacquetExponentPrerequisitesStatement` in `Langlands.Representation.Exponents.DualJacquetStatement`. For irreducible admissible positive-rank GL_n sources, its four components state finite smooth dual spectrum, finite uniform nilpotence indices and spanning of the full dual; dual occurrence iff an actual irreducible admissible opposite Jacquet constituent has the prescribed scalar split-center character; analytic temperedness of such a constituent iff that character is unitary for a tempered source; and tempered opposite-inducing support retaining a prescribed unitary character. The arbitrary constituent carrier has its own universe. These statements use the published full transpose dual construction, not the inverse-element contragredient, and do not prove the comparisons. |
| **Weak-critical predicates and support refinement.** S79 §0.3, pp.5–6, and the paragraph before Cor. 4.5.11 through Cor. 4.5.12(3), pp.189–190. | Published constructions: `Exponents.ConjugateBlockPair` and its actual scalar restriction in `Langlands.Representation.Exponents.ParabolicPair`, and `PadicField.TopologicalData.IsWeaklyCriticalDualJacquetExponent`, `IsWeaklyCriticalDualJacquetPair`, `IsWeaklyMinimalDualJacquetPair` in `Langlands.Representation.Exponents.WeakCritical`. Weak criticality requires an occurring unitary exponent and tests strict uniform-index decrease over every proper finer concrete conjugate pair and every extending unitary exponent. Minimality is separately defined; its intrinsic implication to criticality is proved. The converse and prescribed discrete-series support are published proposition definitions in `GLWeaklyCriticalTemperedRefinementStatement`, described below; their proofs remain open. |
| **Multiplicity comparison.** S78 Prop. 5.1, p.99, Lemmas 5.2–5.6, pp.99–101: generic parameters first, then every regular positive one. | The unique-head conclusion of Prop. 5.1 is included in the published regular family below. Lemma 5.2's type-A genericity is now stated as `GLRelativeGenericParameterStatement` in `Langlands.Representation.Classification.RelativeGenericityStatement`: for nested standard block partitions and every real fine-block vector `v₀`, the actual regular coarse parameters whose fine-Weyl stabilizers of `v₀ − t` lie in the coarse Levi Weyl group form an open dense set. This linear-algebraic specialization imposes no representation hypotheses. The representation-theoretic generic family is published as `GLRelativeGenericComparisonStatement` in `Langlands.Representation.Classification.RelativeJacquetMultiplicityStatement`: actual inner constituents have equal inner/ambient opposite-Jacquet multiplicities, with positivity equivalent to an inner quotient, and actual generic inner quotients induce representations with kernel-unique irreducible heads. The [scope audit](silberger-lemma53-scope.md) gives a GL₂ obstruction to unrestricted Lemma 5.3; this derived target keeps the constituent restriction and documents why its generic summation argument permits arbitrary fine real vectors. `GLRelativeRegularComparisonStatement` in `Langlands.Representation.Classification.RelativeRegularComparisonStatement` is also published: the p.99 positive-root and intermediate discrete-series support data give positive equal multiplicities and a strong head for every strictly decreasing coarse parameter. The continuation and tempered-exponent cone argument remain proof obligations. |
| **Recovery of inducing data.** S78 Props. 5.7–5.9, pp.101–102, Prop. 6.1 and Cor. 6.2, pp.102–103. | Published: `GLRegularLanglandsDataUniquenessStatement` in `Langlands.Representation.Classification.RegularLanglandsStatement` states the ordered block form of Prop. 6.1: isomorphic arbitrary irreducible quotients recover the order, ranks, real exponents and tempered blocks after rank transport. The published `GLRegularLanglandsTensorRecoveryStatement` in `Langlands.Representation.Classification.RegularLanglandsTensorRecoveryStatement` isolates the fixed-shape, fixed-exponent consequence: isomorphic arbitrary irreducible quotients recover equivalence of the actual untwisted tensors of irreducible analytically tempered blocks. It is derived from Prop. 6.1, whose concluding route uses Prop. 5.8 and then Prop. 5.7; it is not unrestricted Prop. 5.7. Published: `GLRelativeRecoveryStatement` in `Langlands.Representation.Classification.RelativeRecoveryStatement` conjoins supported recovery (Prop. 5.7, whose competing inner quotient need not be tempered) and arbitrary-tempered quotient reflection (Prop. 5.8, with no support premise on the coarse input). Both use actual outer quotient maps. `GLRelativeCosocleMultiplicityStatement` is stated; its first commit, proof and actual head carriers are detailed below. Semistandard conjugacy (Cor. 6.2) is stated separately as `GLSemistandardLanglandsConjugacyStatement` in `Langlands.Representation.Classification.SemistandardLanglandsStatement`; its first commit and proof are recorded below. |
| **Exhaustion.** S78 Prop. 7.2, pp.103–104. | Published: `GLRegularLanglandsExhaustionStatement` in `Langlands.Representation.Classification.RegularLanglandsStatement`: every irreducible admissible smooth positive-rank `GL_n` representation is the head of a regular tempered standard module. The intermediate `GLMaximalConeJacquetQuotientStatement` in `Langlands.Representation.Classification.MaximalConeStatement` uses dominance of positive parts instead of the false maximum-block-count clause of an earlier version. Its proof keeps the unrestricted competitor class and the whole opposite-Jacquet quotient conclusion. The final exhaustion target is unchanged, and its separate proof route is independent of this intermediate. |
| **Regular-chamber quotient theorem.** S78 Thm 4.1(1)–(3), p.99, proof §§5–7. | Published: `GLRegularLanglandsQuotientStatement` in `Langlands.Representation.Classification.RegularLanglandsStatement`, the conjunction of unique-head existence, ordered inducing-data uniqueness and exhaustion. The actual upper standard module uses irreducible analytically tempered blocks with strictly decreasing real determinant exponents. All central twists are allowed; one-block regularity is vacuous. Head existence and equality of irreducible quotient kernels are conclusions, not datum fields. |

The two exponent-criterion pairs (square-integrability and temperedness)
first appeared in the Library at commit
`9a0767626050f3346ad5f25e37cef39f38a5c0dc`; downstream Lean files import the
declarations by name. The tempered-induction statement first appeared at
`8b1acb7e020811a7961329d198d300fc9f01e5fa`; its paired Markdown documents the
analytic bridge on both `GL_n` and its actual product Levi, with a proved
Haar-existence helper for the Levi central quotient. The discrete-series
Jacquet statement first appeared at `e3c2fa98be720f63c6981efbbdf15cd223329e76`,
the regular quotient statement at `2f8d1873fbaeb581719bc35dbf6f5c9f2d4a8df4`,
the support/summand statement at `6c3030e24467888afeb3d4e60546c2301ce4f38d` and
the actual parabolic-cone statement at
`67dfb8a24d65657a6bf35da262b1009383d873d5`. The cuspidal multiplicity and
relative genericity statements, and the algebraic construction
`Langlands.Representation.Exponents.UnitaryPart`, first appeared at
`f1b212cc117b9c34dced95c0ac88e6328827334d`; the uniform nilpotence
construction and the discrete-series multiplicity statement at
`aee7fdb7f6d4283cce4db9035fd9478c923d4926`; the full-dual construction at
`9ff0d4f8edaf10dd32d87468c3045da6ec3ee5c6`; the concrete parabolic pairs at
`ac106a0cb63f5fca8c452213147e8926dd2575af`; the dual comparison statements and
the weak-critical construction at `b263cfa454b11d485198ae46d8290f32435e48c6`.
Being in the Library does not make a proposition family proved. The
construction modules include their intrinsic algebraic and coordinate laws only.

The support family first appeared in the Library at commit
`a6c8885e0e4bfcf4ee6d5a4b9a84a6d195085302`. Its entry is
`Langlands.GLWeaklyCriticalTemperedRefinementStatement` in
`Langlands.Representation.Exponents.WeakCriticalStatement`. For an irreducible
analytically tempered source it states existence of a standard pair minimal
among all concrete conjugate pairs, discrete-series opposite-inducing support with a prescribed critical character, and criticality
iff minimality for all such pairs. The source route uses Cor. 4.5.11 to supply
the discrete-series class-exponent premise of Cor. 4.5.12(3). This is the
proposition family, not its proof; this note records no proof of
`GLWeaklyCriticalTemperedRefinementStatement`.

## Proofs in the Library

The Library proves the following statements named in this note (proof
modules under `Langlands/Representation/` unless another path is given):
`GLAdmissibleFiniteLengthStatement` (`glAdmissibleFiniteLength`,
`Classification/FiniteLengthProof`), `GLBlockModulusHaarStatement`
(`glBlockModulusHaar`, `Langlands/Group/GL/BlockModulusHaarProof`),
`GLCuspidalJacquetMultiplicityPrerequisitesStatement`
(`Classification/CuspidalJacquetMultiplicityProof`),
`GLSquareIntegrableExponentCriterionStatement`
(`Classification/SquareIntegrableExponentProof`),
`GLTemperedExponentCriterionStatement` (`Classification/TemperedExponentProof`),
`GLTemperedUnitarityStatement` and `GLTemperedInductionStatement`
(`Classification/TemperedUnitarityProof`, `Classification/TemperedInductionProof`),
`GLTemperedDiscreteSeriesSupportStatement` (`Classification/TemperedSupportProof`),
`GLWeaklyMinimalStandardPairExistenceStatement`
(`Exponents/WeakMinimalExistenceProof`),
`GLWeaklyCriticalDiscreteSeriesSupportStatement`
(`Exponents/WeakCriticalSupportProof`),
`GLParabolicRootWeightConeStatement` (`Classification/ParabolicConeProof`),
`GLMaximalConeJacquetQuotientStatement` (`Classification/MaximalConeProof`),
`GLRegularLanglandsDataUniquenessStatement`,
`GLRegularLanglandsTensorRecoveryStatement` and
`GLRegularLanglandsExhaustionStatement` (the corresponding
`Classification/RegularLanglands…Proof` modules),
`GLRelativeGenericComparisonStatement`, `GLRelativeRegularComparisonStatement`,
`GLRelativeRecoveryStatement`, `GLSupportedRelativeRecoveryStatement`,
`GLTemperedRelativeQuotientReflectionStatement` and
`GLRelativeCosocleMultiplicityStatement` (the corresponding `Classification/…Proof`
modules), `GLSemistandardLanglandsConjugacyStatement`
(`Classification/SemistandardLanglandsProof`), and the prerequisites
`GLOppositeProductReversalStatement`, `Classification.HeadQuotientCriterionStatement`,
`CentralOperatorExpansionStatement`, `Parabolic.FlattenedJacquetQuotientStatement`,
`GLDiscreteSeriesPositiveRootSupportStatement`,
`Parabolic.NormalizedRefinedOppositeJacquetExactnessStatement`,
`GLTemperedJointSupportStatement`,
`Parabolic.NormalizedOppositeRefinementTransitivityStatement`,
`JordanHolderMultiplicityIndependenceStatement` and the equal-exponent
grouping `Classification.SquareIntegrableEqualExponentGrouping`.

This note records no proof of `GLRegularLanglandsQuotientStatement` (the
conjunction), `CentralExponentPrerequisitesStatement`,
`GLFixedCentralCharacterSplittingStatement`,
`GLSquareIntegrabilityPrerequisitesStatement`,
`RootWeightConeDecompositionStatement`,
`GLDiscreteSeriesJacquetPrerequisitesStatement`,
`GLTemperedInductionPrerequisitesStatement` (as a conjunction),
`GLTemperedDiscreteSeriesPrerequisitesStatement`,
`GLDiscreteSeriesJacquetMultiplicityStatement`,
`GLDualJacquetExponentPrerequisitesStatement`,
`GLWeaklyCriticalTemperedRefinementStatement`,
`GLRelativeGenericParameterStatement`, `PadicQuasicuspidalJacquetTheorems`
or `Parabolic.NormalizedRefinementTransitivityStatement`.

## Tempered-support proof dependencies

The proof of `GLTemperedDiscreteSeriesSupportStatement` follows a source
route that separates minimal standard-pair existence from prescribed
critical-character discrete-series support. The intrinsic minimal-to-critical
implication is already proved in `WeakCritical`; prescribed critical support
then supplies ordinary support. Prescribed unitary tempered support and
class-exponent comparison in `DualJacquetStatement` are upstream proof
obligations, together with the analytic exponent criteria.

The converse from criticality to minimality uses the discrete-series support
conclusion of S79 Corollary 4.5.11 in Corollary 4.5.12(3). It must not be used
as an upstream assumption to prove that same support theorem. Consequently
the aggregate `GLWeaklyCriticalTemperedRefinementStatement` is not an atomic
proof prerequisite for ordinary support. Regular Langlands exhaustion,
equal-exponent grouping and tempered-block exhaustion are downstream and may
not be used to prove this support statement.

The route splits into two statements, both proved in the Library:

- `Langlands.GLWeaklyMinimalStandardPairExistenceStatement.{uF,uV}`
  (`glWeaklyMinimalStandardPairExistence`);
- `Langlands.GLWeaklyCriticalDiscreteSeriesSupportStatement.{uF,uV}`
  (`glWeaklyCriticalDiscreteSeriesSupport`).

Both preserve analytic temperedness, original-carrier universes and all
concrete finer pairs. The prescribed-support target additionally keeps the
specified exponent, actual Jacquet class occurrence, scalar character,
all-Haar full-center square-integrability and opposite-induction embedding.
Neither may use the aggregate/converse or the downstream classification;
the converse lies downstream. The precise dual-Jacquet and weak
constant-term prerequisites belong to these two proofs.

## Tensor recovery, real Levi twists and maximal-cone status

The fixed-parameter tensor recovery statement and the actual real Levi
character and twist construction are in the Library; both were checked
unchanged between Library commit `4750a03e101b9ad45fc1a4d90a6a3d02d69c73e9`
and the coverage update of this note.

The tensor recovery target keeps independent field and carrier universes,
positive total rank, a fixed ordered shape and `StrictAnti` exponent, actual
analytic temperedness of every irreducible factor, and weak irreducible
quotient premises. The quotient targets may differ and are related by an
actual smooth isomorphism. Its conclusion is equivalence of the untwisted
product-Levi tensors. It assumes no head or canonical quotient. Its proof
must not assume full inducing-data uniqueness; the Library proves it as
`glRegularLanglandsTensorRecovery`. The helper
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

### Dominance correction and proof boundary

An earlier version of the maximal-cone statement, which first appeared at
Library commit `2da3640f8f3978d2ba6ce703d6c26cf1941ba234`, had a
maximum-block-count clause. The corrected version replaces it and first
appeared at `3e255196ad168b37f73124db5bdb4d6a5168a4da`. The
[corrected paired explanation](../../Langlands/Representation/Classification/MaximalConeStatement.md)
records the source argument and independently checked obstruction.

`GLBlockPositivePartStrictlyDominates C₁ t₁ C₂ t₂` compares the rank-length
vectors obtained by repeating each determinant exponent by its block size.
It requires equal totals, every prefix sum for the first vector at least the
second, and one strictly larger prefix. The selected positive part has no
strictly dominating competitor. Competitors still range over every actual
dual exponent on every standard shape, every real part and every numerical
cone coarsening; no quotient or temperedness premise is added to them.
Character restriction remains pointwise composition with the consecutive
grouping map. The conclusion retains an irreducible admissible quotient of
the **whole** normalized opposite Jacquet module. Its negative determinant
twist is analytically tempered for every Borel Haar measure on the full Levi
central quotient. Arbitrary ambient central twists and independent `uF` and
`uV` remain in scope.

The obstruction uses `A = 1_GL₂ × 1_GL₂`. The opposite Borel
scalar exponent vectors in the correction are
`(1/2,-1/2,1/2,-1/2)` and `(1/2,1/2,-1/2,-1/2)`.
The check recorded in this note was limited to exact rational enumeration of the
numerical cone clauses on those vectors: maximum block count selects
`C=(1,2,1)`, `t=(1/2,0,-1/2)`, with polygon
`(0,1/2,1/2,1/2,0)`, strictly dominated by the polygon
`(0,1/2,1,1/2,0)` of `C=(2,2)`, `t=(1/2,-1/2)`.
The representation-theoretic verification is in the corrected Markdown;
this note does not claim a separate original-source verification of that part.

The corrected Markdown derives full-spectrum selection and extraction of a
whole-module quotient using the annihilator of the Levi orbit of a dual
eigenfunctional. It identifies these as extensions of K03's narrower
subrepresentation route. First adjointness turns the whole opposite-Jacquet
quotient into an embedding in opposite normalized induction. A strong head
of upper normalized induction still needs a correctly oriented separate
bridge; K03 p.396 instead uses a subrepresentation followed by duality.
Finer Jacquet exactness, transitivity, the dominance argument and the analytic
temperedness bridge are the parts of its proof; the Library proves the
corrected statement as `glMaximalConeJacquetQuotient`. The latter uses S79
Theorem 4.5.1 and definition, pp.183–184, Lemma 4.5.3, pp.185–186, and W03
I.1(5), p.241, II.1.1, p.251, and III.2/III.2.2, pp.265–266.

Its proof names the unchanged declaration with its corrected semantics and
must not use the final Langlands exhaustion.

The route to regular exhaustion recorded here uses square-integrable
exhaustion and equal-exponent grouping, independently of maximal-cone
selection; its strong upper-head target is unchanged. The alternate Jacquet
route needs regular exponents, the whole-module quotient, scalar character
and analytic temperedness, but no maximality conclusion. The correction does
not establish those separate exhaustion prerequisites. The Library proves
`GLRegularLanglandsExhaustionStatement` as `glRegularLanglandsExhaustion`;
this note does not record which route that proof takes.

## Additional prerequisites

The following prerequisite statements are in the Library; they are not
proofs of the relative comparison or recovery families. Module links give the
full scope and provenance; the table records the Library commit where each
first appeared. The Library proves all seven (see
[Proofs in the Library](#proofs-in-the-library)).

| Declaration and scope | First in the Library at commit |
| --- | --- |
| [`GLOppositeProductReversalStatement`](../../Langlands/Representation/Induction/OppositeProductReversalStatement.md): actual opposite induction of a smooth block tensor is equivalent to upper induction of the reversed tensor, with both function maps specified; includes rank zero and reducible inputs. | `ec55903e24f28e3dc27f6ba202ff0af22883c525` |
| [`Classification.HeadQuotientCriterionStatement`](../../Langlands/Representation/Classification/HeadQuotientCriterionStatement.md): a strong head is equivalent to existence of an irreducible quotient and absence of a quotient onto a product of two irreducibles, including repeated factors. It imposes no topology or finite-length premise. | `ec55903e24f28e3dc27f6ba202ff0af22883c525` |
| [`CentralOperatorExpansionStatement`](../../Langlands/Representation/Smooth/CentralOperatorExpansionStatement.md): admissibility and finite generation give a uniform finite expansion of actual central action operators by continuous functions with finite-dimensional translate spans. Those functions need not be characters. | `e9ecbfeda9579d84259f3a6c2f76fe0354602b13` |
| [`Parabolic.FlattenedJacquetQuotientStatement`](../../Langlands/Representation/Parabolic/FlattenedJacquetQuotientStatement.md): the prescribed upper flattened-to-iterated Jacquet linear quotient is equivariant and surjective with the actual normalized actions, in all ranks and without smoothness assumptions. It asserts no injectivity or full transitivity. | `84f5d5a32df09643d499627f7ca72504805d3365` |
| [`GLDiscreteSeriesPositiveRootSupportStatement`](../../Langlands/Representation/Classification/DiscreteSeriesPositiveRootSupportStatement.md): arbitrary irreducible analytic discrete-series product-Levi input has unitary cuspidal fine support with a strictly positive scalar-root expansion and an actual upper refined-induction surjection. It assumes no tensor presentation or support certificate. | `cc52f4db904e440c7ced6e759968a1c216438809` |
| [`Parabolic.NormalizedRefinedOppositeJacquetExactnessStatement`](../../Langlands/Representation/Parabolic/OppositeRefinementExactnessStatement.md): injection preservation into a smooth middle representation, algebraic right exactness, and the binary-product equivalence sending `[(u,v)]` to `([u],[v])`, with four independent universes and all ranks. | `3e255196ad168b37f73124db5bdb4d6a5168a4da` |
| [`GLTemperedJointSupportStatement`](../../Langlands/Representation/Classification/TemperedJointSupportStatement.md): arbitrary irreducible analytically tempered product-Levi input has compatible fine cuspidal and middle discrete-series support, a positive scalar-root expansion, literal flatten equality and three actual upper-induction surjections. Support is a conclusion. | `3e255196ad168b37f73124db5bdb4d6a5168a4da` |

The proof of joint support retains independent field and input-carrier
universes, with existential support carriers in `Type (max uF uV)`. It must
reuse the fine-support, tempered opposite-support and analytic induction
branches; it does not permit downstream classification as an assumption.

The Library proves the exactness statement as
`normalizedRefinedOppositeJacquetExactness`
(`Parabolic/OppositeRefinementExactnessProof`). It supplies no multiplicity,
transitivity or recovery conclusion.

Two further prerequisites, proved or constructed, first appeared in the
Library at commit `cc52f4db904e440c7ced6e759968a1c216438809`:

- [`jordanHolderMultiplicityIndependence`](../../Langlands/Representation/Filtration/MultiplicityIndependenceProof.md). It proves independence of factor counts for supplied composition series and uniqueness of multiplicity. It does not construct a series or prove additivity or recovery.
- [`CuspidalSupport.leviCuspidalConstituentMaps`](../../Langlands/Representation/CuspidalSupport/ConstituentUniverse.md). It produces actual embedding and quotient maps across independent carrier universes from occurrence as a quotient of an invariant subspace. The ambient representation is arbitrary admissible input; only the irreducible constituent is cuspidal. It assumes no fixed central character and asserts no splitting, Jacquet multiplicity, reciprocity or head theorem.

The proof of the strict exponent criterion
`GLSquareIntegrableExponentCriterionStatement` does not restrict to
irreducible representations (the Library proves it as
`glSquareIntegrableExponentCriterion`). It retains the arbitrary nontrivial admissible
carrier, supplied scalar character, separate unitarity condition, strict
chamber bound off compact and central directions, independent universes and
all Haar measures. The local-invariance and analytic asymptotic bridges
are parts of that proof, independent of downstream classification.

Two narrower interfaces are needed: admissibility, finite length and an
actual composition series for normalized refined induction of arbitrary
irreducible cuspidal fine-Levi input; and evaluation-at-identity
surjectivity and nontriviality for smooth refined-induction input, with no
admissibility, irreducibility or cuspidality premise. Both retain all ranks
and independent universes. Neither is a replacement for the generic
multiplicity comparison. This note does not record whether the Library
states them.

The summand route needs the same-sigma opposite-to-upper discrete-series
induction interface: an
irreducible tempered representation embedding in opposite induction from a
given discrete-series `σ` yields opposite induced semisimplicity and an
embedding in upper induction from that **same** `σ`. Upper semisimplicity
is a separate interface. Conjugation that
transports `σ` and adjunctions with another map direction do not establish
this interface. Its source-backed proof must avoid assuming the summand theorem it serves
or the classification theorem; no full induction isomorphism is required.

## Relative comparison and recovery statements

The following statements first appeared in the Library at commit
`3f303847f99b2a44e2f0074b9cca983bab26eb3e`. The module prefix in the table is
`Langlands.Representation.Classification`.

| Module and exact aggregate |
| --- |
| `RelativeJacquetMultiplicityStatement`: `Langlands.GLRelativeGenericComparisonStatement` |
| `RelativeRegularComparisonStatement`: `Langlands.GLRelativeRegularComparisonStatement` |
| `RelativeRecoveryStatement`: `Langlands.GLRelativeRecoveryStatement` |

As statements they are not proofs; the Library proves all three
(`glRelativeGenericComparison`, `glRelativeRegularComparison`,
`glRelativeRecovery`), preserving all independent universes and the
hypotheses. The generic statement
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

The cosocle statement first appeared in the Library at commit
`40a7d025f604f74140054607638d2af422b581ce`. Its Lean file is unchanged since;
its paired Markdown later gained a link to the general cosocle construction,
which does not alter the statement. Its pair is
`Langlands/Representation/Classification/RelativeCosocleMultiplicityStatement`,
and its exact proposition is `Langlands.GLRelativeCosocleMultiplicityStatement`.
It states the Proposition 5.9 equality in the two existing canonical heads,
for arbitrary tempered coarse input and any actual regular-positive outer
irreducible quotient. There is no fine/middle support premise on the coarse
input and no fine-ambient quotient premise. One natural number, possibly zero,
is the Jordan–Hölder multiplicity on both sides; both finite series are
conclusions. The field, fine, middle, coarse and outer quotient carriers have
five independent universes. A compilation of all four relative modules gave
zero diagnostics and showed this exact declaration to be Prop-valued; that
check does not prove the target. The Library proves it as
`relativeCosocleMultiplicity` (`Classification/RelativeCosocleMultiplicityProof`).

The ambient multiplicity argument for Proposition 5.9 uses the opposite
Jacquet module of the irreducible quotient itself, not that of its whole
outer induction. General finite-length head semisimplicity is proved in the cosocle
construction below. Finite length of the particular inductions, Schur/Hom
multiplicity identifications, quotient extraction and direct arbitrary-input
continuation are the other parts of the proof. First adjointness for maps into upper induction
does not alone provide the quotient-to-upper-induction reciprocity needed
here. Neither generic nor supported regular comparison may be applied to
arbitrary input by assuming the support one is trying to prove.

## Library statements reused by these families

These proposition definitions of the Library are inputs to the
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
eliminating the forbidden finer witness; the converse is stated in the
support family above (`GLWeaklyCriticalTemperedRefinementStatement`), of which
this note records no proof.

The relative multiplicity/recovery families have actual inner and composed
opposite Jacquet functors sharing one refined-Levi codomain. The geometry is
`Langlands.Representation.Parabolic.OppositeRefinementDefinitions`, in the
Library since commit `a6c8885e0e4bfcf4ee6d5a4b9a84a6d195085302`. Its actual inner lower
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

This construction first appeared in the Library at commit
`a4f4742431c7298bf38f4d4e6bc03a6cd7a33a18`. Their explicit characters have not been
identified with Haar conjugation scaling by these modules. They assert no
relative transitivity, multiplicity comparison or inducing-data recovery.

The [Lemma 5.3 scope audit](silberger-lemma53-scope.md) explains the constituent restriction and the fine twist
`-nu_0 + nu''|M`, with a GL₂ counterexample to the printed unrestricted
comparison. It is a source audit, not a Lean theorem or an author-issued
erratum. It does not contradict the Langlands quotient theorem or supply the
all-regular continuation argument in Lemma 5.6.

The actual refined/flattened coordinate equivalence is in the Library:
`Langlands.Geometric.flattenedLeviEquiv R B S` in
`Langlands.Representation.Geometric.FlattenedLevi`. It identifies
`(B.flatten S).Levi R` with the actual refined subgroup of `B.Levi R`, with
proved component, ambient embedding and continuous-equivalence laws, including
rank zero. It first appeared at Library commit
`0a5d6fd964189579fc9244ddb23e3116fe8dd974`. The relative statements use this constructed
map to transport actual representations and determinant twists; no arbitrary
Levi equivalence is a premise.

The canonical cosocle carrier already exists in
`Langlands.Representation.Classification.CanonicalConstituents`:
`Classification.headKernel` is the common kernel of irreducible surjections,
`Classification.head` is its actual quotient, and `Classification.toHead`
has proved surjectivity and kernel.
`Langlands.Representation.Classification.Cosocle` proves that this same kernel
is the intersection of maximal subrepresentations and the group-algebra
Jacobson radical. It proves finite length and semisimplicity of the head
when the source has finite group-algebra length. `headLift` gives unique
factorization into every semisimple target without a finite-length hypothesis;
`headMap` gives functoriality for arbitrary intertwiners. The smooth versions
reuse the same quotient, generalized to arbitrary fields. No new head carrier
or assumption of irreducibility is introduced.

This construction first appeared in the Library at commit
`e985f888ec722340c194d6d8b80d4338feef4732`. It discharges the general
algebraic obligations of the head; it does not prove the finite-length hypotheses for the particular inductions
or any multiplicity comparison in Proposition 5.9.

Actual induction from a conjugate block parabolic is implemented in
`Langlands/Representation/Induction/ConjugateParabolic.lean` and the paired
Markdown, in the Library since commit
`99ec070e17d124b1ec3414dd2535cdfb94b5079b`. It constructs actual
conjugate Levi embeddings, projection and subgroup, normalized function-space
induction, and the left-translation equivalence with standard induction,
including smoothness and naturality. It supplies an input to Corollary 6.2;
it does not prove semistandard Weyl conjugacy.

The statement `GLSemistandardLanglandsConjugacyStatement` uses
actual split-component inclusion in the diagonal torus. Equivalent arbitrary
irreducible quotients of regular-positive semistandard and standard inductions
must recover the pairs under an actual permutation matrix, a continuous Levi
coordinate equivalence with its matrix embedding law, the real character and
the untwisted tempered representation. The whole-Levi inputs are analytically
tempered; no tensor presentation is assumed.

Its entry module is
`Langlands.Representation.Classification.SemistandardLanglandsStatement`, in
the Library since commit `123284c0f07314aa4544e028a94932bf9eb256af`; its Lean
and Markdown files then had SHA-256
`15536b747f44470be0da67417f56bff988d73bfdb736e309ec0ecd0404354dbc` and
`c0323c927f0b46a7a3c5e5f21cfd27e96f6d00ec663f26f408521f0307c848b9`. A
compilation returned zero diagnostics and showed the exact target to be a
`Prop` with five independent universes.

Its proof must preserve the complete target and independent universes;
semistandard standardization, transport, standard-data uniqueness,
representative replacement and parameter faithfulness are its substantive
parts. The Library proves it as `glSemistandardLanglandsConjugacy`
(`Classification/SemistandardLanglandsProof`).

Relative transitivity is a separate obligation (the Library proves
`Parabolic.NormalizedOppositeRefinementTransitivityStatement`; this note
records no proof of `Parabolic.NormalizedRefinementTransitivityStatement`).
The four relative families and their proofs are recorded above. The
maximal-cone selection proof and the final regular-head exhaustion proof are
distinct; the Library proves both.

The grouping of equal exponents into tempered blocks is stated by
`Langlands.Classification.SquareIntegrableEqualExponentGrouping F T` in
`Langlands.Representation.Classification.TemperedBlockStatement`.
It groups maximal consecutive equal-exponent runs, identifies each new block
with the actual normalized product of the unitarily normalized old factors,
and identifies the resulting standard modules. It is a separate `GL_n`
classification target, not a consequence of the `StrictAnti` field. It
first appeared at Library commit
`2839e6bae86085a8a220122cf5eb434176a57d4c`; the Library proves it as
`squareIntegrableEqualExponentGrouping`
(`Classification/SquareIntegrableEqualExponentGroupingProof`).
The Library contains
`Langlands.Representation.Exponents.Chambers`: coordinate `centreHMap` and
`leviHMap`, partial-sum positive/closed root cones, and their pairing and
exponent-bound equivalences. The actual parabolic coordinate specialization is stated in
`GLParabolicRootWeightConeStatement`. For scalar exponents `r_i` and block
sizes `n_i`, its residuals are `r_i - n_i t_(q i)`: each fiber has total zero
and every prefix has nonpositive sum. The strictly decreasing `t` are the
averaged determinant exponents on the unique coarsening. The statement also
includes the actual matrix subgroup containments. The Library proves it
(`glParabolicRootWeightCone`) and the representation-level maximal-exponent
statement described above (`glMaximalConeJacquetQuotient`).
The two published exponent criteria use inequalities directly.

The opposite-parabolic geometry is in
`Langlands.Group.GL.OppositeBlocks`: the actual common Levi projection,
section, radical, normalizer action and continuous projection. The
specialized opposite normalized induction is in
`Langlands.Representation.Induction.OppositeParabolic` (in the Library at
commit `916154eeb26478d9efb73f26a117f337c9a438a2`).

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
