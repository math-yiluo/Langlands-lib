# Jacquet exponents and Langlands quotients: source map

Author: Worker 19, task `616fab20-3cae-49ab-94f4-d28791b2b93f`.
Opposite-induction documentation contributed by Worker 264.
Source audit updated on 22 October 2026 against the Library commit
`cddb0412f1a617f8f0476ab118a15618a386cf2d`. This update records the published
support/summand and actual parabolic-cone families, with exact publication
receipts below. Declaration names refer to the Library tree containing this
note. Publication records identify earlier
commits where the indicated contributions entered the Library. Review approval
alone does not make an unpublished candidate a Library dependency.

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
From S79, the front matter and pp.1–9, p.25, pp.35–36, pp.119–129,
pp.177–194, pp.287–292 and pp.307–311 were read; this is not a reading of
the whole book. From C95, pp.13, 16–24, 27–29, 44–45 and 47–51 were read. From
L-UBC, the title page and pp.60–62 (Lemma 4.4 and its proof) were read. From
BZ77, only §1.2, p.443, was read for the multiplicity row below.
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
  comparison, which the module does not prove. Even the upper-radical version
  is only stated, as `Langlands.GLBlockModulusHaarStatement`. The Library's
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
| **Discrete-series support and tempered Jacquet summands.** S79 Cor. 4.5.11, pp.189–190, and Thm 4.5.18, p.193. | `GLTemperedDiscreteSeriesPrerequisitesStatement` in `Langlands.Representation.Classification.TemperedSupportStatement` states support and the both-inductions summand clause; the Jacquet quotient equivalence is stated separately in the preceding row. The support clause embeds an irreducible tempered representation into normalized opposite induction from discrete-series Levi data. The summand clause retains discrete-series input and equates its subquotient occurrence in the actual opposite normalized Jacquet module with complete reducibility of both opposite normalized inductions and occurrence of the original representation as a direct summand of each. These are proposition definitions with proofs still open. Cor. 4.5.11's weakly critical-exponent refinement remains unstated. |
| **Cuspidal Jacquet multiplicities.** S78 §2, pp.97–98; S79 Thm 5.4.1.1, pp.287–288, Thm 3.3.1, pp.126–127, §5.4.4, pp.307–311. For discrete-series data the quoted result covers only the maximal tempered summand. | The quasicuspidal case is stated for `GL_n`: `PadicQuasicuspidalJacquetTheorems` in `Langlands.Representation.CuspidalSupport.JacquetInductionStatement` (Bernstein–Zelevinsky 1977, Cor. 2.13; its `AssociatedJacquetFiltrationTheorem` gives a filtration of the normalized Jacquet module of quasicuspidal induction with one Weyl-transported quotient per minimal conjugating permutation). This is the `GL_n` counterpart of S79 Thm 5.4.1.1. Not yet stated: the multiplicity statements themselves (how many composition factors of the Jacquet module carry a given exponent or are equivalent to a given constituent, counted with `HasJordanHolderMultiplicity`), and the non-cuspidal case used for discrete-series data. |
| **Multiplicity comparison.** S78 Prop. 5.1, p.99, Lemmas 5.2–5.6, pp.99–101: generic parameters first, then every regular positive one. | The unique-head conclusion of Prop. 5.1 is included in the published regular family below. The finer multiplicity comparisons of Lemmas 5.3 and 5.6 are not yet stated. They need exponents, standard parabolic chains, Jacquet transitivity and tempered bounds; the counts are `HasJordanHolderMultiplicity`. Genericity must not replace regularity in the final statement. |
| **Recovery of inducing data.** S78 Props. 5.7–5.9, pp.101–102, Prop. 6.1 and Cor. 6.2, pp.102–103. | Published: `GLRegularLanglandsDataUniquenessStatement` in `Langlands.Representation.Classification.RegularLanglandsStatement` states the ordered block form of Prop. 6.1: isomorphic arbitrary irreducible quotients recover the order, ranks, real exponents and tempered blocks after rank transport. The relative recovery and cosocle multiplicities of Props. 5.7–5.9 and semistandard conjugacy of Cor. 6.2 remain unstated. |
| **Exhaustion.** S78 Prop. 7.2, pp.103–104. | Published: `GLRegularLanglandsExhaustionStatement` in `Langlands.Representation.Classification.RegularLanglandsStatement`: every irreducible admissible smooth positive-rank `GL_n` representation is the head of a regular tempered standard module. The representation-level maximal-cone construction used in its proof remains unstated. The parabolic cone specialization is now published; its application still needs class exponents, larger-Levi maps and the tempered criterion. |
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
These publication statuses concern proposition definitions, not theorem proofs.

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
representation-level maximal-exponent construction remain separate obligations.
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
