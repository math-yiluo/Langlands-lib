# Renard VI.9.1–VI.9.3: uniform compression stabilization and the generalized Jacquet lemma

This note was written on 6 November 2026 against Library
`63d0c9b9d2720e646aa7abb360a08988aee052bf`. It maps every printed assertion
of VI.9.1, and the proof steps of VI.9.2 and VI.9.3, to the published Lean
declarations that state or prove them. Where no declaration does, the note
says so. It also records one source discrepancy, after (VI.9.1.2). It
extends the VI.9.1 paragraph of the [parabolic functors note](parabolic-functors-tempered-progress.md). That
paragraph describes the published statement pair and how it differs from
the source, and this note does not repeat it.

Seventeen publications carry the material. They are two statement publications
and fifteen definition publications, listed under "In the Library". This note
documents them. The C.II statement `ActualLocalizationStabilityStatements`,
cited once below, is documented in the
[C.II note](stable-quotients.md) and is not listed again here.

## Source context

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Printed page `p` is PDF page `p + 6`. VI.9.1, "Lemme de Jacquet
généralisé", is on printed pp.195–197 / PDF pp.201–203, and the proofs of
its Remarks continue on printed p.198 / PDF p.204. VI.9.2, "Un cas
particulier", is on printed pp.198–199 / PDF pp.204–205. VI.9.3, "Fin de la
démonstration du lemme de Jacquet", is on printed p.200 / PDF p.206.
PDF pp.201–206 were read for this note.

VI.9.1 fixes a parabolic `P = MN` with split component `A`, a smooth
representation `(π, V)`, a compact open `K` with an Iwahori decomposition
with respect to `P`, and `t ∈ C_A^{++}`. Its assertions are labelled here
for the map below.

- (T) Theorem: the projection `j : V → V_N` maps `V^K` onto `(V_N)^{K_M}`.
- (VI.9.1.1) `j(e_K π(t^m) v) = π_N(t^m) j(v)` for `v ∈ V^K`.
- (VI.9.1.2) `π_N(t^m) j(V^K) ⊆ j(V^K)`. The next sentence of the source
  says that, although `π_N(t^m)` is invertible on `j(V) = V_N`, without
  admissibility this inclusion can be strict. Read literally, this
  contradicts the Theorem. See the section "Source discrepancy after
  (VI.9.1.2)" below.
- (VI.9.1.3) For `v̄ ∈ (V_N)^{K_M}` some `m` has `π_N(t^m) v̄ ∈ j(V^K)`;
  equivalently (VI.9.1.4) `⋃_m π_N(t^{-m}) j(V^K) = (V_N)^{K_M}`.
- `A` is the action on `V^K` of `a_{t,K} = e_K ∗ δ_t ∗ e_K`.
- (L1) First Lemma: `V(N) ∩ V^K = ⋃_i ker A^i`. Its proof uses
  `a_{t^i,K} = (a_{t,K})^i` (Lemma V.5.3) and (VI.9.1.5)
  `a_{t^i,K} = δ_{t^i} ∗ e_{N_i} ∗ e_K` with `N_i = t^{-i} K_N t^i`.
- (L2) Second Lemma: the localization of `V^K` at `A` is naturally
  isomorphic to `((V_N)^{K_M}, π_N(t))`, with canonical map `ι` given by
  `j`. The proof uses A.III.1, the invertibility of `π_N(t)` on
  `(V_N)^{K_M}` and (VI.9.1.6), a restatement of (VI.9.1.4).
- (P) Proposition: `A` is finally stable. There is `b = b(G, K)`,
  depending only on `G` and `K`, such that `A^b` is a stable endomorphism
  of `V^K` for every smooth `(π, V)`. With `V^K_0 = ker A^b` and
  `V^K_* = Im A^b`, `V^K = V^K_0 ⊕ V^K_*`.
- (P-loc) The localization of `V^K` at `A` is also naturally isomorphic to
  `(V^K_*, A|V^K_*)`, with `ι` the projection onto `V^K_*` along `V^K_0`.
- (P-bound) `b` can be chosen at most the constant `c(G, K)` of the uniform
  admissibility theorem VI.2.3.
- (T-end) End of the Theorem's proof: `j` is an isomorphism from `V^K_*`
  onto `(V_N)^{K_M}`, and the kernel of `j` on `V^K` is `V^K_0`. So
  `V^K_*` is a section of `j`.
- (R1) Remark 1: the decomposition does not depend on `t ∈ C_A^{++}`. For
  admissible `(π, V)` it is the decomposition of Proposition VI.6.1.
- (R2) Remark 2: there are compact open `C ⊆ N` and `C̄ ⊆ N̄` with
  `V^K_0 = V^K ∩ ker e_C` and `V^K_* = e_K ∗ e_C̄ · V` for every `(π, V)`.
- (R3) Remark 3: there is `ε > 0` with `V^K_0 = ker π(a_{t,K})` and
  `V^K_* = Im π(a_{t,K})` for every `t ∈ A^+(ε)`.

VI.9.2 proves the Proposition for the universal family of an inertia class
`D` of supercuspidal representations of a Levi subgroup `L`. Its steps are:

- (S1) `(Π_1, V_1) = ind_{⁰L}^L Res(ρ, W)` is a progenerator of `M(L)_D`
  (Remark VI.4.1), with `V_1 ≃ F ⊗ W` for the algebra `F` of regular
  functions on `X(L)`. It is an admissible `(L, F)`-module, an instance of
  Example VI.8.1.
- (S2) `i_Q^G(Π_1, V_1)` is an admissible `(G, F)`-module (Lemma VI.8.2).
  (VI.9.2.1) gives its specialization at `χ ∈ X(L)` by Corollary VI.8.2.
- (S3) Since `Π_1` is supercuspidal, Proposition VI.5.3 makes
  `r_P^G i_Q^G(Π_1, V_1)` an admissible `(M, F)`-module.
- (S4) By the second Lemma of VI.9.1, `A` on `(V_Π)^K` satisfies the
  hypotheses of Proposition C.II, hence is finally stable, (VI.9.2.2).
- (S5) `b ≤ c(G, K)`: by Lemma C.II (iv) it suffices that `A^c` kills
  `(V_Π)^K_0`. This uses generic irreducibility (Theorem VI.8.5), the bound
  (VI.9.2.3) on `dim sp_χ(V_Π)^K` and localization on principal opens as in
  VI.8.4 and VI.8.6.

VI.9.3 extends the Proposition to every smooth representation.

- (S6) For `i_Q^G(ρ, W)` with `(ρ, W)` in `M(L)_D`, Lemma A.VIII.2 gives an
  exact sequence `⊕_α V_1 → ⊕_β V_1 → W → 0`. The functors `i_Q^G` and
  `j_K` are exact and preserve sums (Corollary VI.1.2). The same `b` works
  on the sums, and Lemma C.II (ii) passes to the quotient.
- (S7) For arbitrary `V`, the decomposition theorem VI.7.2 gives
  `V = ⊕_𝔰 V_𝔰`. For the supercuspidal components the source says the claim
  is "trivial par définition". Lemma VI.7.2 (iii) embeds each other `V_𝔰`
  in a finite sum of induced representations, and its cokernel likewise.
  Exactness of `j_K` and Lemma C.II (iii) conclude.

## Lean model

The two VI.9.1 statements lie in namespace
`Langlands.Aubert.General.RationalPointFamily`, in
[UniformCompressionStabilizationStatement](../../Langlands/Representation/Exponents/UniformCompressionStabilizationStatement.md).
Unless stated otherwise, the other declarations below lie in namespace
`Langlands.Jacquet`. The Lean files are under `Langlands/Representation/`.

The parabolic is dynamic: `N` is the dynamic radical of a cocharacter `χ`,
`M` its centralizer and `N̄` the dynamic radical of the inverse
cocharacter, all on rational points. The element `t` is replaced by an
element `g` that commutes with every point of `M` and satisfies
`IsIwahoriContraction K N M N̄ g`. The fields of that predicate are
`mem_levi`, the factorization `factor` of `K` as `(K ∩ N̄)(K ∩ M)(K ∩ N)`,
the conjugation conditions `upper`, `levi` and `lower`, `exhaust` (every
point of `N` is conjugated into `K` by a power of `g`) and `contract`.

The operator `A` is `compressedAction ρ hρ K hK g`, the map
`v ↦ e_K(ρ(g) v)` on `V^K`, in
[CanonicalLiftDefinitions](../../Langlands/Representation/Jacquet/CanonicalLiftDefinitions.md).
On `V^K` this is the action of `e_K ∗ δ_g ∗ e_K`. The same module defines
`stableImage = ⨅ r, range (C ^ r)` and `powerKernelSup = ⨆ r, ker (C ^ r)`,
the candidates for `V^K_*` and `V^K_0`, and `fixedJacquetMap`, the map `j`
from `V^K` to the `K ∩ M`-fixed vectors of the actual coinvariant quotient.
`CompactCompressionSplits` says that `powerKernelSup` and `stableImage` are
complementary. Renard's stability is
`Langlands.LinearAlgebra.StableEndomorphism.Stable t`, that is
`ker t = ker t²` and `range t = range t²`, and `EventuallyStable t` asks
for a positive `n` with `Stable (t ^ n)`.

`UniformCompressionStabilizationStatement` gives, for fixed `χ`, `K` and
`g`, one `b` such that for every smooth representation on a carrier in
`Type v`, every power `C^s` with `s ≥ b` has range `stableImage` and kernel
`powerKernelSup`, and `CompactCompressionSplits` holds.
`GeneralizedJacquetLemmaStatement` asserts that `fixedJacquetMap` is
surjective under the same hypotheses on `g`.

## Assertion map for VI.9.1

| Assertion | Published declarations | Status |
| --- | --- | --- |
| (T) Theorem | `GeneralizedJacquetLemmaStatement`; `Langlands.Aubert.General.RationalPointFamily.generalizedJacquetLemma_of_uniformCompressionStabilization` in [GeneralizedJacquetReduction](../../Langlands/Representation/Exponents/GeneralizedJacquetReduction.md) | Stated for dynamic parabolics. Proved only conditionally: the reduction derives it from `UniformCompressionStabilizationStatement`. The Library has no unconditional proof |
| (VI.9.1.1) | `mk_compressedAction_of_iwahoriContraction` (`m = 1`) in [IwahoriContractionAdmissibility](../../Langlands/Representation/Jacquet/IwahoriContractionAdmissibility.md); `mk_compressedAction_pow_of_iwahoriContraction` (all `m`) in [StationaryRangeLift](../../Langlands/Representation/Jacquet/StationaryRangeLift.md) | Proved, with no finiteness premise |
| (VI.9.1.2) | none named | The inclusion follows directly from `mk_compressedAction_pow_of_iwahoriContraction`. The source's strictness sentence is a source discrepancy, not a result to formalize; see "Source discrepancy after (VI.9.1.2)" |
| (VI.9.1.3), (VI.9.1.4), (VI.9.1.6) | `exists_pow_fixedJacquetMap_preimage_of_iwahoriContraction` (StationaryRangeLift); `fixedJacquetMap_power_exhaustion` and, for `g` central in `M`, `fixedJacquetCentralEquiv_power_exhaustion` in [CompressionLocalization](../../Langlands/Representation/Jacquet/CompressionLocalization.md) | Proved in the form of (VI.9.1.3): some power of `g` carries each fixed Jacquet vector into the image of `j`. The union form is not stated separately |
| `a_{t^i,K} = (a_{t,K})^i` (V.5.3) | `IsIwahoriContraction.compressedAction_pow` (IwahoriContractionAdmissibility) | Proved for `g` |
| (L1) first Lemma | `powerKernelSup_eq_ker_of_iwahoriContraction` (IwahoriContractionAdmissibility): `powerKernelSup = ker fixedJacquetMap` | Proved, with no centrality or finiteness premise |
| (L2) second Lemma | `compressionJacquetLocalizationEquiv : Localized C ≃ₗ[ℂ] (V_N)^{K ∩ M}`, with `compressionJacquetLocalizationEquiv_iota` (composite with `iota C` is `fixedJacquetMap`) and `compressionJacquetLocalizationEquiv_intertwines` (`localizedEnd C` goes to `fixedJacquetCentralEquiv`, the action of `g`), in CompressionLocalization; generic `Langlands.Renard.EndomorphismLocalization.localizationEquivOfKernelExhaustion`; coefficient version `coefficientCompressionJacquetLocalizationEquiv` in [CompressionCoefficientLocalization](../../Langlands/Representation/Jacquet/CompressionCoefficientLocalization.md) | Constructed, for `g` central in `M`, with no finiteness premise. It uses the unnormalized Jacquet action. `Localized`, `iota` and `localizedEnd` are the A.III.1 localization of the [endomorphism-localization note](endomorphism-localization.md) |
| (P) Proposition | `UniformCompressionStabilizationStatement` | Stated with `b` chosen after `χ`, `K` and `g`, not as `b(G, K)`. Unproved: the Library derives it only from further hypotheses, by `uniformCompressionStabilization_of_representationStatements` (`Langlands/Representation/Exponents/UniformCompressionRepresentationReduction.lean`). The reductions in the next table are proved |
| (P-loc) second localization | none for `compressedAction` | **Not stated.** The C.II theorem `Langlands.Renard.EndomorphismLocalization.stablePowerImageStatement` in [RenardLocalizationStabilityProof](../../Langlands/Algebra/RenardLocalizationStabilityProof.md) gives, for any module endomorphism `a` and positive `n` with `ker (a ^ n) = ker ((a ^ n) ^ 2)` and `range (a ^ n) = range ((a ^ n) ^ 2)`, complementary `ker (a ^ n)` and `range (a ^ n)` and a unique intertwining `Localized a ≃ range (a ^ n)` whose inverse is `iota a` on the range. It is described in the [C.II note](stable-quotients.md). Its application to `compressedAction` is not published |
| (P-bound) `b ≤ c(G, K)` | none | **Not stated** |
| (T-end) end of the proof | Unconditional: `powerKernelSup_eq_ker_of_iwahoriContraction`. Conditional: `fixedJacquetMap_surjective_of_stationaryRanges` (stationary ranges), `stableImageJacquetMap_bijective_of_stationaryRanges` and `stationaryRangeJacquetEquiv : stableImage ≃ₗ[ℂ] (V_N)^{K ∩ M}` (stationary ranges and `CompactCompressionSplits`), in StationaryRangeLift; `fixedJacquetMap_surjective_of_splits`, `stableImageJacquetMap_bijective_of_splits`, `stableImageAction_bijective_of_splits` and `compactCompressionSplits_of_eventuallyStable` in [CompressionSplittingDuality](../../Langlands/Representation/Jacquet/CompressionSplittingDuality.md) | The kernel of `j` on `V^K` is `powerKernelSup`, unconditionally. The isomorphism from `stableImage` and the section are proved under the stated hypotheses, which the Proposition would supply. CompressionSplittingDuality obtains them from the contraction hypothesis and `CompactCompressionSplits` alone |
| Admissible case (VI.6.1) | `stableImageJacquetMap_bijective_of_iwahoriContraction`, `fixedJacquetMap_surjective_of_iwahoriContraction` (IwahoriContractionAdmissibility) | Proved when `V^K` is finite dimensional. The [VI.6.1 note](canonical-section-progress.md) documents the surjectivity |
| (R1), (R2), (R3) Remarks | none | **Not stated** |

The reductions of the Proposition are these proved declarations.

| Declaration | Module | Content |
| --- | --- | --- |
| `Langlands.Aubert.General.RationalPointFamily.uniformCompressionStabilizationStatement_iff_pointwise` | [UniformCompressionReduction](../../Langlands/Representation/Exponents/UniformCompressionReduction.md) | The Proposition is equivalent to `PointwiseCompressionStabilizationStatement`: for the same data, `PointwiseCompressionEventuallyStable K hK g`, that is `EventuallyStable C` for every smooth representation separately |
| `uniformCompressionStationary_of_pointwise`, `pointwiseCompressionEventuallyStable_iff_uniform`, `compactCompressionStablePower_of_retract` | [CompressionUniformity](../../Langlands/Representation/Jacquet/CompressionUniformity.md) | Uniformity of the exponent follows from pointwise eventual stability. The proof is by contradiction: it applies the pointwise hypothesis to a countable direct sum of counterexamples and retracts to each summand |
| `CompactCompressionStablePower`, `CompactCompressionStationaryFrom`, `compactCompression_eventuallyStable_iff_exists_stationaryFrom` | [StableCompressionPower](../../Langlands/Representation/Jacquet/StableCompressionPower.md) | Comparison of the stable-power and stationary-chain forms |

This replaces Renard's quantitative bound `b ≤ c(G, K)` in the uniformity
step. The published route shows only the existence of a uniform `b` for
fixed `χ`, `K` and `g`.

## Source discrepancy after (VI.9.1.2)

On printed p.196 / PDF p.202, right after (VI.9.1.2), the source says:
"Bien que `π_N(t^m)` soit inversible sur `j(V) = V_N`, sans l'hypothèse
d'admissibilité, l'inclusion ci-dessus peut être stricte." That is,
although `π_N(t^m)` is invertible on `j(V) = V_N`, without the
admissibility hypothesis the inclusion above can be strict. Read as the
claim that some smooth representation has `π_N(t^m) j(V^K) ≠ j(V^K)`,
this is false under the hypotheses of VI.9.1. Put `W = (V_N)^{K_M}`.

- The Theorem (printed p.195 / PDF p.201) gives `j(V^K) = W` for every
  smooth `(π, V)`, without admissibility.
- The proof of the second Lemma (printed p.197 / PDF p.203) checks that
  `π_N(t)` and `π_N(t^{-1})` both map `W` into itself. They are inverse to
  each other, so `π_N(t^m)` restricts to an automorphism of `W`.
- Hence `π_N(t^m) j(V^K) = π_N(t^m) W = W = j(V^K)` for every `m ∈ ℕ`.

So the inclusion (VI.9.1.2) is an equality for every smooth
representation. The sentence can only be read as a remark about the stage
of the proof: at that point only the inclusion is available. The
following derivation is the and is not in the source. Given
(VI.9.1.4), equality in (VI.9.1.2) for `m = 1` already implies the
Theorem. If `π_N(t) j(V^K) = j(V^K)`, then `π_N(t^{-m}) j(V^K) = j(V^K)`
for every `m`, and (VI.9.1.4) gives `j(V^K) = W`. So the equality is as
strong as the Theorem and cannot be used in its proof.

The strictness sentence is therefore not a result to formalize, and it is
not listed among the unpublished assertions below. In the Lean model, `g` is central in
`M`, and `fixedJacquetCentralEquiv` in CompressionLocalization is the
action of `g` as a linear automorphism `E` of the fixed Jacquet space.
`fixedJacquetMap_intertwines_centralEquiv` gives `j(C x) = E(j x)` for
`C = compressedAction`, which is the inclusion (VI.9.1.2) for `m = 1`.
Since `E` is bijective, the equality `E(range j) = range j` would follow
from `GeneralizedJacquetLemmaStatement`, which the Library proves only
conditionally. This has not been checked in Lean, and no published
declaration states the equality.

## Proof steps VI.9.2–VI.9.3

| Step | Published declarations | Status |
| --- | --- | --- |
| (S1) coefficient algebra | `Langlands.Plancherel.RationalNormalized.regularAlgebraLaurentEquiv`, `regularAlgebra_isNoetherianRing`, `regularAlgebra_finiteType`, `regularAlgebra_isDomain` in [UnramifiedRationalCoefficientAlgebra](../../Langlands/Representation/Plancherel/UnramifiedRationalCoefficientAlgebra.md) | Proved for the complete rational-norm algebra `RegularAlgebra r`. The VI.4.1 progenerator statements are listed below |
| (S2) admissible `(G, F)`-module, (VI.9.2.1) | VI.8.1–VI.8.2 statements below | Proved for the universal normalized induced family. For a general `B`, the VI.8.1 admissibility criterion and specialization Lemma are stated and unproved, and induction of `(G, B)`-modules (VI.8.2) is not stated. See the [VI.8 assertion map](algebraic-families-progress.md) |
| (S3) Jacquet module finite | `Langlands.Plancherel.RationalSupercuspidalJacquetFamilyFiniteStatement` in [UnramifiedRationalJacquetFinitenessStatement](../../Langlands/Representation/Plancherel/UnramifiedRationalJacquetFinitenessStatement.md) | Stated; proved as `rationalSupercuspidalJacquetFamilyFinite` (`Langlands/Representation/Plancherel/UnramifiedRationalJacquetFinitenessProof.lean`) |
| (S4) finite stability, (VI.9.2.2) | `fixedJacquetMap_surjective_and_eventuallyStable_of_finite_coefficients` (CompressionCoefficientLocalization) over a Noetherian `R` with `V^K` and the target finite; `fixedJacquetMap_surjective_and_eventuallyStable_of_compatible_coefficients` in [CompatibleCoefficientActions](../../Langlands/Representation/Jacquet/CompatibleCoefficientActions.md); `CoefficientRestriction.compressedAction_eventuallyStable_of_native_finite` in [CoefficientScalarRestriction](../../Langlands/Representation/Jacquet/CoefficientScalarRestriction.md); `Langlands.Plancherel.UnramifiedNormalized.compressedAction_eventuallyStable_of_normalized_finite` and `normalizedJacquetFixedEquiv` in [UnramifiedCompressionCriterion](../../Langlands/Representation/Plancherel/UnramifiedCompressionCriterion.md) | Proved conditionally. The finiteness of `V^K` and of the normalized Jacquet fixed module over the coefficient algebra are hypotheses. The C.II input is `finiteActualLocalizationStatement`. No eventual-stability theorem for the universal family itself is published |
| (S5) `b ≤ c(G, K)` | none | **Not stated** |
| (S6) passage to quotients and sums | `compressedAction_stablePower_of_rightExact`, `compressedAction_pow_directSum`, `compressedAction_stablePower_directSum_iff`, `Langlands.fixedVectorsDirectSumEquiv`, and `Langlands.LinearAlgebra.StableEndomorphism.stable_of_equiv`, `stable_directSum` and `stable_directSum_iff`, in [StableCompressionPropagation](../../Langlands/Representation/Jacquet/StableCompressionPropagation.md) | Proved for a fixed exponent |
| (S7) kernels and the decomposition | `compressedAction_stablePower_of_leftExact` (StableCompressionPropagation); `compressedAction_eventuallyStable_directSum_of_finite_support` and `FiniteFixedVectorSupport` in [CompressionFiniteSupport](../../Langlands/Representation/Jacquet/CompressionFiniteSupport.md); `Langlands.SmoothRep.HasFixedVectorConstituent`, `hasFixedVectorConstituent_of_nontrivial` and `finite_fixedVectorSupport_of_finite_constituent_classes` in [FixedVectorConstituent](../../Langlands/Representation/Category/FixedVectorConstituent.md); `Langlands.Aubert.General.FiniteInductionFixedVectorVisibility` and `finiteInductionFixedVectorVisibility` in [InductionCompactVisibility](../../Langlands/Representation/Aubert/General/InductionCompactVisibility.md); the VI.7.2 embedding statement below | Kernel passage proved. The direct-sum step is proved under finiteness of the set of summands with nonzero `K`-fixed vectors, together with stability of each summand. CompressionFiniteSupport calls this a derived alternative to Renard's uniform bound. The decomposition and embedding inputs are open |

## Prerequisite statements

This section was updated against Library
`f73044d93e675a78ed75830ef026b3224514e510`. At that commit the three VI.8
statements and the VI.4.1 comparison statement were proved, and no proof of
the other statements in this section was published. The four proofs are
recorded in the [VI.8 note](algebraic-families-progress.md). The last column
gives the proof the Library has now.

| Source input | Published statement | Proof in the Library |
| --- | --- | --- |
| VI.8.1–VI.8.2 flatness and fixed-space finite projectivity of universal normalized induction | `Langlands.Plancherel.RationalNormalized.UniversalInducedCoefficientFinitenessStatement` in [UnramifiedRationalNormalizedInducedFiniteness](../../Langlands/Representation/Plancherel/UnramifiedRationalNormalizedInducedFiniteness.md) | proved: `universalInducedCoefficientFiniteness` (`Langlands/Representation/Plancherel/UnramifiedRationalNormalizedInducedFinitenessProof.lean`) |
| VI.8.1 universal tensor finiteness | `Langlands.Plancherel.RationalNormalized.RationalUniversalTensorFinitenessStatement` in [RationalUniversalTensorFinitenessStatement](../../Langlands/Representation/Plancherel/RationalUniversalTensorFinitenessStatement.md) | proved: `rationalUniversalTensorFiniteness` (`Langlands/Representation/Plancherel/RationalUniversalTensorFinitenessProof.lean`) |
| VI.8.2 specialization, (VI.9.2.1) | `Langlands.Plancherel.RationalNormalized.RationalNormalizedInducedSpecializationStatement` in [RationalNormalizedInducedSpecializationStatement](../../Langlands/Representation/Plancherel/RationalNormalizedInducedSpecializationStatement.md) | proved: `rationalNormalizedInducedSpecialization` (`Langlands/Representation/Plancherel/RationalNormalizedInducedSpecializationProof.lean`) |
| VI.9.2 Jacquet family finiteness, (S3) | `Langlands.Plancherel.RationalSupercuspidalJacquetFamilyFiniteStatement` | proved: `rationalSupercuspidalJacquetFamilyFinite` (`Langlands/Representation/Plancherel/UnramifiedRationalJacquetFinitenessProof.lean`) |
| VI.7.2 finite induced-cuspidal embedding, (S7) | `Langlands.Aubert.General.RationalPointFamily.RationalCuspidalInducedEmbeddingStatement` in [RationalCuspidalInducedEmbeddingStatement](../../Langlands/Representation/CuspidalSupport/RationalCuspidalInducedEmbeddingStatement.md) | not proved; derived from further hypotheses by `rationalCuspidalInducedEmbedding_of_leviJacquetSplittings` (`Langlands/Representation/CuspidalSupport/RationalFiniteCuspidalEmbeddingReduction.lean`) |
| VI.4.1 progenerator, (S1) | `Langlands.CuspidalSupport.RationalUniversalProgeneratorComparisonStatement` in [RationalUniversalProgeneratorComparisonStatement](../../Langlands/Representation/CuspidalSupport/RationalUniversalProgeneratorComparisonStatement.md) and `Langlands.CuspidalSupport.RationalUniversalSmallProgeneratorStatement` in [RationalUniversalSmallProgeneratorStatement](../../Langlands/Representation/CuspidalSupport/RationalUniversalSmallProgeneratorStatement.md) | comparison statement proved: `rationalUniversalProgeneratorComparison` (`Langlands/Representation/CuspidalSupport/RationalUniversalProgeneratorComparisonProof.lean`); small-progenerator statement not proved, derived from further hypotheses by `rationalUniversalSmallProgenerator_of_specialVertexInputs_of_restriction` (`Langlands/Representation/CuspidalSupport/RationalUniversalSmallProgeneratorSpecialVertexReduction.lean`) |

Further inputs to (S7) are the compact-level cuspidal inertia finiteness of
VI.3.4 and the inertial cuspidal data and Bernstein blocks of VI.7.1–VI.7.2.

## Unpublished assertions

At Library `63d0c9b9` these printed assertions have no published statement:

1. The Theorem for every `K` with an Iwahori decomposition and every
   actual parabolic. The comparison with actual parabolics is the separate
   target `ParabolicDynamicStatement`, in
   [BorelStatement](../../Langlands/GroupScheme/Absolute/BorelStatement.md).
2. The dependence `b = b(G, K)` of the Proposition.
3. (P-loc), the identification of the localization with
   `(V^K_*, A|V^K_*)`.
4. The bound `b ≤ c(G, K)` of the Proposition, and its proof (S5).
5. Remarks 1–3.
6. The VI.9.2 eventual stability (VI.9.2.2) for the universal family, as
   a standalone statement.

The strictness sentence after (VI.9.1.2) is omitted from this list: it is
the source discrepancy recorded above, not an assertion to formalize.

The following route has not been checked in Lean; it is a
suggestion only. Given the Proposition's conclusion at a fixed
representation, `Stable (C ^ n)` holds for `n = max b 1`. Then
`stablePowerImageStatement` at `n` would give (P-loc), because the
Proposition also identifies `range (C ^ n)` with `stableImage`.

## In the Library

All seventeen publications are in the Library.

| Publication | First appeared at Library commit |
| --- | --- |
| VI.9.1 statements (`UniformCompressionStabilizationStatement`) | `86cf8f8984679ba48ded6fa152c55ec38b532d97` |
| Stationary-range lift and Theorem reduction (`stationaryRangeJacquetEquiv`) | `1eb9a9ee0815224a368f8dc58b7d95f024cfff05` |
| Pointwise reduction (`PointwiseCompressionStabilizationStatement`) | `1eb9a9ee0815224a368f8dc58b7d95f024cfff05` |
| Coefficient localization (`coefficientCompressionJacquetLocalizationEquiv`) | `1eb9a9ee0815224a368f8dc58b7d95f024cfff05` |
| Uniformity (`UniformCompressionStationary`) | `1eb9a9ee0815224a368f8dc58b7d95f024cfff05` |
| Stable powers (`CompactCompressionStationaryFrom`) | `1eb9a9ee0815224a368f8dc58b7d95f024cfff05` |
| Propagation (`fixedVectorsDirectSumEquiv`) | `1eb9a9ee0815224a368f8dc58b7d95f024cfff05` |
| Second Lemma (`compressionJacquetLocalizationEquiv`) | `1eb9a9ee0815224a368f8dc58b7d95f024cfff05` |
| Normalized criterion (`normalizedJacquetFixedEquiv`) | `80f702330eab13242c1eb52eee2757a5d07eb1ba` |
| Coefficient algebra (`regularAlgebraLaurentEquiv`) | `80f702330eab13242c1eb52eee2757a5d07eb1ba` |
| Scalar restriction (`CoefficientRestriction.coinvariantsEquiv`) | `80f702330eab13242c1eb52eee2757a5d07eb1ba` |
| Compatible coefficients (`coefficientRelations`) | `80f702330eab13242c1eb52eee2757a5d07eb1ba` |
| Finite support (`FiniteFixedVectorSupport`) | `80f702330eab13242c1eb52eee2757a5d07eb1ba` |
| Fixed-vector constituent (`SmoothRep.HasFixedVectorConstituent`) | `80f702330eab13242c1eb52eee2757a5d07eb1ba` |
| Induction visibility (`FiniteInductionFixedVectorVisibility`) | `80f702330eab13242c1eb52eee2757a5d07eb1ba` |
| VI.7.2 embedding statement (`RationalCuspidalInducedEmbeddingStatement`) | `1eb9a9ee0815224a368f8dc58b7d95f024cfff05` |
| Splitting duality (`contragredientNormalizedJacquetIsoOfSplits`) | `8b3ba080b2e8bcecb1612373f236b9ad96423d12` |

The stationary-range lift and Theorem reduction publication carries both
StationaryRangeLift and GeneralizedJacquetReduction. The splitting-duality
publication has entry module
[IwahoriNaturalJacquetDuality](../../Langlands/Representation/Aubert/General/IwahoriNaturalJacquetDuality.md)
and carries CompressionSplittingDuality.

Each publication was checked by a fresh Lake build of the Library with it. The
build checks compilation, not mathematical fidelity.

The Lean and Markdown files of the nineteen modules below were checked at
Library `63d0c9b9`. Each equals its copy in every publication, as first checked,
that contains it, with one exception: the coefficient-localization and
second-Lemma publications contained an earlier StableCompressionPropagation pair,
which the propagation publication superseded.

| File under `Langlands/Representation/` | SHA256 at Library `63d0c9b9` |
| --- | --- |
| `Exponents/UniformCompressionStabilizationStatement.lean` | `f326323a374173794c5dfda7dbf0003505410b9fcf6577cbb8ffb962a79dad8f` |
| `Exponents/UniformCompressionStabilizationStatement.md` | `61f7fd8af518824e729ca5a0fae16d93567eea16a62cadd8559c789e063f7162` |
| `Exponents/GeneralizedJacquetReduction.lean` | `bc01a41c868aa489cd8eed7b373cdd78e4ca44c8c47121361f5535a1121f89ee` |
| `Exponents/GeneralizedJacquetReduction.md` | `c32e141856de26c44c6ac77a2c968f6ce8477afd7791f921d1c33a942c314f0a` |
| `Jacquet/StationaryRangeLift.lean` | `57e0336f0d8f61e00edaf07aaea9a1583d006481f5194b37d271c369934b7e08` |
| `Jacquet/StationaryRangeLift.md` | `44b5de11575ece2eb5de84fcf56f4e3d2de87a32ceae094ff17f169b77b34018` |
| `Exponents/UniformCompressionReduction.lean` | `3bdaa825400dda1f344782d43ccc0f70843e788deb9fda81c59e4f40452158ba` |
| `Exponents/UniformCompressionReduction.md` | `e0b95b8b9a6bf9d4b18508b41bb8c767b0c458b4b942ea069554e75fa65be5c2` |
| `Jacquet/CompressionUniformity.lean` | `395a8074565dfd07fcb0d2ae2fc98e45b3436a625afeb3fac1ba99a646cfb7d9` |
| `Jacquet/CompressionUniformity.md` | `1124332a2ab2c4ff1acccd2ef0ce4c668f8ba9a2c1671ca6677d14fcd942fdf4` |
| `Jacquet/StableCompressionPower.lean` | `531c8458ba6f64d9901d4c7753e64a87e7572a0aedbb18f558da427ea572d8f4` |
| `Jacquet/StableCompressionPower.md` | `f34204e22cc025bdbd20b28fb89b6bcaee719b298dd05969293e9053f9c63c6c` |
| `Jacquet/StableCompressionPropagation.lean` | `04756ef0674ae853264fedbe845f51fd076b4a928862fb00acf0e3e6dce8bb0f` |
| `Jacquet/StableCompressionPropagation.md` | `c3eb8d1403f52f322565fdce0d0f3a887447d2b8b445bd53f13b8f681d93bec3` |
| `Jacquet/CompressionLocalization.lean` | `d17c396c6d34a453828e080edacb4894cb4a21b8269f097af1c399c09674deea` |
| `Jacquet/CompressionLocalization.md` | `86160d5d50ce0cc5fb948667393a8617039805d6a04dfca05e9b8e322a42e606` |
| `Jacquet/CompressionCoefficientLocalization.lean` | `db3943bf4dd4465df630dc75227c89a8da842afd72fc15d4365be3ef49442493` |
| `Jacquet/CompressionCoefficientLocalization.md` | `bd3e311909271408854eb52971025ab24485e6b512ac72018badeacc4519451a` |
| `Jacquet/CoefficientScalarRestriction.lean` | `0c26b9f432ceebbb5d354e084314f888c98d5d07da8bd6e62cfc7eb88b1bee59` |
| `Jacquet/CoefficientScalarRestriction.md` | `9f44b88d0561a02aa2640a927d66bc48158e1b45f5198d60c4b837672d9d2432` |
| `Jacquet/CompatibleCoefficientActions.lean` | `6f228d8c4c42faa0e92a07c7898a97c25684638b5260276366dc9d2ed634bbd4` |
| `Jacquet/CompatibleCoefficientActions.md` | `2d1b2d56e26cfe513ae3e87771525457a7661c54e50a649017a41f37c0a0e7b6` |
| `Jacquet/CompressionFiniteSupport.lean` | `2e316e8bbb5ac35ab23cdd413636fde1dddae482b9b4bdce5ec3cfb354420d89` |
| `Jacquet/CompressionFiniteSupport.md` | `6301c58fc8eaa6360a08ea9a1814512caafb23bb7d995b1b8703b0e5f0067e68` |
| `Plancherel/UnramifiedCompressionCriterion.lean` | `d0d31a6596fdc2941c35a5b9bf0c1d1dd0c540fb6d09a33d16d8ddadc696c57b` |
| `Plancherel/UnramifiedCompressionCriterion.md` | `027385adabeb2378c56f12a19c5cedfedc8e877026cac36a539652863be8fd7d` |
| `Plancherel/UnramifiedRationalCoefficientAlgebra.lean` | `86cfa29a5a2906b6d3e49171b3eabaca797f7b14e067494265acf1e7cca1aa25` |
| `Plancherel/UnramifiedRationalCoefficientAlgebra.md` | `c74ebdaf8391d90a97334fa328820e0da3a919d73e778fbfc7604d2aacf602aa` |
| `Category/FixedVectorConstituent.lean` | `354e25ddadaac65c1fc1ce8cd3403119dc4aa4446146e39b8a9b9c1759780690` |
| `Category/FixedVectorConstituent.md` | `a51f389d6406ed237c23ed26dc07f18a75cf8d3785f89b0f52b32e4b028f8876` |
| `Aubert/General/InductionCompactVisibility.lean` | `ce4f107ca796f0110ce1e62e4f6a0287f74eae73359fc2f30035f07383a48519` |
| `Aubert/General/InductionCompactVisibility.md` | `df3e955c1766ee5d4fc46fe3e2bf73ad98ff9cd85dc8487ddfdbe141d2b6c202` |
| `CuspidalSupport/RationalCuspidalInducedEmbeddingStatement.lean` | `98e29ff71efbb249dd6c7c38f86d11eb0c17aa970ca1e4ac2eeb82b5769961a2` |
| `CuspidalSupport/RationalCuspidalInducedEmbeddingStatement.md` | `23844cd70e757daa68160dfaf3a43096bf8babfb423da2765318297e6bada769` |
| `Jacquet/CompressionSplittingDuality.lean` | `f89363c84e54e45b6227cae3ea76089d34f3baadcab0de8025d53ce09af1fee1` |
| `Jacquet/CompressionSplittingDuality.md` | `f916dc3f82ffe54b78a90e28ed6d36223c69f9148ff2416c1b4aafb17e707aec` |
| `Aubert/General/IwahoriNaturalJacquetDuality.lean` | `fcaa9c6e3712e28868035757328a9f7336a01e2a04f7c6762cc161ff84c5e4a6` |
| `Aubert/General/IwahoriNaturalJacquetDuality.md` | `b862273df048cc6b7941c496e9457618d7ceb6fb12ac364df9abb748c5e78dbe` |

## Scope

This note covers VI.9.1–VI.9.3 only. VI.9.4–VI.9.7, including the VI.9.6
second-adjointness statements described in the parabolic functors note, are
outside it. This note declares no section, chapter or book completion.
