# Arthur L3 foundations: declarations and proof targets

Worker 128, Task 5536 (`e079aef9-b46a-468b-a373-87322d41b934`), a block of the [global automorphic program](global-program-coverage.md). This snapshot records the five units verified in Library commit `7ae0d83b7cb2ad9aaca52ada487b3a5d3314323a` and their exact-target proof successors. A published proposition is not a proof. Each of the twelve successors below was open, with no published proof of its exact target, when created.

Arthur 2005 is *An introduction to the trace formula*, in `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura` (PDF page = printed page + 12). Arthur 1978 is *A trace formula for reductive groups I*, `arthur-1978-trace-formula-reductive-groups-I`. Lapid 2011 is *On Arthur's asymptotic inner product formula of truncated Eisenstein series*, `lapid-2011-asymptotic-inner-product-truncated-eisenstein` (PDF page = printed page + 9). The paired Markdown in the links gives the source comparisons, including the qualifications below.

## Root combinatorics and real parameters

- [ArthurRelativeCombinatorics](../../Langlands/GroupScheme/Rational/ArthurRelativeCombinatorics.md), `Langlands.GroupScheme.ArthurRelative`: `rootPairing` and `base` use the indivisible relative roots (also for non-reduced systems); `standardIndex` transports standard-parabolic indexing. `toCorootSpan` removes the central part, and `levelProjection`, `aSpace`, `relativeSpace`, `weight`, `tau`, `tauHat`, `sigma`, `epsilon` and `phi` implement the Arthur 1978 §1 and §6 and Arthur 2005 §§5 and 8 conventions. This unit contains proved identifications, not a new proposition target. The abstract `Langlands.ArthurCombinatorics.ArthurCombinatoricsStatement` already has the public proof `Langlands.ArthurCombinatorics.arthurCombinatoricsStatement` in `Langlands.LinearAlgebra.ArthurCombinatoricsProof`; no successor here duplicates it.
- [ArthurParabolicSpaces](../../Langlands/Global/ArthurParabolicSpaces.md), `Langlands.Global.ArthurParabolicSpaces`: `restrictToTorus` acts on `RealCharacterParameter`, and `toCharacterDual` is its transpose on cocharacters with values in `RealCharacterDual`. The [comparison statement](../../Langlands/Global/ArthurParabolicSpacesStatement.md) concerns these maps for the actual standard group schemes. `bijective_restrictToTorus_empty` is a proved consequence *of* that statement, not its proof. It supplies the `hρ` used to read the minimal-parabolic height in `𝔞₀` when the comparison is proved.

| Source | Exact target | Open proof task |
|---|---|---|
| Arthur 2005, §5, (5.1) and p.26 | `Langlands.Global.ArthurParabolicSpaces.ParabolicSpacesComparisonStatement` | Task 8038 (`35d6500f-c0ca-4677-a1be-dbd991307099`) |

## `(G, M)`-families

[GMFamilies](../../Langlands/LinearAlgebra/GMFamilies.md) implements families of smooth functions on the imaginary dual, face restriction, the Euclidean lattice-covolume factors of `theta` and `thetaHat`, the sum `cM`, and the product and descent coefficients. Its root arrangement is an abstract Euclidean model. The [statements](../../Langlands/LinearAlgebra/GMFamiliesStatement.md) use `Langlands.GMFamily`:

| Source | Exact target (in `Langlands.GMFamily`) | Open proof task |
|---|---|---|
| Arthur 2005, Lemma 17.1, p.94 | `SmoothExtensionStatement` | Task 8039 (`8188c354-ba73-41df-87de-2d4ecbc33560`) |
| Lemma 17.4, pp.97–98 | `SplittingFormulaStatement` | Task 8040 (`1de8ea23-9d57-4c8b-be0c-9a4a1ced1253`) |
| Lemma 17.5, pp.99–100, same-field Levi case | `DescentFormulaStatement` | Task 8041 (`21b29a48-46ac-4b23-b3b7-ce2a027c8df1`) |
| Lemma 17.6, p.101, with the two-family summand from Arthur 1988, Corollary 7.4 | `AlternateSplittingFormulaStatement` | Task 8042 (`71fdc83c-7051-45f4-95e2-3729268d7dd6`) |
| Conjunction | `GMFamilyStatement` | Task 8048 (`fb9a2b4f-b9f9-4efe-8b73-5a7313ad1136`), assembles 8039–8042 |

The splitting and descent identities use their defining expressions away from a finite union of proper hyperplanes, not separate propositions at `λ = 0`. Passing to all parameters uses continuity of the smooth extensions (including the extension of the primed term in Lemma 17.3). For a proper field extension, rational character base change need not agree with extending a parameter by orthogonal projection for an arbitrary invariant metric on the larger root space. That case of Lemma 17.5 is not covered.

## Truncation and Siegel sets

[ArthurTruncation](../../Langlands/Global/ArthurTruncation.md) defines `truncation` and `relativeTruncation` on full adelic points as in Lapid 2011, §2, p.312, with Arthur's relative sign `(−1)^{dim 𝔞_Q^P}`. The height is read from the L1 `IsIwasawaCompact.height` for `P₀` using the comparison `hρ`. Constant terms are the L1 subgroup integrals with quotient Haar probability measure along the unipotent radical. [ArthurSiegelSets](../../Langlands/Global/ArthurSiegelSets.md) defines the sets using the L1 ordered product `N₀ M₀¹ A₀ K` with compact factors from `AdelicSiegelFactors`, and defines `siegelIndicator` on adelic points: it is `1` exactly when a left `P(F)`-translate lies in the truncated set. This pulls back the characteristic function of the image in `P(F) \ G(𝔸_F)`, not in the L1 quotient `X_P`.

All targets in this table belong to `Langlands.Global.ArthurTruncation`. The first four and their conjunction are in [ArthurTruncationStatement](../../Langlands/Global/ArthurTruncationStatement.md); the common-witness bundle is in [ArthurSiegelSetsStatement](../../Langlands/Global/ArthurSiegelSetsStatement.md).

| Source | Exact target | Open proof task |
|---|---|---|
| Arthur 2005, p.68; Arthur 1978, Lemma 5.1 | `TruncationFinitenessStatement` | Task 8043 (`1035fa58-0f5c-477e-9a76-7a5ee85716f1`) |
| Arthur 2005, p.68 and Proposition 13.1(c), pp.68–69 | `TruncationSelfAdjointStatement` | Task 8044 (`78bc713c-5319-4b23-aa99-6f660e97db41`) |
| Proposition 13.1(a),(b), pp.68–69 | `TruncationProjectionStatement` | Task 8047 (`f51727f3-8e37-44b1-a176-200134d1fbd6`), can project the witness and idempotence from 8046 |
| Proposition 13.3 and (13.10), pp.73–74 | `TruncationCancellationStatement` | Task 8045 (`eb872e23-a8fe-4416-b995-287a3b521636`) |
| Lemma 8.2 and (8.1), pp.38–41; Proposition 13.1(a),(b); Proposition 13.2(a), p.71 (restricted); Arthur 1978, Lemma 6.4 | `ArthurSiegelSetsStatement` | Task 8046 (`30990292-d483-4592-9f11-48f7ec8e12e6`) |
| Conjunction of the four `ArthurTruncationStatement` module targets | `ArthurTruncationStatement` | Task 8049 (`12188a0b-2992-482f-8c87-a1c16b8a487d`), assembles 8043–8045 and 8047 |

`TruncationSelfAdjointStatement` includes local boundedness, convergence of truncated constant terms, and the pairing with a continuous function of compact support modulo `G(F)`. `TruncationProjectionStatement` is pointwise constant-term vanishing and idempotence, not a bounded projection on `L²`. `ArthurSiegelSetsStatement` has **one** maximal compact witness for covering, both finite-support partitions, pointwise idempotence and rapid decay. The decay conclusion is on norm-one slices, for restrictions of full-adelic smooth uniformly moderately growing functions. The full norm-one function space and the uniform family estimate of Proposition 13.2(b), (13.5)–(13.6), are not stated in these five units. Neither is the Hilbert-space extension in the paragraph after Proposition 13.1. These scope boundaries and the field-extension case of descent remain separate from the proof work on the published targets.
