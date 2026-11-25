# Poitou–Tate duality, the global Euler characteristic and Selmer groups

This note describes the top of the Library's global Galois cohomology:
`Langlands/GaloisCohomology/Global/PoitouTate/`, `Langlands/GaloisCohomology/Global/EulerCharacteristic/`
and `Langlands/GaloisCohomology/Global/Selmer/` (namespaces `Langlands.GaloisCohomology` and
`Langlands.GaloisCohomology.PoitouTate`). It uses everything in [global Galois cohomology](global.md)
and [local Galois cohomology](local.md); the [overview](overview.md) gives the whole.

## The mathematics

Let `K` be a number field, `S` a finite set of finite places containing the places above `N ≥ 1`,
G_S the Galois group of the maximal extension K_S unramified outside `S`, `M` a finite
G_S-module killed by `N` and `M' = Hom(M, μ_N)`. Poitou and Tate proved that cup product and the
sum of the local invariants give perfect pairings between global cohomology and cohomology with
compact support, that the sequence

`0 → H⁰(G_S, M) → P̂⁰(M) → H²(G_S, M')^∨ → H¹(G_S, M) → P¹(M) → H¹(G_S, M')^∨ → H²(G_S, M) → P²(M) → H⁰(G_S, M')^∨ → 0`

is exact, where `Pⁿ(M) = ∏_{v ∈ S} Hⁿ(K_v, M) × ∏_{w real} Hⁿ(K_w, M)` (with Tate's `Ĥ⁰` at the
real places in `P̂⁰`) and `X^∨ = Hom(X, ℚ/ℤ)`, and that the Tate–Shafarevich groups `Ш¹_S(M)` and
`Ш²_S(M')` are finite and dual. Tate's global Euler characteristic formula computes
`|H⁰|·|H²|/|H¹|` for G_S, and the formula of Greenberg and Wiles compares the orders of the Selmer
groups of a family of local conditions and of the dual family. The Library follows Tate's address
of 1962, Milne, *Arithmetic Duality Theorems*, I §4–§5, and Neukirch–Schmidt–Wingberg,
*Cohomology of Number Fields*, VIII §6 (the formula of Greenberg and Wiles is their (8.7.9)); each
page gives the exact places.

## Layout

`Langlands/GaloisCohomology/Global/PoitouTate/`:

| Files | Content |
| --- | --- |
| `Trace.lean`, `FiniteTrace.lean` | the families of localizations, the dualizing module μ_N, the local invariants, the trace `Ĥ_c³(G_S, μ_N) → ℤ/N` |
| `Sequence.lean`, `LocalPairings.lean`, `LocalDuality.lean` | the groups and maps of the nine-term sequence; the local pairings; local Tate duality at the places of `S` |
| `DualityStatement.lean`, `NineTermStatement.lean`, `ShaStatement.lean` | the three statements |
| `BaseCase/`, `FinitePlaces.lean`, `FinitePlacesProof.lean` | the base case: the pairing of the roots of unity; duality with compact support at the finite places when `N` is odd or `K` totally complex |
| `OpenSubgroups.lean`, `OddDuality.lean`, `EvenDuality.lean`, `Hypotheses.lean`, `Reduction.lean`, `Assembly.lean` | the passage to open subgroups, the odd and even cases, the hypotheses of the abstract nine-term sequence for G_S, the assembly |
| `DualityProof.lean`, `NineTermProof.lean`, `ShaProof.lean` | the three proofs |
| `Corollaries.lean` | the isomorphisms and the criteria for local classes to come from global ones |

`Langlands/GaloisCohomology/Global/EulerCharacteristic/`: `Statement.lean`, `Proof.lean`, the steps
(`Ratio.lean`, `Multiplicative.lean`, `Induced.lean`, `KummerSha.lean`, `ShaDescent.lean`,
`ShaTwist.lean`), `Corollaries.lean`, and `Internal/`.

`Langlands/GaloisCohomology/Global/Selmer/`: `LocalConditions.lean`, `SelmerGroup.lean`,
`Orthogonal.lean`, `LocalPairing.lean`, `ExactSequence.lean`, `Bidual.lean`, `LocalCount.lean`,
`Unramified.lean`, `GreenbergWilesStatement.lean`, `GreenbergWilesProof.lean`.

The order is: the vanishing of Ĥ_cʳ in degrees `≥ 4` and the base case → duality → the nine-term
sequence and `Ш` → their corollaries → the real places in degree three
(`Langlands/GaloisCohomology/Global/RealPlaces/DegreeThreeProof.lean`) → the Euler characteristic →
Selmer groups.

## The data of the statements

In namespace `Langlands.GaloisCohomology.PoitouTate`, for `K, Ω : Type u`, `Ω` a separable closure,
`S` finite (`[Finite S]`), `ι : PlaceEmbeddings K Ω`, `N` with `[NeZero N]` and
`M : Rep (ULift ℤ) G_S` finite and smooth:

- `localFamily ι S`, `realFamily ι S`: the localization homomorphisms at the places of `S` and at
  the real places; `dualizingModule K Ω S N = μ_N(K_S)`; `dual N M = Hom(M, μ_N)`
  (`Trace.lean`, `Sequence.lean`).
- `compactCohomology ι M n = Ĥ_cⁿ(G_S, M)`: cohomology with compact support with respect to the
  places of `S` and the real places, with Tate's `Ĥ⁰` in degree `0` at the real places (the
  Tate-modified theory of `Langlands/GaloisCohomology/CompactSupport/TateModified/`).
- `invariantAt`, `realInvariantAt`: the local invariants on `H²(K_v, μ_N)` and `H²(K_w, μ_N)`;
  `trace ι S N : Ĥ_c³(G_S, μ_N) →+ ℤ/N`, characterized by `trace_localToCompact` (on the image of
  the local terms it is the sum of the local invariants).
- `dualityMap ι N M h : Hʳ(G_S, M) → Hom(Ĥ_cˢ(G_S, M'), ℤ/N)` and
  `compactDualityMap ι N M h : Ĥ_cʳ(G_S, M) → Hˢ(G_S, M')^∨` for `h : r + s = 3`; `shaPairing ι N M`;
  the maps `locHat`, `locDualHat`, `connecting`, `loc`, `locDual` of the nine-term sequence.

## Main theorems

All are proved; the hypotheses are those of the statements: `K` any number field, `Ω` any separable
closure in the same universe, `S` any finite set of finite places containing the places above `N`,
`M` any finite smooth G_S-module killed by `N`, with **no condition on the parity of `N` and none
on the real places**.

- `PoitouTateDualityStatement` (`PoitouTate/DualityStatement.lean`) asserts `PoitouTate.IsDuality ι N M`:
  `dualityMap` is bijective for `r + s = 3`, `s ≥ 1`, and `compactDualityMap` for `r + s = 3`,
  `r ≥ 1`. Proved: `poitouTateDualityStatement` (`PoitouTate/DualityProof.lean`).
- `PoitouTateNineTermStatement` (`PoitouTate/NineTermStatement.lean`) asserts
  `PoitouTate.IsNineTermExact ι N M`, the exactness of the nine-term sequence at its nine places.
  Proved: `poitouTateNineTermStatement` (`PoitouTate/NineTermProof.lean`).
- `PoitouTateShaStatement` (`PoitouTate/ShaStatement.lean`) asserts `PoitouTate.IsShaDuality ι N M`:
  `Ш¹_S(M)` and `Ш²_S(M')` (`sha`) are finite and `shaPairing` is perfect on both sides. Proved:
  `poitouTateShaStatement` (`PoitouTate/ShaProof.lean`).
- Corollaries (`PoitouTate/Corollaries.lean`): `PoitouTate.dualityEquiv`,
  `PoitouTate.compactDualityEquiv`, `PoitouTate.shaDualEquiv` (the isomorphisms), and
  `PoitouTate.mem_range_loc_one_iff`, `PoitouTate.mem_range_loc_two_iff`: a family of local classes
  in degree `1` (resp. `2`) comes from a global class iff it is orthogonal, under the sum of the
  local pairings, to the localizations of all global classes of `M'` in degree `1` (resp. `0`).
- Local duality at the places of `S` in every universe: `LocalTateDualityStatement` with
  `localTatePairing` (`PoitouTate/LocalDuality.lean`), proved by `localTateDualityStatement` from
  `Langlands.GaloisCohomology.Local.tatePairing_bijective`.
- When `N` is odd or `K` is totally complex the real places play no role, and
  `FinitePlacesDualityStatement` (`PoitouTate/FinitePlaces.lean`, duality with compact support at the
  places of `S` only, for a trace `T` restricting to the sum of the invariants) is proved by
  `finitePlacesDualityStatement` (`PoitouTate/BaseCase/Proof.lean`), from the pairing of the roots of
  unity (`RootsOfUnityPairingStatement`, `BaseCase/Main.lean`, proved by
  `rootsOfUnityPairingStatement` in `BaseCase/Pairing.lean`).
- **Tate's global Euler characteristic formula** `GlobalEulerCharacteristicStatement`
  (`EulerCharacteristic/Statement.lean`): for every finite smooth G_S-module `M` with the places
  above `#M` in `S` (`S` finite),
  `Langlands.ProfiniteCohomology.eulerCharacteristic M = ∏_{w real} #H⁰(K_w, M) / (#M)^{#∞}`, `#∞` the number of infinite places
  (`Fintype.card (InfinitePlace K)`). Proved: `globalEulerCharacteristic`
  (`EulerCharacteristic/Proof.lean`), with the `ℓ`-primary case `eulerCharacteristic_eq_of_primary`
  and the form `card_cohomology_one_mul_prod`. `EulerCharacteristic/Corollaries.lean` counts
  `H²(G_S, M)` by the end of the nine-term sequence (`card_cohomology_two_mul_card_dual_zero`).
- **Selmer groups.** `LocalConditions ι M` (`Selmer/LocalConditions.lean`) is a subgroup
  `L_v ⊆ H¹(K_v, M)` for each `v ∈ S` and `L_w ⊆ H¹(K_w, M)` for each real `w`; `LocalConditions.dual`
  is the family of orthogonal complements under the local pairings; `LocalConditions.selmerGroup`
  (`Selmer/SelmerGroup.lean`) is the preimage in `H¹(G_S, M)` of the local conditions.
  `GreenbergWilesStatement` (`Selmer/GreenbergWilesStatement.lean`):
  `#Sel_L(M) / #Sel_{L^⊥}(M') = #H⁰(G_S, M)/#H⁰(G_S, M') · ∏_{v ∈ S} #L_v/#H⁰(K_v, M) ·
  ∏_{w real} #L_w/#H⁰(K_w, M) / (#M)^{r₂}`, `r₂` the number of complex places
  (`InfinitePlace.nrComplexPlaces`). Proved: `greenbergWilesStatement` (`Selmer/GreenbergWilesProof.lean`).
  `Selmer/Unramified.lean`: the unramified condition `unramifiedCondition ι M v` (classes vanishing on
  inertia, the local layer's `unramifiedClasses`), `rightOrthogonal_unramifiedCondition` (its
  orthogonal complement is the unramified condition of `M'` when `#M` is a unit at `v`), and
  `LocalConditions.card_selmerGroup_div_card_selmerGroup_dual_of_unramified` (the formula with the
  product only over the places where L_v is not the unramified condition).

## Conventions

- **Which dual.** `M' = Hom(M, μ_N)` with `μ_N = μ_N(K_S)`; `M'` depends on `N`, not only on `M`.
  `X^∨ = Hom(X, ℚ/ℤ)` for the Pontryagin dual of a finite group; the duality map with values in
  `ℤ/N` uses `Hom(·, ℤ/N)`.
- **Which trace.** `trace` is a chosen extension to `Ĥ_c³(G_S, μ_N)` of the sum of the local
  invariants; `trace_localToCompact` is the property that fixes it, and it is unique because the
  local terms surject onto `Ĥ_c³(G_S, μ_N)`.
- **Which invariants.** The local invariants are those of [local Galois cohomology](local.md), in
  the arithmetic normalization; at a real place the invariant takes values in `{0, 1/2}`.
- **Which `Ш`.** `sha` is Шⁿ_S: vanishing at the places of `S` and at the real places only.
- **Real places.** Degree `0` at the real places is Tate's `Ĥ⁰` in Ĥ_c and in `P̂⁰`; the complex
  places contribute nothing to the local terms. In the formula of Greenberg and Wiles each complex
  place contributes `1/#M`.

## What is stated without proof

Every `…Statement` of these directories has a theorem of its type:
`PoitouTateDualityStatement`, `PoitouTateNineTermStatement`, `PoitouTateShaStatement`,
`LocalTateDualityStatement`, `FinitePlacesDualityStatement`, `RootsOfUnityDualityStatement`,
`RootsOfUnityPairingStatement`, `GlobalEulerCharacteristicStatement`, `GreenbergWilesStatement`;
of the two internal statements of `EulerCharacteristic/Internal/`, `ShaTwoBaseCountStatement` is
proved (`shaTwoBaseCount`), and `GlobalEulerCharacteristicBaseStatement` has no theorem of its own
type but follows from it (`globalEulerCharacteristicBase_of_shaTwoBaseCount`) inside the proof of
the formula.

## Why it is built this way

- Each statement is a `Prop` in a file of its own, apart from its proof, and quantifies over all
  number fields of a universe and all `S`, `ι`, `N`, `M`.
- Duality is stated with Tate-modified compact support at the real places, so that the theorems
  hold for even `N` and fields with real places; the case "`N` odd or `K` totally complex" is the
  base case of the proof, not a restriction of the result.
- The Euler characteristic formula is proved after Poitou–Tate duality and the real places in
  degree three, which its proof uses (the multiplicativity of the ratio on short exact sequences);
  the formula of Greenberg and Wiles is proved from the Euler characteristic, the exact sequence of
  a Selmer group (`Selmer/ExactSequence.lean`) and the local counts (`Selmer/LocalCount.lean`).

## Origin of the text

Eighteen of the 30 files of `EulerCharacteristic/` (with `Internal/`) and eight of the 30 of
`PoitouTate/` (with `BaseCase/`) contain text ported from the repository
leanprover-community/riemann-hypothesis (commit `f1f6d65`); `Selmer/` contains none. Each page names
its source, if any, and `licenses/RiemannHypothesis/SOURCE.md` describes the source and the terms of
its use.
