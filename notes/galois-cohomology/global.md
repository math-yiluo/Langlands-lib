# Global Galois cohomology: G_S, cohomology with compact support, the Brauer sequence, dimension and finiteness

This note describes the part of the Library's global Galois cohomology that precedes duality:
the group G_S (`Langlands/Galois/RestrictedRamification/`), the abstract cohomology with compact
support (`Langlands/GaloisCohomology/CompactSupport/`), and the arithmetic of G_S in
`Langlands/GaloisCohomology/Global/`: localization and the groups Шⁿ_S, the `S`-units, the
fundamental exact sequence of the Brauer group, `cd_ℓ(G_S) ≤ 2`, finiteness, the real places in
degrees `≥ 3`, and the characters of G_S. Poitou–Tate duality, the Euler characteristic formula
and Selmer groups are in [Poitou–Tate duality, the Euler characteristic and Selmer groups](poitou-tate.md);
the lower layers are in [profinite groups and fields](profinite-and-fields.md) and
[local fields](local.md); the [overview](overview.md) gives the whole.

## The mathematics

Let `K` be a number field, `Ω` a separable closure and `S` a set of finite places of `K`. The
maximal extension `K_S ⊆ Ω` unramified outside `S` (the infinite places being allowed to ramify, as
in Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, chapter VIII, where `S` contains the
archimedean places) has Galois group G_S. Its cohomology with finite coefficients `M` of order
invertible outside `S` is the subject of Tate's duality theorems (Tate, *Duality theorems in Galois
cohomology over number fields*, 1962; Milne, *Arithmetic Duality Theorems*, I §4;
Neukirch–Schmidt–Wingberg, chapter VIII). The arithmetic inputs are the cohomology of the
`S`-units 𝒪_Sˣ of K_S (`H¹ = Pic(𝒪_S)`, `H²` inside the Brauer group, `H³ = 0` on `ℓ`-primary
parts), the fundamental exact sequence
`0 → Br(K) → ⊕_v Br(K_v) → ℚ/ℤ → 0` with its continuation in higher degrees, Kummer theory and class
field theory. From them: `cd_ℓ(G_S) ≤ 2` when `S` contains the places above `ℓ` and `ℓ` is odd or
`K` totally complex; finiteness of `Hʳ(G_S, M)`; and Tate's theorem that the localization
`Hʳ(G_S, M) → ∏_{w real} Hʳ(K_w, M)` is bijective for `r ≥ 3`.

The duality theorems are proved on an abstract layer that knows no number theory: a compact group
`G` with a family of homomorphisms `φ_v : H_v → G`, its cohomology with compact support (the
cohomology of the mapping cocone of the restriction of cochains), cup products on it and a duality
theorem by dévissage, in two forms: one, and one in which degree `0` at a second family of finite
groups (for G_S: `Gal(ℂ/ℝ)` at the real places) is Tate's `Ĥ⁰`.

## Layout

| Directory or file | Content |
| --- | --- |
| `Langlands/Galois/RestrictedRamification/` | K_S and G_S, extensions unramified outside `S`, open subgroups and finite subextensions, decomposition homomorphisms, embeddings at the places, localization homomorphisms |
| `Langlands/GaloisCohomology/CompactSupport/` | cohomology with compact support relative to a family of homomorphisms: `Basic`, `Functoriality`, `CupProduct`, `OpenSubgroup`, `OpenSubgroupCup`, `DualityMap`, `Duality`, `DualityPrimary`, `BaseCase`, `NineTerm`, `Transport` (transport along isomorphisms of groups); `TateModified/` (the version with Tate's `Ĥ⁰`); `Internal/` (mapping cocones, Leibniz pairings, signs, homotopies; no stability promise) |
| `Langlands/GaloisCohomology/Global/Localization.lean` | localization maps and the groups Шⁿ_S |
| `Langlands/GaloisCohomology/Global/Units/` | `S`-units and divisors of K_S prime to `S`, the `S`-Picard group, capitulation, `H¹`, `H²`, `H³` of the `S`-units and units |
| `Langlands/GaloisCohomology/Global/BrauerSequence/` | the fundamental exact sequence of the Brauer group and its consequences, with `HigherDegrees/` for `H³(Gal(Ω/K), Ωˣ) = 0` and the real places in degrees `≥ 4` |
| `Langlands/GaloisCohomology/Global/Dimension/` | `cd_ℓ(G_S) ≤ 2` (`Statement`, `Proof`) |
| `Langlands/GaloisCohomology/Global/Finiteness.lean` | finiteness of `Hʳ(G_S, M)` |
| `Langlands/GaloisCohomology/Global/RealPlaces/` | the real places in degrees `≥ 3`; vanishing of `Ĥ_cʳ(G_S, M)` for `r ≥ 4` |
| `Langlands/GaloisCohomology/Global/Abelianization.lean`, `Global/Abelianization/` | the characters of G_S by `S`-idèle classes |

Order of dependence: `RestrictedRamification` and `CompactSupport` (independent of each other) →
`Localization` → `Units`, `BrauerSequence` → `Dimension` → `Finiteness` → the vanishing of
Ĥ_cʳ (`RealPlaces/Vanishing*`) → Poitou–Tate duality (`PoitouTate/`, next note) → the real
places in degree three (`RealPlaces/DegreeThreeProof.lean`, which uses the corollaries of
Poitou–Tate) → the Euler characteristic → Selmer groups. `Abelianization` uses
`RestrictedRamification` and the global class field theory of
`Langlands/ClassFieldTheory/Global/Artin/`.

## The objects

- **K_S and G_S** (`Langlands/Galois/RestrictedRamification/MaximalExtension.lean`, namespace
  `Langlands.Galois`): for `K : Type u`, `Ω : Type v` with `Algebra K Ω` and
  `S : Set (HeightOneSpectrum (𝓞 K))`, `maximalUnramifiedOutside K Ω S` is the compositum of the
  finite subextensions of `Ω/K` that are `IsUnramifiedOutside S` (every finite place outside `S` is
  unramified, `Unramified.lean`; the infinite places play no role), and
  `GaloisGroupUnramifiedOutside K Ω S` is `G_S = Gal(K_S/K)`. A number field `L` between `K` and
  K_S is unramified outside `S`, and K_S is also the maximal extension of `L` unramified outside
  the places above `S` (`restrictScalars_maximalUnramifiedOutside`, `OpenSubgroups.lean`).
- **Places** (`PlaceEmbeddings.lean`, `Localization.lean`): `PlaceEmbeddings K Ω` is a choice, for
  every place of `K`, of an embedding of `Ω` into the algebraic closure of the completion;
  `localizationHom ι S v : Gal(K̄_v/K_v) →ₜ* G_S` at a finite place `v` and `realLocalizationHom ι S w`
  at an infinite place `w`.
- **Localization and `Ш`** (`Langlands/GaloisCohomology/Global/Localization.lean`, namespace
  `Langlands.GaloisCohomology`): `localModule ι M v`, `realLocalModule ι M w`, `localization ι M v n`,
  `realLocalization ι M w n`; `sha ι M n = Шⁿ_S(M)`, the classes of `Hⁿ(G_S, M)` vanishing **at the
  places of `S` and at the real places**; `sha_eq`: it does not depend on `ι`. `absoluteSha ι A n` is
  the version for `Gal(Ω/K)` and all finite and real places.
- **Cohomology with compact support** (`Langlands/GaloisCohomology/CompactSupport/Basic.lean`): for
  `φ v : H v →ₜ* G`, a smooth `G`-module `A`, smooth `H v`-modules `Aᵥ v` and
  `a v : Rep.res (φ v) A ⟶ Aᵥ v` (all in one universe), `localRes` is the restriction of cochains,
  `compactSupportCochains` its mapping cocone and `compactSupportCohomology φ A Aᵥ a n` its cohomology,
  with `compactSupportCohomologyRes` for the local modules the restrictions; `compactToGlobal`,
  `globalToLocal`, `localToCompact` form the long exact sequence
  (`compactSupportCohomology_exact_global`, `compactSupportCohomology_exact_local`,
  `compactSupportCohomology_exact_compact`). `TateModified/Basic.lean` adds a family of finite groups
  with norm cochains in degree `0` (`tateCompactCochains`, `tateCompactCohomologyRes`).

## Main theorems

**The abstract duality** (`CompactSupport/`). `compactDualityMap` (`DualityMap.lean`) is the cup
product with the evaluation `M ⊗ Hom(M, D) → D` followed by a trace `t : H_c^m(G, D) → ℤ/n`.
`CompactGroupDualityHypotheses.bijective_compactDualityMap` (`Duality.lean`): under
`CompactGroupDualityHypotheses` (`D ≅ ℤ/n`, `H_c⁴ = 0` for modules killed by `n`, duality for the
modules coinduced from `ℤ/n` on the open subgroups below some `U₀`), the duality map
`Hʳ(G, Hom(M, D)) → Hom(H_cˢ(G, M), ℤ/n)`, `r + s = 3`, is bijective for every finite smooth `M`
killed by `n`; `bijective_compactDualityMap_of_primePow` reduces to prime powers.
`TateCompactDualityHypotheses.bijective_tateCompactDualityMap` is the Tate-modified form, for
`s ≥ 1`. `PoitouTateDualityHypotheses.isNineTermExact` (`NineTerm.lean`) and
`TatePoitouTateHypotheses` with `IsTateNineTermExact` (`TateModified/NineTerm.lean`) give the
nine-term sequence from duality, finiteness and `H³ = 0`.

**`S`-units** (`Global/Units/`; `F, Ω : Type u`, `Ω/F` Galois and separably closed).
- `cohomologyOneSUnitsPicardEquiv : H¹(G_S, 𝒪_Sˣ) ≃+ SPicardGroup S` for **every** set `S` of finite
  places (`Units/PicardCapitulation.lean`); `SPicardGroup S` is `Pic(𝒪_S)`, the divisors prime to `S`
  modulo principal divisors, finite and killed by the class number (`Units/Picard.lean`). The
  surjectivity comes from the capitulation of the divisors of K_S prime to `S` at finite levels
  (`Units/CapitulationPrincipalIdeal.lean`), which uses the principal ideal theorem of the NYLL copy
  through `Langlands/ClassFieldTheory/Global/Artin/PrincipalIdeal.lean`.
- `maximalSUnitsPrimaryEquiv` (`Units/Brauer.lean`): for a prime `ℓ` such that `S` contains the places
  above `ℓ`, the `ℓ`-primary part of `H²(G_S, 𝒪_Sˣ)` is isomorphic to the `ℓ`-primary Brauer classes
  of `K` vanishing at every finite place outside `S`.
- `eq_zero_of_cohomology_three_maximalSUnits` (`Units/HighDegree.lean`): under the same condition,
  `H³(G_S, 𝒪_Sˣ)(ℓ) = 0`.

**The Brauer sequence** (`Global/BrauerSequence/`). `BrauerSequenceData K Ω ι` (`Statement.lean`,
for `K, Ω : Type u`, `Ω` a separable closure, `ι : PlaceEmbeddings K Ω`) collects: a class of
`H²(Gal(Ω/K), Ωˣ)` is nonzero at finitely many finite places, is zero if all its localizations are
zero, and the sum of its local invariants (`localInvariant`, `realLocalInvariant`) is zero; a family
of local classes with finite support and sum of invariants zero comes from a unique global class;
`H³(Gal(Ω/K), Ωˣ) = 0`; for `r ≥ 4` localization to the real places is bijective; a class killed by
`m` with trivial real localizations dies in every finite extension whose local degrees above its
support are multiples of `m`; and cyclic extensions with prescribed local degrees exist.
`BrauerSequenceStatement` asserts it for every `K`, `Ω`, `ι`, and it is proved:
`brauerSequenceStatement` (`HigherDegrees.lean`), from `unitsCohomologyHigherDegreesStatement`
(`UnitsCohomologyHigherDegreesStatement`, `Proof.lean`). Consequences in `Statement.lean`:
`BrauerSequenceData.brauerLocalization_injective`, `BrauerSequenceData.eq_zero_iff_localInvariant`,
`BrauerSequenceData.exists_brauerLocalization_eq`.

**Dimension and finiteness.**
- `CohomologicalDimensionStatement` (`Global/Dimension/Statement.lean`): for every number field `K`,
  separable closure `Ω` (one universe), set `S` of finite places and prime `ℓ` such that every finite
  place above `ℓ` lies in `S` and `ℓ ≠ 2` or `K` is totally complex,
  `cd ℓ (GaloisGroupUnramifiedOutside K Ω S) ≤ 2`. Proved: `cohomologicalDimensionStatement`
  (`Dimension/Proof.lean`). `S` need not be finite.
- `finite_cohomology_of_le_two` (`Global/Finiteness.lean`): for finite `S` and a finite smooth
  G_S-module `M` such that the places above `#M` lie in `S`, `Hʳ(G_S, M)` is finite for `r ≤ 2`;
  `finite_cohomology_of_odd_or_isTotallyComplex`: in every degree when `#M` is odd or `K` totally
  complex.

**The real places.**
- `RealLocalizationDegreeThreeStatement` (`Global/RealPlaces/HighDegree.lean`): for finite `S` and a
  finite smooth `M` killed by `n ≠ 0` with the places above `n` in `S`, the localization
  `H³(G_S, M) → ∏_{w real} H³(K_w, M)` is bijective. Proved: `realLocalizationDegreeThreeStatement`
  (`RealPlaces/DegreeThreeProof.lean`), and from it `bijective_realLocalization` (Tate's
  theorem, every `r ≥ 3`, the places above `#M` in `S`) and `realLocalizationEquiv`.
- `TateCompactSupportVanishingStatement` (`RealPlaces/VanishingStatement.lean`): under the same
  hypotheses, `Ĥ_cʳ(G_S, M) = 0` for `r ≥ 4` (`PoitouTate.compactCohomology`). Proved:
  `tateCompactSupportVanishingStatement` (`RealPlaces/VanishingProof.lean`).

**Characters of G_S** (`Global/Abelianization.lean`; `K : Type u`, `Ω : Type v` a separable
closure, `S` finite, `n ≠ 0`).
- `continuousCharEquivNarrowSIdeleClass`: continuous characters `G_S → ℤ/n` correspond to
  homomorphisms from the narrow `S`-idèle class group `NarrowSIdeleClassGroup S = I_K / K^× U^S_+` to
  `ℤ/n`, with no condition on `n` or on the real places.
- `continuousCharEquivSIdeleClass`: if `n` is odd or `K` totally complex, the same with
  `SIdeleClassGroup S = I_K / K^× U^S`.

## Conventions

- `S` is a set of **finite** places; the real places are always added in the local terms (`sha`,
  the localizations, the compact support of `PoitouTate.compactCohomology`), and ramification at the
  infinite places is allowed in K_S.
- The coefficient modules are `Rep (ULift ℤ) G_S`, and the global statements quantify over
  `K, Ω : Type u` in one universe `u`; G_S itself is defined for `K : Type u`, `Ω : Type v`.
- The local invariants at the finite places are those of [local Galois cohomology](local.md)
  (arithmetic normalization), read on the completions with the structure
  `Langlands.Global.FiniteCompletion.valuativeRel`; at a real place the invariant is
  `realInvariant`, with values in `{0, 1/2}`.
- The characters of G_S are matched with idèle classes through the Library's global Artin map
  `Langlands.ClassFieldTheory.Global.Artin.geometricArtinMap`, which is in the **geometric**
  normalization (a uniformizer at an unramified place goes to the inverse of the arithmetic
  Frobenius); the two equivalences use only kernels and images, the value lemmas
  `continuousCharEquivNarrowSIdeleClass_mk`, `continuousCharEquivSIdeleClass_mk` use the
  normalization. `Global/Abelianization/ArtinFrobenius.lean` relates the arithmetic Artin lifts of
  the local layer to geometric Frobenius lifts (`isGeometricFrobeniusLift_inv_of_isArithmeticArtinLift`).

## What is stated without proof

Every `…Statement` of these directories has a theorem of its type: `BrauerSequenceStatement`,
`UnitsCohomologyHigherDegreesStatement`, `CohomologicalDimensionStatement`,
`RealLocalizationDegreeThreeStatement`, `TateCompactSupportVanishingStatement`. The structures
`CompactDualityHypotheses`, `CompactGroupDualityHypotheses`, `BaseDualityHypotheses`,
`TateCompactDualityHypotheses`, `PoitouTateDualityHypotheses` and `TatePoitouTateHypotheses` are
hypotheses of the abstract layer; they are supplied for G_S in
`Langlands/GaloisCohomology/Global/PoitouTate/` (see the next note).

## Why it is built this way

- The proof of Poitou–Tate has an abstract layer (a group with a family of homomorphisms, compact
  support as a mapping cocone, dévissage) and an arithmetic layer that supplies its hypotheses for
  G_S. The abstract layer is in `Langlands/GaloisCohomology/CompactSupport/` because only the
  global theory uses it; it speaks of no field.
- The cones are built from explicit pairs of cochains, so that cup products on cones can be written
  with their signs (`Internal/`); these files are internal.
- The real places are handled by a second, Tate-modified, theory of compact support rather than by
  restricting to odd `N` or totally complex fields, so that the main theorems carry no parity
  condition.

## Origin of the text

Text is ported from the repository leanprover-community/riemann-hypothesis (commit `f1f6d65`) in
all files of `RestrictedRamification/` and `CompactSupport/`, in `Global/Localization.lean` and
`Global/Finiteness.lean`, and in most files of `Global/Units/` (13 of 16) and `Global/RealPlaces/`
(8 of 11) and one of `Global/Dimension/`; `Global/BrauerSequence/` and the characters of G_S
(`Global/Abelianization.lean`, `Global/Abelianization/`) contain none. Each page names its source or
says that it contains no text of the source, and `licenses/RiemannHypothesis/SOURCE.md` describes the source and the
terms of its use.
