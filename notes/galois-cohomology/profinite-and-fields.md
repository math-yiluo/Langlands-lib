# Cohomology of profinite groups and Galois cohomology of fields

This note describes the two lower layers of the Library's Galois cohomology: the cohomology of a
topological group with smooth coefficients (`Langlands/Cohomology/Profinite/`, namespace
`Langlands.ProfiniteCohomology`) and the Galois cohomology of an arbitrary field
(`Langlands/GaloisCohomology/Field/`, namespace `Langlands.GaloisCohomology`). The layers above are
described in [local Galois cohomology](local.md), [global Galois cohomology](global.md) and
[Poitou–Tate duality, the Euler characteristic and Selmer groups](poitou-tate.md); the
[overview](overview.md) gives the whole.

## The mathematics

For a profinite group `G` and a discrete `G`-module `A` (every element fixed by an open
subgroup), `Hⁿ(G, A)` is the cohomology of the complex of continuous inhomogeneous cochains
`Gⁿ → A`; with discrete values, continuous means locally constant. This is the definition of Serre
(*Galois Cohomology*, I §2.2) and of Neukirch–Schmidt–Wingberg (*Cohomology of Number Fields*,
I §2), and it agrees with the colimit of the cohomology of the finite quotients G/U with
coefficients `A^U`. The first layer develops the standard theory on this model: functoriality
along continuous homomorphisms, the long exact sequence, Shapiro's lemma, corestriction,
inflation–restriction with the five-term sequence and transgression, cup products, the Mackey
formula, cohomological dimension with pro-`p` and pro-Sylow subgroups, the Euler–Poincaré
characteristic, class formations with Tate's theorem, and duality for a group with a dualizing
module of finite level (the abstract form of local Tate duality).

The second layer applies it to `Gal(L/K)` for an extension of fields, with the coefficient modules
`L`, `Lˣ` and `μ_n(L)`: Hilbert's theorem 90 in its additive and multiplicative forms, Kummer
theory, the Brauer group `Br(K) ≅ H²(Gal(Ksep/K), Ksepˣ)`, its description by finite levels, the
Cartier dual, and the cup product of a character with a unit.

## Layout

`Langlands/Cohomology/Profinite/`:

| Files | Content |
| --- | --- |
| `SmoothCoefficients.lean` | the class `IsSmoothRep` of smooth objects of Mathlib's `Rep k G` |
| `Cochains.lean`, `Functoriality.lean`, `LongExactSequence.lean`, `LowDegree.lean`, `OpenNormal.lean` | the cochain model, `map`, `res`, `infl`, the connecting map `δ`, `H⁰` |
| `Comparison/` | comparison with Mathlib's `groupCohomology` and `continuousCohomology`, with the colimit over finite quotients, with directed unions of coefficients |
| `Coinduced/`, `Shapiro.lean`, `Corestriction.lean` | smooth coinduced modules, their acyclicity, Shapiro's lemma, corestriction |
| `InflationRestriction/` | degree one, the five-term sequence, transgression, higher degrees |
| `Cup/` | cup products, their naturality, graded commutativity, connecting maps, the projection formula |
| `Characters.lean`, `TorsionDual.lean`, `Cyclic/` | characters with values in ℚ/ℤ, `H¹(G, ℚ/ℤ)` and `H²(G, ℤ)`, cup products with a character |
| `Mackey/`, `InnerConjugation.lean` | the Mackey decomposition and formula; inner conjugation acts trivially |
| `Dimension/` | supernatural numbers, pro-`p` and pro-Sylow subgroups, `cd` and `scd`, closed subgroups, procyclic groups |
| `EulerCharacteristic.lean` | the Euler–Poincaré characteristic |
| `ClassFormation/` | class formations, fundamental classes, corestriction, Tate's theorem, vanishing in degree `≥ 3` |
| `Duality/` | dual modules, dualizing data, the duality map, dévissage, the duality theorem |

`Langlands/GaloisCohomology/Field/`: `Modules.lean` (the Galois modules), `OpenSubgroup.lean`
(open subgroups of `Gal(L/K)` and finite subextensions), `Hilbert90.lean`,
`AdditiveHilbert90.lean`, `FiniteLevel.lean`, `KummerSequence.lean`, `Brauer.lean`,
`CartierDual.lean`, `CyclicCup.lean`, `RelativeInflation.lean`.

The order of dependence is: Mathlib and the Library's smooth representations
(`Langlands/Representation/Smooth/Definitions.lean`, `Langlands/Representation/Category/Basic.lean`),
its continuous and Tate cohomology (`Langlands/Cohomology/Continuous/`, `Langlands/Cohomology/Tate/`)
and `Langlands/ClassFieldTheory/Local/Cohomology.lean` (for ℚ/ℤ and `IntegerScalars`) →
`Cohomology/Profinite` → `GaloisCohomology/Field` → the local and global layers. The profinite
layer states nothing about fields.

## Conventions

- **Coefficients.** A coefficient module is an object `A : Rep k G` of Mathlib's category of
  representations with the class `Langlands.IsSmoothRep A`, which is the Library's
  `Langlands.IsSmooth A.ρ` (every vector is fixed by an open subgroup); `isSmoothRep_iff_isOpen_stabilizer`
  says it is the openness of every stabilizer. The cohomology functor is defined on the Library's
  category `Langlands.SmoothRep k G`. Abelian groups are modules over `ULift ℤ` (in the Galois
  layers through `Langlands.ClassFieldTheory.Local.IntegerScalars`, which is `ULift ℤ`), so that
  the ring, the group and the module live in **one universe** `u`: `cochains`, `cohomology` and
  every construction of the layer take `k G : Type u` and `A : Rep.{u} k G`.
- **The cochain model.** `Langlands.ProfiniteCohomology.cohomology A n : ModuleCat k` is the
  cohomology of `cochains A`, the subcomplex of locally constant cochains of Mathlib's
  `groupCohomology.inhomogeneousCochains A` (`Cochains.lean`). It is related to the other models by
  three isomorphisms, which are part of the interface:
  `isoGroupCohomology` (with Mathlib's `groupCohomology`, for a discrete group),
  `isoContinuousCohomology` (with Mathlib's `continuousCohomology` of a discrete topological
  representation of a locally compact group; natural by `isoContinuousCohomology_naturality`) and
  `isoFiniteQuotientCohomology` (with the Library's `Langlands.Continuous.finiteQuotientCohomology`,
  the colimit over open normal subgroups, for a compact totally disconnected group).
- **ℚ/ℤ.** `Langlands.ClassFieldTheory.Local.RationalModIntegers` is `ℚ` modulo the integers;
  `Langlands.ProfiniteCohomology.QZ` is the same type with the discrete topology, so that continuous
  homomorphisms to it are the characters with open kernel.
- **Maps.** There is one functoriality, `map φ f n : Hⁿ(G, A) ⟶ Hⁿ(H, B)` for a continuous
  homomorphism `φ : H →ₜ* G` and a morphism `f : Rep.res φ A ⟶ B` (a compatible pair);
  coefficient maps (`coeffMap`), restriction (`res`, `resOfLE`) and inflation (`infl`) are special
  cases of it.
- **Signs.** The cup product of cochains is `(f ∪ g)(x₁,…,xₙ) = f(x₁,…,x_p) ⊗ (x₁⋯x_p)·g(x_{p+1},…,xₙ)`
  (`Cup/Cochains.lean`, the Library's `Langlands.Tate.ordinaryCochainCup`). Graded commutativity
  carries the sign `(-1)^{pq}` through the braiding `A ⊗ B ≅ B ⊗ A` (`coeffMap_braiding_cup`).

## Main definitions and theorems: profinite groups

All are in `Langlands.ProfiniteCohomology` unless written otherwise; `G` is a topological group
in universe `u` with `IsTopologicalGroup G`, `k` a commutative ring, `A` a smooth `G`-module.

**Foundations.**

- `cochains A`, `cocycles A n`, `cohomology A n` (`Langlands/Cohomology/Profinite/Cochains.lean`);
  `cohomologyFunctor k G n : SmoothRep k G ⥤ ModuleCat k` (`Functoriality.lean`).
- `δ hS i j hij : Hⁱ(G, X₃) ⟶ Hʲ(G, X₁)` for a short exact sequence `S` of smooth modules and
  `i + 1 = j`, with exactness at the three places (`cohomology_exact₁`, `cohomology_exact₂`,
  `cohomology_exact₃`) and naturality (`δ_naturality`) (`LongExactSequence.lean`).
- `zeroIso A : H⁰(G, A) ≅ A^G` (`LowDegree.lean`).
- `isoGroupCohomology A n` (`[DiscreteTopology G]`, `Comparison/Discrete.lean`);
  `isoContinuousCohomology X n` (`[LocallyCompactSpace G]`, `X : TopRep k G` discrete with smooth
  underlying representation, `Comparison/Continuous.lean`); `isoFiniteQuotientCohomology A n`
  (`[CompactSpace G] [TotallyDisconnectedSpace G]`, `Comparison/FiniteQuotients.lean`).

**Shapiro, corestriction, inflation–restriction** (`G` compact).

- `shapiroIso U B n : Hⁿ(G, Coind_U^G B) ≅ Hⁿ(U, B)` for an open subgroup `U` and a smooth
  `U`-module `B`, with Mathlib's coinduced representation `Rep.coind` (`Shapiro.lean`).
- `cores U A n : Hⁿ(U, A) ⟶ Hⁿ(G, A)` and `res_comp_cores`: restriction followed by corestriction is
  multiplication by `[G : U]` (`Corestriction.lean`).
- `fiveTerm_exact`: for `G` compact and totally disconnected, `N` a closed normal subgroup,
  `0 → H¹(G/N, A^N) → H¹(G, A) → H¹(N, A)^G → H²(G/N, A^N) → H²(G, A)` is exact, the third map
  being the transgression (`InflationRestriction/FiveTerm.lean`, `InflationRestriction/Transgression.lean`).
- `range_infl_eq_ker_res` and `infl_injective_of_isZero`: for `G` compact and totally
  disconnected, if `Hⁱ(N, A) = 0` for `0 < i < q` (`q ≠ 0`, `N` closed normal), then `0 → H^q(G/N, A^N) → H^q(G, A) → H^q(N, A)` is exact
  (`InflationRestriction/Higher.lean`).

**Cup products** (`Cup/`).

- `cup h : Hᵖ(G, A) →ₗ[k] H^q(G, B) →ₗ[k] Hⁿ(G, A ⊗ B)` for `h : p + q = n`, with the unit class
  (`cohomologyMap_leftUnitor_unitClass_cup`, `cohomologyMap_rightUnitor_cup_unitClass`), naturality
  (`cohomologyMap_tensorHom_cup`), compatibility with connecting maps
  (`δ_cup_of_shortExact_tensorRight`), the projection formula `cores_cup_res` and, for `G`
  compact, graded commutativity `coeffMap_braiding_cup`. `cupPairing μ h` is the cup product
  followed by a morphism `μ : A ⊗ B ⟶ C`.

**Characters** (`Characters.lean`, `Cyclic/`). `cohomologyTwoIntAddEquiv`:
`H²(G, ℤ) ≃+ (Additive G →ₜ+ QZ)`, through the connecting map of `0 → ℤ → ℚ → ℚ/ℤ → 0`, for
`G : Type` compact and totally disconnected (`Hⁿ(G, ℚ) = 0` for `n ≥ 1`; the coefficients are
Mathlib's `ℤ`, hence the universe `0`). For a procyclic group with a topological generator `σ` of
`ℤ̂`-type (`IsZHatGenerator σ`: `σ` generates a dense subgroup and every `ℤ/n` is a quotient by an
open subgroup with `σ ↦ 1`): `IsZHatGenerator.isZero_cohomology_two` (`H²(G, A) = 0` for torsion
`A`, `G` compact) and `cohomologyTwoIntAddEquivQZ : H²(G, ℤ) ≃+ QZ` (for `G : Type` compact and
totally disconnected) (`Dimension/Procyclic.lean`).

**Mackey and conjugation.** `mackeyCohomologyEquiv`: for an open subgroup `V` of a compact `G`, a
continuous `ι : H →ₜ* G` from a compact group and a smooth `V`-module `N`,
`Hⁿ(H, Res_ι Coind_V^G N)` is the product over the double cosets `V\G/ι(H)` of the cohomology of
the groups `ι⁻¹(x⁻¹Vx)` (`Mackey/Cohomology.lean`). `cohomologyInnerConj_eq_id`: inner conjugation
acts as the identity on `Hⁿ(G, A)` for compact `G` (`InnerConjugation.lean`).

**Cohomological dimension** (`Dimension/`). For a prime `p`, `cd p G : ℕ∞` is characterized by
`cd_le_iff`: `cd p G ≤ n` iff the `p`-primary part of `H^q(G, A)` vanishes for every `q > n` and
every smooth **torsion** module `A : Rep (ULift ℤ) G`; `scd p G` is the same without the torsion
condition (`scd_le_iff`); `cdSup G`, `scdSup G` are the suprema over the primes
(`Dimension/Basic.lean`). For `G` compact: `cd_le_iff_forall_simple` (it suffices to test the simple
smooth modules killed by `p` in degree `n + 1`), `cd_closedSubgroup_le` (`cd p H ≤ cd p G` for a
closed subgroup `H`), `cd_eq_of_isProSylow` (equality for a pro-`p` Sylow subgroup); pro-Sylow
subgroups (`IsProSylow`, closed pro-`p` subgroups of index prime to `p` in the sense of
supernatural numbers) exist (`exists_isProSylow`, `Dimension/ProP.lean`).

**Euler–Poincaré characteristic** (`EulerCharacteristic.lean`). `eulerCharacteristic A : ℚ` is
`|H⁰| · |H²| / |H¹|` (`eulerCharacteristic_eq`). `HasFiniteCohomology k G P` says that every finite
smooth module whose order satisfies `P` has finite cohomology vanishing in degrees `≥ 3`; under it,
`eulerCharacteristic_shortExact` gives multiplicativity in short exact sequences of finite modules.

**Class formations** (`ClassFormation/`). `PreClassFormation C` is a family of homomorphisms
`inv U : H²(U, C) →+ QZ` over the open subgroups, with `H¹(U, C) = 0` and `inv_V ∘ res = [U : V] · inv_U`;
`ClassFormation C` asks the `inv U` to be bijective, `ClassFormation.At P C` only injective with
image containing the `p`-primary part for `p ∈ P`. `ClassFormation.invEquiv_res` is the restriction
law. `ClassFormation.subsingleton_cohomology_top_of_three_le`: for `G` compact and totally
disconnected and `C : Rep (ULift ℤ) G` a class formation, `Hʳ(G, C) = 0` for `r ≥ 3`
(`ClassFormation/HighDegree.lean`). Tate's theorem for a finite group is
`GroupCoh.exists_cupH_of_tate` (`ClassFormation/TateTheorem.lean`, in Mathlib's `groupCohomology`).

**Duality** (`Duality/`). For a compact `G`, `n` and a smooth `D : Rep (ULift ℤ) G`,
`DualizingData n D` (`Duality/DualModule.lean`) is: `D ≃+ ℤ/n`; finiteness of `Hʳ(U, M)` for
`r ≤ 2` and vanishing of `H³(U, M)` for every open `U` and finite smooth `U`-module `M` killed by
`n`; isomorphisms `t U : H²(U, D) ≃+ ℤ/n` compatible with corestriction; and perfectness of the cup
product pairing `H¹(U, ℤ/n) × H¹(U, D) → H²(U, D) ≅ ℤ/n` for every open `U`. Then
`DualizingData.dualityMap_bijective`: for every open `U`, every finite smooth `U`-module `M`
killed by `n` and `r + s = 2`, the duality map `Hʳ(U, M) → Hom(Hˢ(U, Hom(M, D)), ℤ/n)` is
bijective; `DualizingData.dualityMap_bijective_of_group` is the case `U = G` (`[NeZero n]`)
(`Duality/Main.lean`). The proof is the dévissage of `Duality/Devissage.lean` through coinduced
modules.

## Main definitions and theorems: fields

`K L : Type u` are fields with `Algebra K L`; `Gal(L/K)` carries its Krull topology.

- `unitsModule K L`, `rootsOfUnityModule K L n`, `additiveModule K L` (`Field/Modules.lean`):
  `Lˣ` (written additively; the Library's `Langlands.ClassFieldTheory.Local.unitsRepresentation`),
  `μ_n(L)` and `L` as representations of `Gal(L/K)`; they are smooth when L/K is algebraic.
- `subsingleton_cohomology_one_unitsModule`: Hilbert 90, `H¹(Gal(L/K), Lˣ) = 0` for L/K Galois
  (`Field/Hilbert90.lean`); `subsingleton_cohomology_additiveModule`: `Hⁿ(Gal(L/K), L) = 0` for
  `n ≠ 0` and L/K Galois (`Field/AdditiveHilbert90.lean`).
- `exists_brauerInflation_eq` and `brauerInflation_injective` (`Field/FiniteLevel.lean`): for L/K
  Galois, every class of `H²(Gal(L/K), Lˣ)` is inflated from a finite Galois subextension `E`, and inflation from
  `H²(Gal(E/K), Eˣ)` (Mathlib's `groupCohomology`) is injective.
- `kummerEquiv : H¹(Gal(L/K), μ_n) ≃+ Kˣ/Kˣⁿ` and `kummerH2Equiv : H²(Gal(L/K), μ_n) ≃+` the
  `n`-torsion of `H²(Gal(L/K), Lˣ)`, for a separable closure `L` of `K` and `(n : K) ≠ 0`
  (`Field/KummerSequence.lean`).
- `Langlands.GaloisCohomology.brauerEquiv : BrauerGroup K ≃+ H²(Gal(L/K), Lˣ)` for a separable closure
  `L` (`[IsSepClosure K L]`), with Mathlib's `BrauerGroup` (`Field/Brauer.lean`).
- `cartierDual K L M = Hom(M, Lˣ)` with the action `(σf)(m) = σ f(σ⁻¹m)` and the Cartier pairing
  (`Field/CartierDual.lean`); it is the dual module of `Duality/DualModule.lean` with values in the
  units, so the abstract duality theorem applies to it.
- `Field/CyclicCup.lean`: for a continuous character `χ` and `a ∈ Kˣ`, the class `δχ ∪ a ∈ H²(Gal(L/K), Lˣ)`
  vanishes iff `a` is a norm from the cyclic extension cut out by `χ`.
- `Field/RelativeInflation.lean` describes, in the cochain model, the Library's inflation of relative
  classes `Langlands.BrauerComparison.relativeToContinuous`, on which the local invariant is computed.

## What is stated without proof

Nothing in these two layers is a `…Statement` without a proof. `DualizingData`,
`HasFiniteCohomology`, `ClassFormation` and `GroupDualityHypotheses` (`Duality/Devissage.lean`)
are hypotheses of abstract theorems; they are supplied for local fields in the local layer
(`Langlands.GaloisCohomology.Local.classFormation`, the dualizing data of μ_n).

## Why this model

- The coefficients are the Library's own smooth representations on Mathlib's `Rep`, not a new
  notion, so that the representation theory of the Library and its Galois cohomology speak of the
  same objects.
- The locally constant cochains give explicit cocycles, which the cup symbol, the local invariant
  and the cones of cohomology with compact support need; Mathlib's `continuousCohomology` and the
  Library's colimit over finite quotients are reached through the comparison isomorphisms rather
  than replaced, and the Library's Tate cohomology (`Langlands/Cohomology/Tate/`) and Brauer
  comparison (`Langlands/Algebra/BrauerComparison/`) are used rather than duplicated.
- No class field theory is built here: the invariant of a local field and the local Artin map come
  from the Library's class field theory (see [local Galois cohomology](local.md) and
  [class field theory through the copies](../class-field-theory/through-the-copies.md)).

## Origin of the text

Most files of the two layers (49 of the 53 of `Cohomology/Profinite/`, 8 of the 10 of
`GaloisCohomology/Field/`) are ported from the repository leanprover-community/riemann-hypothesis
(commit `f1f6d65`), with the coefficient class renamed to `IsSmoothRep`; each page names its source
file, or says that it contains no text of the source, and
`licenses/RiemannHypothesis/SOURCE.md` describes the source and the terms of its use.
