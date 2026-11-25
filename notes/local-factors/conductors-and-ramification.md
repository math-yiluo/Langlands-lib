# Conductors and ramification: integrality, Herbrand functions, Hasse–Arf and the FontaineWintenberger bridges

This note describes `Langlands/LocalFactor/Ramification/` (namespaces `Langlands.Ramification`,
`Langlands.Ramification.Padic`, `Langlands.Ramification.Local`, `Langlands.Ramification.Kummer`,
`Langlands.Ramification.HerbrandBridge`, `Langlands.Ramification.Wintenberger`) with the Weil-group
level of the conductor in `Langlands/LocalFactor/Ramification/WeilExponent.lean` and
`Langlands/Correspondence/`.

## The mathematics

A finite Galois extension L/K of local fields has the lower ramification groups `G_i`, the
kernels of the action of `G = Gal(L/K)` on `𝒪_L/𝔪^{i+1}`. The Artin conductor of a
representation `ρ` of `G` is `a(ρ) = Σ_{i≥0} |G_i|/|G_0| · codim V^{G_i}` and the Swan conductor the
same sum over `i ≥ 1`; Artin's theorem says they are natural numbers (Serre, *Local Fields*, VI §2,
Theorem 1′). The Herbrand function `φ_{L/K}` renumbers the filtration (upper numbering
`G^{φ(i)} = G_i`), compatibly with quotients (Herbrand's theorem), which makes the upper filtration
of an infinite Galois extension, in particular of `Gal(Ksep/K)`, meaningful (Serre, IV §3). The
Hasse–Arf theorem says that for abelian `G` the jumps of the upper filtration are integers. Through
finite inertia presentations these notions pass to representations of the Weil group, whose Artin
and Swan exponents are natural numbers with `a = dim V − dim V^I + sw` (Deligne, *Les constantes
des équations fonctionnelles des fonctions L*, §4.5). Wintenberger's field of norms identifies the
absolute Galois group of an infinite arithmetically profinite extension of a `p`-adic field with
that of a Laurent series field, with the upper filtrations matched by a function `ψ`; this gives
the close-fields comparison of Deligne (*Les corps locaux de caractéristique p, limites de corps
locaux de caractéristique 0*, §3.5).

## Layout

| Files | Content |
| --- | --- |
| `Filtration.lean`, `LowerGroup.lean`, `LowerGroupQuotients.lean`, `Uniformizer.lean`, `Depth.lean`, `FixedSubring.lean`, `FixedSubringQuotient.lean`, `FixedSubringValuation.lean`, `DifferentFiltration.lean`, `Monogenic.lean`, `SeparableResidueField.lean` | lower ramification groups of a group acting on a local ring or a discrete valuation ring, their quotients, the uniformizer test, depths, fixed subrings, the different |
| `Conductor.lean`, `ConductorFunctional.lean`, `ArtinCharacter.lean`, `CharacterConductorSum.lean` | the Artin and Swan expressions of a representation of a finite group acting on a local ring, the conductor as a functional of the character, the Artin and Swan characters |
| `Galois.lean`, `LocalGalois.lean` | the action of `Gal(L/K)` on the integers: for `p`-adic fields (`Langlands.PadicField` with `Langlands.PadicField.TopologicalData`) and, in `Langlands.Ramification.Local`, for nonarchimedean local fields of any characteristic |
| `FiniteStatement.lean` and the proof files beside it (`FiniteIntegralityProof.lean`, `FiniteFormalPropertiesProof.lean`, `FiniteExactSequenceProof.lean`, `InductionProof.lean`, `InflationProof.lean`, `ConductorDiscriminantProof.lean`, …) | the finite-Galois conductor of a `p`-adic extension: integrality and the formal properties |
| `ArtinExponent.lean`, `InducedRankOneDifference.lean`, `RankOneConductorIntegrality.lean`, `RankOneArtinSum.lean` | integrality for the inertia group and without the Galois hypothesis; the rank-one and induced cases used by the proof |
| `InertiaPresentation*.lean`, `InertiaConductor*.lean`, `Breaks.lean`, `WeilBreakStatement.lean`, `WeilExponent.lean`, `LocalInertiaPresentationStatement.lean`, `LocalWeilBreakStatement.lean` | finite inertia presentations of representations of the Weil group, their conductors and breaks; the Weil-group exponents |
| `Herbrand/` (50 files) | Herbrand functions `φ`, `ψ` and upper groups, finite and absolute, `p`-adic (`Herbrand/Finite.lean`, `Herbrand/Absolute.lean`) and in either characteristic (`Herbrand/GeneralFinite.lean`, `Herbrand/GeneralAbsolute.lean`); Herbrand's quotient, subgroup and tower theorems; the Kummer tower; truncation quotients; Hasse–Arf for `p`-adic fields (`Herbrand/HasseArfProof.lean`) |
| `HasseArf/` | the Hasse–Arf theorem for a finite abelian group acting on a discrete valuation ring |
| `Wintenberger/` | the bridges to the FontaineWintenberger copy |
| `CloseFieldsStatement.lean`, `CloseFieldsGaloisQuotientProof.lean`, `CloseFieldsWeilQuotientProof.lean` | the close-fields comparison |

## Main definitions and theorems

**Lower groups and conductors.** `Langlands.Ramification.lowerGroup R G i` (`Filtration.lean`) is the
kernel of the action on `R/𝔪^{i+1}`, `i : ℕ`, and `Langlands.Ramification.lowerGroupInt` the version
with integer index (the whole group below `0`). `Langlands.Ramification.artinConductor R G ρ` and
`Langlands.Ramification.swanConductor R G ρ` (`Conductor.lean`) are the rational sums above, for a
finite group acting faithfully on a Noetherian local ring; `Langlands.Ramification.Padic.artinConductor`
specializes them to the ring of integers (`Langlands.PadicField.TopologicalData.Integers`) of a
`p`-adic field `F : PadicField p` with supplied data `T` (`Langlands.PadicField.TopologicalData`) and a base `K` between `ℚ_p` and `F` (`Galois.lean`), and
`Langlands.Ramification.Padic.lowerRamificationGroup T K i` is the lower group there.

**Integrality, finite level.**
- `Langlands.Ramification.Padic.finiteGaloisConductorIntegrality` (`FiniteIntegralityProof.lean`)
  proves `FiniteGaloisConductorIntegralityStatement` (`FiniteStatement.lean`): for a prime `p`, a
  `p`-adic field `F : PadicField.{uL} p` with `T`, a field `K : Type uK` in the tower `ℚ_p → K → F`
  and a finite-dimensional complex `V : Type uV` (three independent universes), if F/K is Galois
  then for every representation `ρ` of `F ≃ₐ[K] F` on `V` the Artin and Swan expressions are natural
  numbers.
- `ArtinExponent.lean` removes the Galois hypothesis and passes to the inertia group:
  `exists_nat_artinConductor`, `exists_nat_swanConductor`, `exists_nat_inertiaArtinConductor`,
  `exists_nat_inertiaSwanConductor`, and for quotient presentations
  `exists_nat_artinConductorOfQuotient`, `exists_nat_swanConductorOfQuotient`, with the natural numbers
  `artinExponent_cast`, `swanExponent_cast` and `artinExponent_eq_fixedCodimension_add_swanExponent`.
- `Langlands.Ramification.Padic.finiteGaloisConductor` (`FiniteFormalPropertiesProof.lean`) proves the
  whole family `FiniteGaloisConductorStatement` (integrality, direct sums, duals, unramified twists,
  vanishing on unramified representations, the tame part); `finiteGaloisConductorExactSequence`,
  `finiteGaloisConductorInduction`, `finiteGaloisInducedConductor`, `finiteGaloisConductorInflation`
  prove additivity, induction and inflation.
- `Langlands.Ramification.Padic.finiteConductorDiscriminant` (`ConductorDiscriminantProof.lean`): the
  conductor–discriminant formula `𝔡 = ∏_χ 𝔣(χ)^{χ(1)}`, with
  `Langlands.LocalField.dvrDiscriminantDifferent` (the discriminant is the norm of the different).
- `Langlands.Ramification.Padic.artinRepClass`, `Langlands.Ramification.Padic.swanRepClass`
  (`ArtinCharacter.lean`): the Artin and Swan class functions are characters of representations.

**Integrality, Weil-group level.** For `F : PadicField p` and
`A : FiniteRepresentation ℂ (Langlands.Weil.Local.localWeilGroup F)`: `Langlands.Weil.Local.artinExponent F A` and
`Langlands.Weil.Local.swanExponent F A : ℕ` (`WeilExponent.lean`) are the Artin and Swan expressions
of any finite inertia presentation of `A` (and `0` if `A` has none); every presentation gives the
same number, continuous representations have presentations, and `a = dim V − dim V^I + sw`.
`Langlands.Henniart.weilConductorIntegrality` (`Langlands/Correspondence/HenniartWeilConductorIntegralityProof.lean`)
gives integrality for every presentation of every Weil representation and an integral presentation
for every continuous one. The presentation theory is
`Langlands.Ramification.Padic.inertiaSurjectivityPresentationAndConductorIndependence`
(`InertiaPresentationProof.lean`).

**Herbrand functions and upper numbering.** `Langlands.Ramification.Padic.herbrandPhi`,
`Langlands.Ramification.Padic.herbrandPsi` and `Langlands.Ramification.Padic.upperRamificationGroup`
(`Herbrand/Finite.lean`) for finite extensions of `p`-adic fields;
`Langlands.Ramification.Padic.absoluteUpperRamificationGroup F v` (`Herbrand/Absolute.lean`) the upper
filtration of `Gal(F̄/F)` as the inverse limit of the finite ones. The same in either characteristic
in `Langlands.Ramification.Local` (`herbrandPhi`, `herbrandPsi`, `localUpperRamificationGroup`,
`localAbsoluteUpperRamificationGroup`, `Herbrand/GeneralFinite.lean`, `Herbrand/GeneralAbsolute.lean`),
for `T : Langlands.LocalField.TopologicalData K₀ L` and a tower `K₀ → K → L`, with no hypothesis on
the characteristic; the declarations of `Langlands.Ramification.Padic` are specializations of them. Herbrand's quotient theorem,
the subgroup formula and the tower laws are in `Herbrand/QuotientProof.lean`,
`Herbrand/LocalQuotientProof.lean`, `Herbrand/SubextensionProof.lean`, `Herbrand/TowerProof.lean`;
the Kummer tower `kummerTower F πs`, the union of the fields F(ϖ^{1/p^n}) for a compatible system
of `p^n`-th roots of a uniformizer ϖ, and the truncation quotients through the break `pe/(p−1)`
(`kummerBreak`), in
`Herbrand/Kummer*.lean` and `Herbrand/Truncation*.lean` (for example
`Langlands.Ramification.Kummer.kummerTowerUpperSup`).

**Hasse–Arf.** `Langlands.Ramification.hasseArfChain_lowerGroup_of_isCyclic` (`HasseArf/Cyclic.lean`)
and `Langlands.Ramification.hasseArfChain_lowerGroup_of_isMulCommutative` (`HasseArf/Abelian.lean`):
for a finite abelian group acting faithfully on a discrete valuation ring, with the residue hypotheses
of the files, `φ(i)` is an integer at every break `i`. `Langlands.Ramification.Padic.hasseArfIntegrality`
(`Herbrand/HasseArfProof.lean`) proves the Library's `HasseArfIntegrality K L T` for every Galois
extension L/K of `p`-adic fields with commutative Galois group (independent universes). From it,
`exists_nat_artinConductor_and_swanConductor_rankOne_of_hasseArf`
(`Herbrand/CharacterExponentIntegrality.lean`) and `exists_nat_artinConductor_rankOne`
(`RankOneConductorIntegrality.lean`): the Artin and Swan expressions of a character are natural
numbers, without local class field theory.

**Close fields.** `Langlands.Ramification.Local.closeFieldsGaloisQuotient` and
`Langlands.Ramification.Local.closeFieldsWeilQuotient` prove `CloseFieldsGaloisQuotientStatement`
and `CloseFieldsWeilQuotientStatement` (`CloseFieldsStatement.lean`): for a `p`-adic field `F` with
absolute ramification index `e` and residue field `k`, `X = k((t))`, there is an isomorphism of
topological groups `G_F/G_F^e ≃ G_X/G_X^e` carrying the image of `G_F^v` onto that of `G_X^v` for
`0 ≤ v ≤ e`, and the same for the Weil groups; `exists_closeFieldsGaloisQuotient` adds the
compatibility with residue degrees.

## What is taken from the FontaineWintenberger copy

The files of `Langlands/LocalFactor/Ramification/Wintenberger/` are the only Library files that import
`FontaineWintenberger/` (see [the roots and the import rule](../library/roots-and-import-rule.md)). They
make the two ramification theories interchangeable by theorems:

- `Wintenberger/FieldClass.lean`: the Library's local fields (proper ultrametric normed fields and
  their finite extensions) are fields of the copy's class `FontaineWintenberger.IsPerfectResidueLocalField`.
- `Wintenberger/Generic.lean`: for a group acting on a local ring, the copy's lower groups and Herbrand
  functions (defined by an integral) equal the Library's (a polygon), for example
  `lowerRamificationGroup_maximalIdeal_eq_lowerGroupInt`.
- `Wintenberger/Finite.lean`, `Wintenberger/Absolute.lean`: the finite and absolute upper filtrations
  agree; `upperRamificationGroupInfinite_eq_padic`, `upperRamificationGroupInfinite_eq_local`
  (`FontaineWintenberger.upperRamificationGroupInfinite` is the Library's absolute filtration).
- `Wintenberger/APF.lean`, `Wintenberger/KummerTower.lean`, `Wintenberger/NormField.lean`,
  `Wintenberger/NormFieldResidue.lean`, `Wintenberger/Degree.lean`: arithmetically profinite extensions
  in the Library's filtrations, the Kummer tower is arithmetically profinite, the filtration of the
  field of norms, residue actions and degrees.
- `Langlands.Ramification.Wintenberger.normFieldComparison` (`Wintenberger/Comparison.lean`):
  Wintenberger's Corollaires 3.2.3 and 3.3.6 in the Library's filtrations: for an infinite,
  arithmetically profinite, totally ramified `L` inside `F̄`, `Gal(F̄/L)` is isomorphic as a
  topological group to the automorphism group of a separable closure of `k((t))`, carrying
  `G_F^u ∩ G_L` onto the upper group at `wintenbergerPsi F L u` for `u ≥ −1` and preserving residue
  degrees. The close-fields proofs use it.

## What is stated and not proved

- `FiniteGaloisConductorCommonRefinementStatement`, `FiniteGaloisInertiaInflationStatement` and
  `FiniteGaloisConductorInflationAndIndependenceStatement` (`InflationStatement.lean`; inflation itself
  is proved as `finiteGaloisConductorInflation`).
- `Langlands.Ramification.Kummer.KummerStageGaloisQuotientStatement`
  (`Herbrand/TruncationQuotientStatement.lean`; its Weil form `KummerStageWeilQuotientStatement` is
  proved).
- `Langlands.Ramification.HerbrandBridge.TameSubextensionHerbrandStatement` (`Herbrand/TameSubextension.lean`).
- `Langlands.Ramification.Padic.WeilBreakComparisonStatement` (`WeilBreakStatement.lean`) and
  `Langlands.Ramification.Local.WeilBreakComparisonStatement` (`LocalWeilBreakStatement.lean`).
- Over local fields of any characteristic, the Weil-group statements of
  `LocalInertiaPresentationStatement.lean` (inertia surjectivity, presentations, conductor
  independence and refinement in `Langlands.Ramification.Local`) have no proof; their `p`-adic
  counterparts in `InertiaPresentationStatement.lean` are proved. Integrality of the conductor is
  proved for `p`-adic fields only.

## Conventions

- The lower index is Serre's: `G_i` acts trivially on `𝒪/𝔪^{i+1}`, `G_0` is inertia, `G_{-1} = G`;
  real indices are read at the ceiling. The upper index is `G^{φ(u)} = G_u`.
- The Library's Herbrand function is a polygon given by a finite sum of clamped linear functions;
  the copy's is an integral of the orders of the lower groups; `Wintenberger/Generic.lean` proves they
  are equal.
- `p`-adic statements take a `PadicField p` with a supplied `Langlands.PadicField.TopologicalData` (any realization of the
  field) and a base `K` given by a scalar tower `ℚ_p → K → F`; the general ones take
  `Langlands.LocalField.TopologicalData K₀ L`. Universes of base, extension and representation space
  are independent.
- In the copy, the lower groups of a valuation subring are `ValuationSubring.lowerRamificationGroupInt`
  (integer index); the Library's are `Langlands.Ramification.lowerGroup` (natural index) and
  `Langlands.Ramification.lowerGroupInt`.

## Why it is built this way

- The FontaineWintenberger copy is one proof of Wintenberger's theorems for a class of fields larger
  than the Library's; it stays whole, and neither ramification theory is retired: the bridges prove
  that they agree, and the statements that the Library publishes use its own filtrations.
- Integrality is proved by Deligne's degree-zero form of Brauer's theorem
  (`Langlands.FiniteRep.DegreeZeroBrauer.finiteDegreeZeroBrauer`): the conductor is a linear functional
  of the character, it is an integer on the generators `Ind_S χ − Ind_S χ'`
  (`InducedRankOneDifference.lean`), and the generators are integral by Hasse–Arf in rank one; no
  Artin character or different is needed for integrality. The Artin character and the
  conductor–discriminant formula are proved separately.
- The general (any characteristic) Herbrand theory is the `p`-adic one generalized in place: the
  names of `Langlands.Ramification.Padic` remain and specialize those of
  `Langlands.Ramification.Local`.

## Origin of the text

The lower-group files (`Depth.lean`, `DifferentFiltration.lean`, `FixedSubring.lean`,
`FixedSubringQuotient.lean`, `FixedSubringValuation.lean`, `LowerGroup.lean`, `LowerGroupQuotients.lean`,
`Monogenic.lean`, `Uniformizer.lean`), `HasseArf/` and `Herbrand/CosetDepth.lean`,
`Herbrand/LowerQuotient.lean`, `Herbrand/Rational.lean`, `Herbrand/RationalQuotient.lean` are adapted
from the Anthropic Lean formalisation of Fermat's Last Theorem; their pages name the source files, and
`licenses/Anthropic-FLT/` holds the licence, the notice and the attribution.
