# The general reductive quotient `[G]`: construction, measure, reduction targets and open obligations

This note was written on 7 November 2026 and revised on 13, 14 and 15 November 2026 and once
more after that.

Finite volume of `G(F) \ G(A_F)^1` and of `[G]` is proved. The finite-place Iwasawa theorem
completes the compositions for adelic Iwasawa and for the good Siegel covering (§2).
The slice-to-global growth theorem uses a covering by finitely many right translates (§5, item 8).

The note records the published Lean construction of the Getz–Hahn quotient
`[G] = A_G G(F) \ G(A_F)`, its measure and its `L²` and cuspidal spaces, for a group scheme `G`
over a number field `F` whose underlying scheme is affine and locally of finite type. All the
adelic constructions below assume both conditions. It also lists the reduction-theory
propositions and which of them are proved. This is the first block of the
[global automorphic program](global-program-coverage.md).

In the table in §2, "Proved" identifies a Library theorem whose type is the statement.
"Composable" identifies a type-checked term built from published theorems.

Related notes:
- [Getz–Hahn (6.1): the literal algebraic tensor removes cusp forms](getz-hahn-literal-tensor-boundary.md)
  treats the literal tensor convention used in §3.
- [Global automorphic library and Henniart inputs](global-program-coverage.md) is the program
  ledger. Its L1 row records an earlier state.
- [Adelic Siegel reduction: the GL(n) chain](adelic-siegel-reduction-gl-progress.md) covers the
  matrix-level reduction theory.
- [Getz–Hahn Chapter 9](getz-hahn-cuspidal-source-map.md) covers the cuspidal operator proofs.

## Sources

- Getz–Hahn, *An Introduction to Automorphic Representations* (2024), registered as
  `getz-hahn-2024-automorphic-representations` (SHA-256
  `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`). The passages used are
  (2.19)–(2.22) and Lemma 2.6.2, printed pp. 68–69; Theorem 2.6.3; §2.7, pp. 71–72; §3.6,
  pp. 88–90; Definition 6.5.1 and (6.18)–(6.21), pp. 167–168; (8.1), p. 213; and §§9.1–9.2.
- The October 2026 author errata, `getz-hahn-2024-errata-2026-10`. They have no Chapter 2
  entry, and they correct no §3.6 passage used here.
- Mœglin–Waldspurger (1995), registered as `moeglin-waldspurger-1995-spectral-decomposition`:
  I.1.4, pp. 4–7 (choice of `K`, `log_M`, `m_P`); I.1.13, p. 18 (measure normalizations);
  I.2.1, pp. 18–20 (`A_M`, Siegel domains); I.2.17, p. 37 (functions on `U(𝔸) M(k) \ G`).
  MW's Siegel domains use strict inequalities, while GH §2.7 uses weak ones. The Lean targets
  follow GH.
- T. A. Springer, *Reduction theory over global fields* (1994), registered as
  `springer-1994-reduction-global-fields`: §2.1, statements (C) and (F).
- J. S. Milne, *Algebraic Groups* (2017), registered as `milne-2017-algebraic-groups`:
  Proposition 1.92 (functorial centralizer and centre), 2.55 (Weil restriction), and the
  structural statements cited by §2.

## 1. The carrier and its measures

**Left quotients.** `LeftCosetSpace Γ` (module `Langlands/Global/LeftCosetSpace`) is the actual
quotient `Γ \ H` by a subgroup that need not be normal, with right translation
`[x] ↦ [x * g]`. The modules `LeftCosetMeasure`, `LeftCosetFundamentalDomain`,
`LeftCosetHaarMeasure` and `LeftCosetWeilMeasure` construct, for discrete `Γ`, the pushforward
of Haar measure restricted to a Borel fundamental domain, and the Weil compatibility structure
`IsCompatible`.

**Norm-one quotient.** `AdelicGroupHaarMeasure` defines `rationalQuotientHaarMeasure` on
`RationalQuotient F G = G(F) \ G(A_F)` and `normOneRationalQuotientHaarMeasure` on
`NormOneRationalQuotient F G = G(F) \ G(A_F)^1` (GH (2.19)). No reductivity is assumed.
`AdelicCharacterLog` gives MW's `log_G : G(A_F) → Hom(Rat(G), ℝ)` as `characterLog`, with
kernel `normOneSubgroup`. The principal-adele product formula is
`NumberField.AdeleRing.norm_algebraMap_eq_one_of_ne_zero` in `Mathlib.NumberTheory.NumberField.AdeleRing`.
It gives norm one for the image of every nonzero element of `F`.

**Positive tori (MW I.2.1).** The `PositiveRealTorus*`, `AdelicSplitCenter*` and
`AdelicSplitComponent*` modules treat an `F`-split central torus `i : T ⟶ G`. They give the
positive image `imageSubgroup F T G i`, the quotient `PositiveRationalQuotient F G T i`, its
measure, and Weil compatibility.

**The restriction split centre (GH (2.20)–(2.22)).**
- `AdelicRestrictionSplitCentre` takes `j : S ⟶ Res_{F/ℚ} G` (the published
  `AffineWeil.groupScheme ℚ F G`) and defines `subgroup F G S j`, the image of the positive real
  points of `S`, its join `rationalSubgroup` with `G(F)`, and `Quotient F G S j`.
- `AdelicRestrictionSplitCentreQuotient` defines `quotientHaarMeasure F G S j` and proves,
  under explicit splitting hypotheses, closedness, the Hausdorff and Borel properties, the
  homeomorphism of the shape of (2.22), and Weil compatibility.
- `RestrictionSplitCentre.comparison : ComparisonStatement` is proved: split components of
  `Res_{F/ℚ} G` and of `G` give the same subgroup.
- `AdelicRestrictionSplitCentreCanonical` fixes split components by choice and defines
  `CanonicalQuotient F G` and `canonicalMeasure F G`. It proves closedness of `A_G G(F)`, the
  Hausdorff and Borel properties of `[G]`, Weil compatibility, right invariance and positivity
  on open sets. These results take `hCST : CentralSplitTorusCharacterStatement.{0}` and
  `hG : IsConnectedReductive G`. The first hypothesis is now proved
  (`GroupScheme.centralSplitTorusCharacter`), so the results hold for every connected reductive
  `G`.
- **The Getz–Hahn `A_G`.** `AdelicRestrictionCentreTorus` defines
  `IsRestrictionCentreValued` and `IsGreatestRestrictionCentreSplitTorus`. They express that
  `j : S ⟶ Res_{F/ℚ} G` takes values in `Res_{F/ℚ} Z_G` and is the greatest `ℚ`-split torus
  there. The centre is the Library's `center G`, tested on all `F ⊗ C`-points. The module proves:
  such a `j` exists; it is exactly a split component of `Res_{F/ℚ} G`; and
  `canonicalSubgroup F G` is the image in `G(A_F)` of the identity component of its real points
  (`coe_canonicalSubgroup_eq_image_connectedComponent`). So `CanonicalQuotient` uses exactly
  the GH (2.20) group `A_G`.

## 2. Reduction theory and finite volume

| Target | Source | Status |
| --- | --- | --- |
| `AdelicGroupPoints.NormOneRationalQuotientFiniteVolumeStatement` (`AdelicFiniteVolumeStatement`) | GH Thm 2.6.3 | Proved: `AdelicGroupPoints.normOneRationalQuotientFiniteVolume` (module `AdelicFiniteVolumeProof`), see below. |
| `AdelicGroupPoints.ConnectedReductiveFiniteVolumeStatement` | GH Thm 2.6.3, reductive case | Proved: `AdelicGroupPoints.connectedReductiveFiniteVolume` (same module). |
| `RestrictionSplitCentre.ConnectedReductiveQuotientFiniteVolumeStatement` | finite volume of `[G]` | Proved: `RestrictionSplitCentre.connectedReductiveQuotientFiniteVolume` (module `AdelicRestrictionSplitCentreFiniteVolumeProof`), see below. |
| `AdelicGroupPoints.AdelicHaarUnimodularityStatement` | GH Lemma 3.6.4 | Proved: `adelicHaarUnimodularity`. Its second conjunct `ConnectedReductiveHaarRightInvariantStatement` is therefore `adelicHaarUnimodularity.2`. |
| `AdelicGroupPoints.AdelicModularCharacterAdjointDeterminantStatement` | adelic modulus | Proved: `adelicModularCharacterAdjointDeterminant` (module `AdelicModularCharacterAdjointDeterminantProof`), which is `adelicModularCharacterAdjointDeterminantStatement_of_local localModularCharacterAdjointDeterminant`. |
| `AdelicGroupPoints.AdelicParabolicModulusStatement` | MW I.1.13; GH (8.1) | Proved: `adelicParabolicModulus` (module `AdelicParabolicModulusProof`). `δ_P` is the idele norm of `det Ad` on `Lie U` and the modular character of `P(𝔸_F)`, see §3. |
| `AdelicGroupPoints.AdelicIwasawaIntegrationStatement` | MW I.1.13 | Proved: `adelicIwasawaIntegration` (module `AdelicIwasawaIntegrationProof`). `dg = c · δ_P(m)⁻¹ du dm dk` for any compact `K` with `P(𝔸_F) K = G(𝔸_F)`, see §3. |
| `Langlands.Global.IwasawaCompatibleMeasureExistenceStatement` | MW I.1.13 | `iwasawaCompatibleMeasureExistence` (module `AdelicIwasawaCompatibleMeasureProof`) chooses the compatible Levi Haar measure for the stated parabolic presentation and compact factor, see §3. |
| `PositiveRealTorus.AdelicPositiveDecompositionStatement` | GH Lemma 2.6.2 | Proved: `adelicPositiveDecompositionStatement`. |
| `GroupScheme.CentralSplitTorusCharacterStatement` | structural | Proved: `centralSplitTorusCharacter`. |
| `InfinitePlaceGroupPoints.ParabolicIwasawaStatement` | archimedean Iwasawa | Proved: `parabolicIwasawaStatement`. |
| `InfinitePlaceGroupPoints.LeviCompatibleIwasawaStatement` | GH Thm B.4.1 | Proved: `leviCompatibleIwasawaStatement`. |
| `FinitePlaceGroupPoints.ParabolicIwasawaStatement` | GH Prop. B.4.2, Thm B.4.3 | Proved: `FinitePlaceGroupPoints.parabolicIwasawaStatement` (module `FinitePlaceIwasawaProof`). For each finite place and actual rational parabolic it gives a maximal compact subgroup with the parabolic on the left in the local product. |
| `IntegralIwasawaFamily.ExistenceStatement` | GH §2.4, App. B | Proved: `IntegralIwasawaFamily.existenceStatement` (module `IntegralIwasawaFamilyProof`), which is `existenceStatement_of_maximalCompact` applied to the proved `IntegralModel.maximalCompactStatement`. |
| `AdelicGroupPoints.ParabolicIwasawaStatement` | GH Thm 2.7.1 | Composable by `parabolicIwasawaStatement_of_archimedean_finite_integral`, applied to the archimedean, finite-place and integral theorems. |
| `AdelicSiegelFactors.AdelicCompatibleIwasawaCompactStatement` | MW I.1.4 | Composable by `adelicCompatibleIwasawaCompactStatement_of_local`, applied to the Levi-compatible archimedean, finite-place and integral theorems. |
| `AdelicSiegelFactors.SiegelAlgebraicSetupExistenceStatement` | GH §2.7 setup | Proved: `siegelAlgebraicSetupExistence` (module `AdelicSiegelSetupExistenceProof`), which is `siegelAlgebraicSetupExistence_of_structural genericMinimalParabolic derivedMaximalSplitTorus derivedCentralSplitTorusProduct`. |
| `AdelicGroupPoints.UnipotentRationalQuotientCompactStatement` | compact `U(F)\U(A)` | Proved: `unipotentRationalQuotientCompact` (module `UnipotentRationalQuotientCompactProof`). |
| `AdelicSiegelFactors.PositiveTorusUnipotentModulusStatement` | Haar modulus | Composable: `positiveTorusUnipotentModulus_of_coordinates positiveTorusTriangularCoordinates`. |
| `AdelicSiegelFactors.SimpleRootBoxCompactStatement` | chamber box | Composable: `simpleRootBoxCompactStatement_of_rootComplement relativeRootNegation relativeCharacterRootComplement`. |
| `AdelicSiegelFactors.SiegelProductFiniteMeasureStatement` | MW I.1.13, I.2.1 | Proved: `siegelProductFiniteMeasure` (module `AdelicSiegelFiniteVolumeProof`), from the three rows above by `siegelProductFiniteMeasureStatement_of_inputs`; it is the term `siegelMeasure` below, which uses the published `AdelicGroupPoints.unipotentRationalQuotientCompact`. |
| `AdelicSiegelFactors.CentralSplitCompactQuotientStatement` | Springer (C) | Proved: `AdelicSiegelFactors.centralSplitCompactQuotient` (module `AdelicSpringerCentralCompactnessProof`); see "Split groups" below. |
| `RepresentationGrowth.RankOneParabolicRationalOrbitHeightBoundStatement` | Springer §3.6 | Proved: `RepresentationGrowth.rankOneParabolicRationalOrbitHeightBound` (module `AdelicRankOneOrbitHeightBoundProof`), see below. |
| `AdelicSiegelFactors.AdelicSiegelChamberReductionStatement` | Springer (F) | Proved: `AdelicSiegelFactors.adelicSiegelChamberReduction` (module `AdelicSiegelChamberReductionProof`), see below. |
| `AdelicSiegelFactors.AdelicGoodSiegelReductionStatement` | GH §2.7, MW I.2.1 | Composable from the algebraic setup, compatible Iwasawa compact and chamber covering as described below. It implies `AdelicSiegelReductionStatement`. |

**Finite volume (proved).** `AdelicGroupPoints.connectedReductiveFiniteVolume`
and `AdelicGroupPoints.normOneRationalQuotientFiniteVolume` (module `AdelicFiniteVolumeProof`)
prove the reductive and the norm-one finite-volume statements at every
universe. Their route does not use finite-place Iwasawa existence; see "Compact covers and the
published finite-volume proof" below.
`RestrictionSplitCentre.connectedReductiveQuotientFiniteVolume` (module
`AdelicRestrictionSplitCentreFiniteVolumeProof`) proves finite volume of `[G]`. It applies the published
`connectedReductiveQuotientFiniteVolumeStatement_of_normOne` to
`AdelicGroupPoints.connectedReductiveFiniteVolume` at universe `0`, because the `[G]` statement
is about number fields in `Type`. The bridge uses that `quotientHaarMeasure F G S j` is the
pushforward of the norm-one quotient measure, so both have the same total mass.
When a maximal `F`-split torus is central, `centralSplitCompactQuotient` gives a compact
norm-one cover. `HasCompactNormOneRationalCover.compactSpace` and the homeomorphism
`RestrictionSplitCentre.canonicalNormOneQuotientHomeomorph` then give compactness of `[G]`.

**Adelic Iwasawa and the good Siegel covering.** The local proof in
`FinitePlaceIwasawaProof` constructs a special-point stabilizer in the common norm
kernel of the rational characters. It transports the resulting Iwasawa compact from the
completion's rational-point group to the actual finite-place evaluation topology.
See [the finite-place proof](../../Langlands/Global/FinitePlaceIwasawaProof.md).

`AdelicGroupPoints.parabolicIwasawaStatement_of_archimedean_finite_integral` takes
`InfinitePlaceGroupPoints.parabolicIwasawaStatement`,
`FinitePlaceGroupPoints.parabolicIwasawaStatement` and `IntegralIwasawaFamily.existenceStatement`.
This gives `AdelicGroupPoints.ParabolicIwasawaStatement` for every actual rational parabolic.

For a connected reductive `G`, `siegelAlgebraicSetupExistence` gives the maximal split
torus, generic cocharacter and derived split torus of the setup. Applying
`adelicCompatibleIwasawaCompactStatement_of_local` to
`InfinitePlaceGroupPoints.leviCompatibleIwasawaStatement` and the same finite-place and
integral proofs supplies a maximal compact subgroup whose intersection with the minimal
parabolic commutes with the positive torus. For this subgroup
`exists_isSiegelCover_of_chamber` uses Springer's (C) via `centralSplitCompactQuotient` and
(F) via `adelicSiegelChamberReduction`. The compact factors it returns use that same subgroup,
so the covering and the commutation property give `AdelicGoodSiegelReductionStatement`.
`adelicSiegelReductionStatement_of_good` gives `AdelicSiegelReductionStatement`. Both
compositions, as well as adelic Iwasawa, type-check at arbitrary universe using the
declarations in Library commit `d6108aa8`.

The Library's `siegelProductFiniteMeasure` has the following proof term.

```lean
theorem siegelMeasure : AdelicSiegelFactors.SiegelProductFiniteMeasureStatement.{u} :=
  AdelicSiegelFactors.siegelProductFiniteMeasureStatement_of_inputs
    AdelicGroupPoints.unipotentRationalQuotientCompact
    (AdelicSiegelFactors.positiveTorusUnipotentModulus_of_coordinates
      positiveTorusTriangularCoordinates)
    (AdelicSiegelFactors.simpleRootBoxCompactStatement_of_rootComplement
      relativeRootNegation relativeCharacterRootComplement)
```

Applying `connectedReductiveFiniteVolumeStatement_of_siegel` to the good covering and
`siegelProductFiniteMeasure` gives a finite-volume proof via the single Siegel product.

**The chamber reduction (F).** The published
`AdelicSiegelFactors.adelicSiegelChamberReduction_of_rankOne_height` (module
`AdelicChamberFromRankOneHeight`) proves `AdelicSiegelChamberReductionStatement`
at every universe from one proposition,
`RepresentationGrowth.RankOneParabolicRationalOrbitHeightBoundStatement` (module
`AdelicRankOneOrbitHeightBound`). This is the arithmetic rank-one assertion. Take `G` with
exactly one simple relative root and a matrix representation in which the stabilizer of a
coordinate line is exactly the minimal standard parabolic. Then one constant `C` works for every
norm-one adelic point `g`: some rational right translate of `g` gives the selected coordinate
vector height at most `C`. It is proved by
`RepresentationGrowth.rankOneParabolicRationalOrbitHeightBound` (module
`AdelicRankOneOrbitHeightBoundProof`). That theorem is
`rankOneParabolicRationalOrbitHeightBound_of_galoisInputs splitGaloisOverlapMatching
(galoisBorelTwisting_of galoisTwistNormOne galoisTwistSubgroup)`. The implication
`rankOneParabolicRationalOrbitHeightBound_of_galoisInputs` fills in the published split
fundamental set and split overlap estimate (see "Split groups" below), following Springer
§3.6. `AdelicSiegelFactors.adelicSiegelChamberReduction` (module
`AdelicSiegelChamberReductionProof`) is
`adelicSiegelChamberReduction_of_rankOne_height rankOneParabolicRationalOrbitHeightBound`, so (F)
is proved at every universe.

The earlier published theorem
`AdelicSiegelFactors.adelicSiegelChamberReduction_of_rankOne_height_and_coordinates` (module
`AdelicChamberFromRootLeviBounds`) also needed
`AdelicSiegelFactors.MinimalParabolicNormCoordinatesStatement` (module
`AdelicMinimalParabolicNormCoordinates`). That statement asks for a
homeomorphism `N(𝔸_F) × (M(𝔸_F)¹ × A_{T₀}) ≃ₜ P(𝔸_F) ∩ G(𝔸_F)¹` for the canonical minimal
parabolic. The new module uses only the existence of such factors. It defines this weaker
property as `HasMinimalParabolicNormFactors` and proves it for every actual Siegel setup of a
connected reductive `G` (`IsSiegelAlgebraicSetup.hasMinimalParabolicNormFactors`). The
coordinate statement is therefore not an input of finite volume. It is proved too, as
`AdelicSiegelFactors.minimalParabolicNormCoordinates` (module
`AdelicMinimalParabolicNormCoordinatesProof`).

**Split groups.** Several published results treat split groups: groups whose Siegel setup
torus `i` is also a maximal torus (`IsMaximalTorus i`). None of them alone proves a general
(non-split) target of this block. With the Galois twisting and matching below they give (C) and
the general rank-one bound.

`RepresentationGrowth.SplitRankOneParabolicRationalOrbitHeightBoundStatement` (module
`AdelicSplitRankOneOrbitHeightBound`) is the rank-one statement above with the
extra hypothesis `IsMaximalTorus i`. It is proved by
`RepresentationGrowth.splitRankOneParabolicRationalOrbitHeightBound` (module
`SplitRankOneAdelic`). The general rank-one statement is proved
too (see above). Its proof uses the split fundamental set, which in turn is derived from the
split bound (next paragraph).

`AdelicSiegelFactors.SplitAdelicFundamentalSetStatement` (module `AdelicSplitFundamentalSet`)
is the split case of Springer's fundamental-set theorem. It asserts that every actual
Siegel setup of a connected reductive `G` with `IsMaximalTorus i` has a right adelic fundamental
set (`HasRightAdelicFundamentalSet`). It is proved by
`AdelicSiegelFactors.splitAdelicFundamentalSet` (module `AdelicSplitFundamentalSetFromCover`),
with no Iwasawa input. That module first proves
`splitAdelicFundamentalSet_of_splitRankOne`, which derives the statement from the split rank-one
bound alone, and then applies it to the published split bound. The chamber argument needs only a
compact set `Ω ⊆ G(𝔸_F)¹` with `P_∅(𝔸_F) · Ω = G(𝔸_F)`, not a compact subgroup, and
`IsSiegelAlgebraicSetup.hasCompactNormOneParabolicCover` below supplies such a set. The earlier
conditional theorem `splitAdelicFundamentalSet_of_splitRankOne_of_finitePlaceIwasawa` (module
`AdelicSplitFundamentalSetFromRankOne`) also assumes finite-place Iwasawa.

**Compact covers and the published finite-volume proof.** `AdelicParabolicCompactCover`
proves `AdelicGroupPoints.hasCompactParabolicCover`. For every connected reductive `G`
and every parabolic `p : P ⟶ G`, some compact set `Ω` of adelic points satisfies
`P(𝔸_F) · Ω = G(𝔸_F)`. The proof uses archimedean Iwasawa, the integral Iwasawa family and local
compact covers at the finite places (`FinitePlaceGroupPoints.exists_isCompact_parabolic_cover`,
from compactness of `P(F_v) \ G(F_v)`); it does not use finite-place Iwasawa.
`AdelicSiegelFactors.IsSiegelAlgebraicSetup.hasCompactNormOneParabolicCover` gives such an `Ω`
inside `G(𝔸_F)¹` for the canonical minimal parabolic. These covers are sets, not subgroups.
The good Siegel reduction gives compact factor data and a threshold with
`IsParabolicIwasawaCompact` (`K` maximal compact with `P(𝔸_F) K = G(𝔸_F)`) and
`G(F) S = G(𝔸_F)¹` for the Siegel product `S`. These are the two parts of `IsSiegelCover`.
`SiegelProductFiniteMeasureStatement` is different: for any supplied compact factor data whose
subgroup satisfies `IsParabolicIwasawaCompact` and `IsPositiveTorusCompatible`, and any positive
threshold, it concludes that the Siegel product meets `G(𝔸_F)¹` in a set of finite measure. It
neither assumes nor concludes any covering.

The published finite-volume proof replaces that subgroup by weaker data.
Besides `AdelicFiniteVolumeProof`, it uses the supporting modules
`AdelicOpenIwasawaCompact`, `AdelicSiegelMeasureOpenSubgroup` and
`Langlands/Analysis/Local/OpenCompactFactorizationHaar` for it.
- `AdelicSiegelFactors.exists_compact_openSubgroup_finite_cover` (module
  `AdelicOpenIwasawaCompact`) gives, for every Siegel setup, a compact subgroup `K`, an open
  subgroup `H₁ ⊇ K` with `H₁ ⊆ P(𝔸_F) K`, positive-torus compatibility of `K`, and a finite set
  `W ⊆ G(𝔸_F)¹` with `P(𝔸_F) (K W) = G(𝔸_F)`. Here `K` is the product of the archimedean
  Levi-compatible Iwasawa compacts with a compact open subgroup of `G(𝔸_f)`, and `H₁` is the
  preimage of that compact open subgroup. `W` comes from covering the compact set of
  `hasCompactNormOneParabolicCover` by finitely many right translates of `H₁`.
- `exists_rational_mul_mem_weakSiegelProduct_mul` (module `AdelicFiniteVolumeProof`) applies the
  published chamber reduction for compact covers,
  `hasWeakChamberCoverReduction_of_rootLeviHeightBounds` (module
  `AdelicSplitFundamentalSetFromCover`), with the published rank-one bound, to the compact set
  `K W`. Every norm-one point then has a rational left translate in the weak Siegel
  product times `W`.
- `measure_weakSiegelProduct_lt_top_of_openSubgroup` (module `AdelicSiegelMeasureOpenSubgroup`)
  is the published Siegel finite-measure reduction with the hypothesis `P(𝔸_F) K = G(𝔸_F)`
  replaced by the open subgroup `H₁`. Finitely many right translates by `W` keep the measure
  finite (`measure_mul_finite_lt_top`), and the published covolume criterion gives finite
  volume.

This route does not prove the good Siegel reduction. It supplies neither a maximal compact
subgroup `K` with `P(𝔸_F) K = G(𝔸_F)` nor a Siegel product `S` with `G(F) S = G(𝔸_F)¹`: its
covering of `G(𝔸_F)¹` needs the extra finite set `W`. `SiegelProductFiniteMeasureStatement` is
unaffected and remains composable (the term `siegelMeasure` above); it has no covering
condition. The open-subgroup lemma only weakens the input of the finite-measure argument: it
replaces the hypothesis `IsParabolicIwasawaCompact` by an open subgroup `H₁` with
`K ≤ H₁ ⊆ P(𝔸_F) K`. `W` is needed for the covering; it is not a hypothesis of the
finite-measure target.

The proof of (C) passes through split groups over a splitting field. Three published statements
serve it, all proved:
- `AdelicSiegelFactors.SplitSiegelOverlapStatement` (module `AdelicSplitSiegelOverlap`):
  Springer's Proposition 2.6 for split groups. It is proved by
  `AdelicSiegelFactors.splitSiegelOverlap` (module `AdelicSplitSiegelOverlapProof`).
  The proof avoids Springer's claim that the line weight is a multiple of `α`, which fails in
  higher rank; see the module's Markdown.
- `AdelicGaloisUnit.SplitGaloisOverlapMatchingStatement` (module `AdelicGaloisOverlapMatching`):
  Springer's §3.5 step, as an implication from `SplitAdelicFundamentalSetStatement` and
  `SplitSiegelOverlapStatement` to a twisted factorization with inverse-orbit matching
  (`HasTwistedOverlapMatching`) over the splitting field. It is proved by
  `AdelicGaloisUnit.splitGaloisOverlapMatching` (module `AdelicGaloisOverlapMatchingProof`).
- `AdelicGaloisUnit.GaloisBorelTwistingStatement` (module `AdelicGaloisBorelTwisting`): every
  connected reductive group over a number field has a finite Galois splitting field with a split
  maximal torus, a generic cocharacter and a Galois twisting of the resulting split Borel pair.
  It is proved by `galoisBorelTwisting_of galoisTwistNormOne galoisTwistSubgroup` (modules
  `AdelicGaloisBorelTwistingProof` and `AdelicGaloisTwistSubgroupProof`).

`AdelicSiegelFactors.centralSplitCompactQuotient_of_splitInputs` (module
`AdelicSpringerCentralCompactness`) derives (C) from the split fundamental set, the split overlap
estimate and the Galois twisting, using `splitGaloisOverlapMatching`. The published
`centralSplitCompactQuotient` applies it to the proofs above. In the finite-volume route, (C) is
consumed by `exists_isSiegelCover_of_chamber` (module `AdelicSiegelChamberReduction`).

## 3. Heights, parabolic quotients, `L²` and cuspidal spaces

Automorphic forms and constant terms are published on `G(F) \ G(A_F)`, with carrier
`ContinuousRationalFunctions F G` and right translation. `GroupSchemeConstantTerm` defines
`constantTerm` along subgroup quotients. `GroupSchemeForms` defines `IsAdelicAutomorphicForm`
(moderate growth with compact and centre finiteness). `GroupSchemeAdelicUniformGrowth` defines
uniform moderate growth (one exponent for all derivatives of the actual enveloping action).
`GroupSchemeFunctions.adelicAutomorphicUniformGrowth` proves
`AdelicAutomorphicUniformGrowthStatement` for connected reductive `G` with a closed matrix
embedding of positive size and a maximal compact subgroup at infinity. One real exponent
works for all enveloping derivatives, each with its own bound constant (MW I.2.17 with I.2.5
in the case `P = G`, and GH Corollary 6.2.5 at infinity). See §5, item 6.
`GroupSchemeSliceAdelicGrowthStatement` states the
slice-to-global growth comparison (`AdelicSliceModerateGrowthStatement`). Take a connected
reductive `G`, a closed matrix embedding `rho` of positive size, and a function with an open
finite-level stabilizer whose infinite slices each have polynomial growth
(`GroupSchemeFunctions.HasPolynomialGrowth`). The statement asserts that such a function has one
moderate-growth bound `HasAdelicModerateGrowth` on all of `G(A_F)`. The converse is proved
(`HasAdelicModerateGrowth.polynomialGrowth`, module `GroupSchemeAdelicSliceGrowth`). The
statement is derived from MW I.2.1–I.2.3 and GH (6.17); it is proved (§5, item 8).
`GroupSchemeCuspidalForms` defines `AdelicCuspidalForms`. The form-space Markdown explains why
these spaces follow Borel–Jacquet §4.1–4.2 rather than the literal tensor of GH (6.1).

The `[G]` modules `Langlands/Automorphic/GroupSchemeRestriction*` keep the actual
quotient, measure and right action:
- `QuotientL2`, `QuotientL2Continuity`, `QuotientL2InfiniteAction`, `QuotientL2FiniteAverage`
  and `QuotientL2SmoothVectors` give `L²([G])`, its right regular and integrated actions,
  averaging over compact open subgroups and smooth vectors.
- `ContinuousL2` and `CuspidalL2` treat continuous square-integrable and cuspidal classes.
  Parabolic vanishing takes the explicit hypotheses `hPD : ParabolicDynamicStatement` and `hG`.
  `hPD` is now proved (`GroupScheme.parabolicDynamic`).
- `FullAEL2` and its companions treat the closed subspace of almost-everywhere cuspidal classes.
  `FullAEL2FullGroup` puts the quantifier over all of `G(A_F)`. `FullAEL2CentreQuotient` builds
  the quotient group `A_G \ G(A_F)` with its Borel σ-algebra and states the condition with the
  quantifier for Haar measure there, as GH (6.21) write it. It proves that the three conditions
  agree under the decomposition hypotheses.
- `CanonicalCuspidalL2` gives the norm-one spaces on `CanonicalQuotient F G`.

The four approximation statements on `[G]` (`QuotientL2HermitianApproximationStatement`,
`QuotientFullAEL2HermitianApproximationStatement`, `QuotientL2FiniteApproximationStatement`,
`QuotientFullAEL2FiniteApproximationStatement`) are proved. The parabolic `L²` closedness
statement `GroupSchemeParabolicL2ClosednessStatement` is proved (`groupSchemeParabolicL2Closedness`).

**Heights and parabolic quotients (MW I.1.4, I.2.17).** `AdelicIwasawaHeight` defines the height
`H_P(g) = log_P(q)` for `g = p(q) k` and a supplied compact `K` with `P(A_F) K = G(A_F)`, with its
Levi form (`m_P`). The height depends on `K`. `AdelicParabolicQuotient` defines
`X_P = U(A_F) M(F) \ G(A_F)` and proves that `P_J(A_F)` normalizes `U_J(A_F)` for every standard
parabolic. `AdelicMaximalCompactFactors` shows that a maximal compact subgroup of `G(A_F)` is
`K_∞ × K_f` with both factors maximal compact, and transfers `IsParabolicIwasawaCompact` along
`P₀ → P`.

**The modulus `δ_P` and the measure `dk` (MW I.1.13).** `AdelicParabolicModulus`
works with the dynamic parabolic `P = P_G(χ)`, its unipotent radical `U = U_G(χ)` and its Levi
factor `M = Z_G(χ)` of a cocharacter `χ`, given by representing group schemes. It proves that
`U(𝔸_F)` is closed in `G(𝔸_F)` and normalized by `P(𝔸_F)`. It defines
`parabolicModulus F hP hU : P(𝔸_F) →* ℝ≥0ˣ` as the published
`HaarModulus.closedNormalizerCharacter` of the image of `U(𝔸_F)`, so that
`μ(p E p⁻¹) = δ_P(p) μ(E)`. It proves the integral form `integral_conj_parabolicModulus`:
`∫ f(p⁻¹ u p) du = δ_P(p) ∫ f(u) du` on `U(𝔸_F)`. For `m ∈ M(𝔸_F)` this is MW's `m^{2ρ_P}`. For
a compact subgroup `K` of `G(𝔸_F)`, `compactHaarProbability F G K hK` is the Haar probability
on `K`, and `eq_compactHaarProbability` shows that it is the only left Haar probability there.
Two statements concern them. Both are proved, as `AdelicGroupPoints.adelicParabolicModulus`
(module `AdelicParabolicModulusProof`) and `AdelicGroupPoints.adelicIwasawaIntegration` (module
`AdelicIwasawaIntegrationProof`):
- `AdelicParabolicModulusStatement`: `δ_P` is the idele norm (`characterNorm`) of the rational
  character `det(Ad | Lie U)` of `P`, for every choice of coordinates on `Lie U`, and is Mathlib's
  modular character of `P(𝔸_F)`;
- `AdelicIwasawaIntegrationStatement`: for every compact subgroup `K` with `P(𝔸_F) K = G(𝔸_F)`
  there is `c > 0` with `∫_{G(𝔸_F)} f dg = c ∫_K ∫_{M(𝔸_F)} ∫_{U(𝔸_F)} δ_P(m)⁻¹ f(u m k) du dm dk`
  for all `f ∈ C_c(G(𝔸_F))`, where `dg`, `dm`, `du` are Mathlib's Haar measures. The constant
  `c` is not normalized: the Haar measures on `G(𝔸_F)`, `M(𝔸_F)` and `U(𝔸_F)` are fixed
  independently.

The lemmas `continuous_parabolicModulus_of_eq` and `parabolicModulus_rational_of_eq` give
continuity of `δ_P` and triviality on `P(F)` under the conclusion of the first statement.
For an actual parabolic inclusion, the adelic Iwasawa composition in §2 supplies such a `K`.

`Langlands.Global.iwasawaCompatibleMeasureExistence` applies the two theorems to a
parabolic with a compatible root presentation and a supplied maximal compact `K`
with `P(𝔸_F) K = G(𝔸_F)`, for `F : Type`. It fixes the ambient Mathlib Haar measure,
uses Haar probability on `K` and unipotent Haar measure with quotient mass one, and absorbs
the scalar into the Levi Haar measure. The integral defining `IsIwasawaCompatibleMeasure`
then has coefficient one.

**Infinite-place compatibility of the form spaces (GH (6.11)–(6.14)).**
`Geometry/Manifold/SmoothGroupConjugationLie` proves that `Ad(g)` (the derivative of conjugation)
preserves the bracket of the identity tangent space of a Lie group. `GroupSchemeInfiniteTranslation`
uses it for every smooth affine `G`:
- the adjoint automorphism `adelicEnvelopingConjugationEquiv` of the actual enveloping algebra,
  which preserves its centre;
- the covariance `R(g) D_a = D_(Ad(g) a) R(g)` of right translation and the actual enveloping
  action;
- preservation of centre finiteness and uniform growth by every infinite translation, and of the
  form conditions by the specified infinite subgroup `Kinf`;
- `Kinf`-subrepresentations of the form, uniform form, cusp form and uniform cusp form spaces.

Whether the enveloping action preserves cuspidality is the target statement
`AdelicConstantTermEnvelopingStatement` (module `GroupSchemeConstantTermEnvelopingStatement`): it
asserts that enveloping derivatives preserve identically vanishing normalized constant terms along
a proper rational parabolic. It is proved (§5, item 5). Its consequences, conditional on the
statement, are published in `GroupSchemeCuspidalEnvelopingAction`: the uniform cusp forms carry the
enveloping action compatibly with `Kinf`, and the `GL_n` cusp forms form an operator realization
(see §4).

## 4. GL_n comparisons

The specializations to the `Langlands.Automorphic` GL_n spaces are published in the
`Langlands/Automorphic/GeneralLinear*` modules. All use the actual general-linear group scheme
and the unchanged original carriers:
- forms and growth: `GeneralLinearAdelicForms` (`isAdelicAutomorphicForm_iff_generalLinear_and_adelicGrowth`,
  `adelicAutomorphicGeneralLinearMap`), `GeneralLinearAdelicUniformForms`,
  `GeneralLinearGrowthIndependence`;
- differential, enveloping and centre actions: `GeneralLinearFiniteAdelicDifferential`,
  `GeneralLinearFiniteAdelicEnveloping`, `GeneralLinearAdelicCenterFinite`;
- constant terms: `GeneralLinearConstantTermComparison` and `GeneralLinearIntrinsicConstantTerm`
  (`constantTerm_generalLinearBlock`, with `CompactSpace (AdeleQuotient F)` explicit);
- cusp forms: `GeneralLinearCuspidalComparison` (`generalLinearCuspidalEquiv`), the proved
  `GeneralLinearParabolicCuspidalComparisonStatement` (all proper rational parabolics against
  standard maximal blocks), `GeneralLinearParabolicCuspidalEquivalence` and
  `GeneralLinearParabolicCuspidalInclusion`.

**Operator realizations (11 November 2026).**
- `GeneralLinearUniformOperatorRealization` makes the matrix-side uniform-growth forms an invariant
  subspace of `fullAutomorphicAction`, hence an `OperatorRealization`. It proves that the actual
  uniform forms map onto exactly this subspace, with intertwining of the enveloping and finite
  actions, and that they are closed under the transported standard maximal compact.
- `GeneralLinearUniformCuspidalRealization` maps every realization inside the uniform realization
  injectively into the actual uniform forms, and every cuspidal one into the actual uniform cusp
  forms. It constructs the largest cuspidal realization inside the uniform realization.
- `GeneralLinearCanonicalUniformComparison` instantiates these
  comparisons with every hypothesis discharged by published results: the standard representation, the reductive atlas
  `(isConnectedReductive_generalLinear F (Fin n)).smoothDimension_spec`,
  `adelicDifferentialCommutator_of_smooth` and `parabolicDynamic`. Only `0 < n` remains.
- The original matrix form definition bounds each infinite slice separately, with an exponent
  and constant that may depend on the finite component.
  `isAdelicAutomorphicForm_iff_generalLinear_and_adelicGrowth` keeps the full adelic bound
  (`HasAdelicModerateGrowth`) as an extra conjunct on the matrix side.
  `adelicSliceModerateGrowthStatement` gives that bound at the form's finite level.
  `adelicAutomorphicUniformGrowth` then gives a common exponent for all enveloping derivatives.
  `hasAdelicUniformModerateGrowth_iff` converts to a natural exponent for the height and
  `hasAdelicUniformPolynomialGrowth_iff_generalLinear` identifies the resulting condition on
  the original matrix operator action. The standard embedding in this argument has `0 < n`.

The `GL_n` side has cuspidal rapid-decay and band square-integrability results
(`Langlands/Automorphic/CuspidalL2/`). No comparison of these with the `[G]` `L²` spaces is
published. That comparison belongs to the later Chapter 9 blocks of the program.

## 5. Open obligations

1. `AdelicGoodSiegelReductionStatement` includes the positive-torus commutation needed to
   apply the single-product finite-measure theorem to the factors of the covering (§2).
2. Exact-target proofs of the composable statements in §2. The Library proves
   `UnipotentRationalQuotientCompactStatement` (`unipotentRationalQuotientCompact`),
   `SiegelProductFiniteMeasureStatement` (`siegelProductFiniteMeasure`),
   `AdelicModularCharacterAdjointDeterminantStatement` (`adelicModularCharacterAdjointDeterminant`),
   `SiegelAlgebraicSetupExistenceStatement` (`siegelAlgebraicSetupExistence`) and
   `RestrictionSplitCentre.ConnectedReductiveQuotientFiniteVolumeStatement`
   (`connectedReductiveQuotientFiniteVolume`). `PositiveTorusUnipotentModulusStatement` and
   `SimpleRootBoxCompactStatement` are composable, with no exact-target proof recorded here.
3. `AdelicCompatibleIwasawaCompactStatement` uses Levi compatibility at the infinite
   places because the positive torus has trivial components at the finite places (§2).
4. Smooth-vector density on `[G]` (`RestrictionSplitCentre.QuotientL2SmoothDensityStatement`
   and the positive-torus version). It waits for the generic
   `Langlands.Analysis.IntegratedIsometricSmoothDensityStatement`, whose remaining input
   `SmoothInverseKernelSequenceStatement` is proved, as `Langlands.Analysis.smoothInverseKernelSequence`
   (module `Langlands/Analysis/SmoothInverseKernelSequenceProof`). This note records no proof of
   the generic statement or of the `[G]` statements.
5. `AdelicConstantTermEnvelopingStatement` (§3) is proved, as
   `GroupSchemeFunctions.adelicConstantTermEnveloping` (module
   `GroupSchemeConstantTermEnvelopingProof`). It makes the cusp form spaces stable under the
   enveloping action. It also supplies the input for identifying the `GL_n` uniform cuspidal
   realization with all uniform cuspidal forms.
6. `GroupSchemeFunctions.adelicAutomorphicUniformGrowth` (module
   `GroupSchemeAutomorphicUniformGrowthProof`) proves `AdelicAutomorphicUniformGrowthStatement`
   (§3). It applies `adelicAutomorphicUniformGrowthReduction` to
   `lieGroupEllipticInteriorEstimate` and `adelicAdaptedCasimir`. The adapted Casimir yields an
   elliptic equation for each left translate of the form. The interior estimate bounds its
   enveloping derivatives by the supremum of the translate near the identity, and
   submultiplicativity of the height gives the common exponent.
7. `AdelicParabolicModulusStatement` and `AdelicIwasawaIntegrationStatement` (§3) are proved
   (`adelicParabolicModulus`, `adelicIwasawaIntegration`).
8. The slice-to-global moderate-growth comparison: whether a function with an open
   finite-level stabilizer, whose growth is bounded slice by slice, has the full adelic bound
   `HasAdelicModerateGrowth` (§4). It is the exact target `AdelicSliceModerateGrowthStatement`
   (§3), for connected reductive `G` and a closed embedding. It is proved, as
   `GroupSchemeFunctions.adelicSliceModerateGrowthStatement` (module
   `GroupSchemeSliceAdelicGrowthProof`): `adelicSliceModerateGrowthStatement_of_rationalHeightReduction`
   (module `GroupSchemeSliceAdelicGrowthReduction`) applied to
   `RepresentationGrowth.adelicRationalHeightReduction_of_finiteRightSiegelCover` (module
   `AdelicFiniteTranslateHeightReduction`), which works with a Siegel cover up to finitely many
   right translates and does not need the good Siegel reduction.
   A second published reduction follows the route through the Siegel covering:
   `GroupSchemeFunctions.adelicSliceModerateGrowthStatement_of_siegel` (module
   `AdelicRationalHeightReduction`) proves the target from three propositions:
   - the Siegel covering `AdelicSiegelReductionStatement`, which follows from the good Siegel
     reduction by `adelicSiegelReductionStatement_of_good`;
   - `AdelicSiegelFactors.SiegelNormMinimalityStatement` (module
     `AdelicSiegelNormMinimalityStatement`), MW I.2.2 (vii) in the polynomial form
     `height(s) ≤ c · height(q s)^e` on a weak Siegel product;
   - `RepresentationGrowth.CentralNormOneHeightFactorStatement` (module
     `AdelicCentralPositiveHeightStatement`), the factorization `G(𝔸) = A_G · G(𝔸)¹` of GH
     Lemma 2.6.2 with a polynomial height bound on the central factor.

   The last two propositions are proved:
   `AdelicSiegelFactors.siegelNormMinimalityStatement` (module
   `AdelicSiegelNormMinimalityProof`) and
   `RepresentationGrowth.centralNormOneHeightFactorStatement` (module
   `AdelicCentralPositiveHeightProof`). Using the single Siegel covering from §2,
   this composition type-checks at arbitrary universe.

   For `GL_n`, the original matrix slice growth transfers to the slice-growth hypothesis of the statement
   (`continuousGeneralLinearEquiv_mem_polynomialGrowth_of_closedImmersion`, module
   `GeneralLinearGrowthIndependence`). This is the first step of the matrix growth argument in §4.
