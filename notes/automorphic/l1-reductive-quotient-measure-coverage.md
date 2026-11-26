# Construction, measure and reduction for the general reductive quotient `[G]`

The Library constructs the Getz–Hahn quotient `[G] = A_G G(F) \ G(A_F)` with its invariant
measure and proves finite volume for connected reductive groups over number fields. The
good Siegel theorem gives a single weak Siegel product whose rational left translates
cover `G(A_F)^1` (§2). The constructions use affine group schemes locally of finite
type. Sections 3 and 4 describe the form, constant-term, cuspidal and `L²` constructions
and the comparisons for `GL_n`. [Global automorphic library](global-program-coverage.md)

In the table in §2, "Proved" identifies a Library theorem whose type is the statement.
"Composable" identifies a type-checked term built from published theorems.

## Related notes

- The literal tensor convention of Getz–Hahn (6.1) affects cuspidality on the function
  carrier of §3. [The algebraic tensor boundary](getz-hahn-literal-tensor-boundary.md)
- Matrix-level reduction gives explicit Siegel factors.
  [Adelic Siegel reduction for GL(n) and connected reductive groups](adelic-siegel-reduction-gl-progress.md)
- The cuspidal operator proofs follow the source map for Chapter 9.
  [Getz–Hahn Chapter 9](getz-hahn-cuspidal-source-map.md)

## Sources

- Getz–Hahn, *An Introduction to Automorphic Representations* (2024), registered as
  `getz-hahn-2024-automorphic-representations` (SHA-256
  `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`). The passages used are
  (2.19)–(2.22) and Lemma 2.6.2, printed pp. 68–69, Theorem 2.6.3, Theorems 2.7.1–2.7.2,
  pp. 71–72, §3.6, pp. 88–90, Definitions 6.3.1 and 6.5.1, pp. 161–162 and 167–168,
  (6.18)–(6.21), pp. 167–168, (8.1), p. 213, and §§9.1–9.2. The Siegel products use GH's
  weak inequalities (2.26).
- The October 2026 author errata, `getz-hahn-2024-errata-2026-10` (SHA-256
  `e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`).
- Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995),
  `moeglin-waldspurger-1995-spectral-decomposition` (folder SHA-256
  `1ba99fb90916a687503e88c7191dad43b9c4865b68e6b4221a4f2126f2d2f141`).
  In `05.1_pp_1_18_Hypotheses_and_general_notation.pdf`, see I.1.4, pp. 4–7, for the choice of
  `K`, `log_M` and `m_P`. In `05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf`,
  see I.1.13, p. 18, for the measure normalizations, I.2.1, pp. 18–20, for `A_M` and the
  Siegel domains, I.2.2–I.2.3 and I.2.5 for height and growth, and I.2.17, pp. 37–39,
  for the functions on `U(𝔸) M(k) \ G`.
- T. A. Springer, *Reduction theory over global fields* (1994), registered as
  `springer-1994-reduction-global-fields` (SHA-256
  `774f5531200db07140b30ffb8f4adce8cf3a3914ca9f38b796f2a2d24ff18496`).
  Section 2.1 gives statements (C) and (F), and §3.6 gives the rank-one argument.
- A. Borel and H. Jacquet, *Automorphic forms and automorphic representations* (1979),
  `borel-jacquet-1979-automorphic` (SHA-256
  `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`), §§3.3 and 4.1–4.4,
  printed pp. 194–196, for cuspidality, finite-level smoothness and the form conditions.
- J. S. Milne, *Algebraic Groups* (2017), `milne-2017-algebraic-groups` (SHA-256
  `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`).
  Proposition 1.92 gives the functorial centralizer and centre, and 2.55 describes Weil
  restriction.

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
| `AdelicGroupPoints.ParabolicIwasawaStatement` | GH Thm 2.7.1 | Proved by `AdelicGroupPoints.parabolicIwasawaStatement` in `AdelicIwasawaProof`. |
| `AdelicSiegelFactors.AdelicCompatibleIwasawaCompactStatement` | MW I.1.4 | Proved by `AdelicSiegelFactors.adelicCompatibleIwasawaCompact` in `AdelicGoodSiegelReductionProof`. |
| `AdelicSiegelFactors.SiegelAlgebraicSetupExistenceStatement` | GH §2.7 setup | Proved: `siegelAlgebraicSetupExistence` (module `AdelicSiegelSetupExistenceProof`), which is `siegelAlgebraicSetupExistence_of_structural genericMinimalParabolic derivedMaximalSplitTorus derivedCentralSplitTorusProduct`. |
| `AdelicGroupPoints.UnipotentRationalQuotientCompactStatement` | compact `U(F)\U(A)` | Proved: `unipotentRationalQuotientCompact` (module `UnipotentRationalQuotientCompactProof`). |
| `AdelicSiegelFactors.PositiveTorusUnipotentModulusStatement` | Haar modulus | Composable: `positiveTorusUnipotentModulus_of_coordinates positiveTorusTriangularCoordinates`. |
| `AdelicSiegelFactors.SimpleRootBoxCompactStatement` | chamber box | Composable: `simpleRootBoxCompactStatement_of_rootComplement relativeRootNegation relativeCharacterRootComplement`. |
| `AdelicSiegelFactors.SiegelProductFiniteMeasureStatement` | MW I.1.13, I.2.1 | Proved by `siegelProductFiniteMeasure` in `AdelicSiegelFiniteVolumeProof`, which combines the three preceding results by `siegelProductFiniteMeasureStatement_of_inputs`. |
| `AdelicSiegelFactors.CentralSplitCompactQuotientStatement` | Springer (C), sufficiency over number fields | Proved by `AdelicSiegelFactors.centralSplitCompactQuotient` in `AdelicSpringerCentralCompactnessProof`. |
| `RepresentationGrowth.RankOneParabolicRationalOrbitHeightBoundStatement` | Springer §3.6 | Proved: `RepresentationGrowth.rankOneParabolicRationalOrbitHeightBound` (module `AdelicRankOneOrbitHeightBoundProof`), see below. |
| `AdelicSiegelFactors.AdelicSiegelChamberReductionStatement` | Springer (F) | Proved: `AdelicSiegelFactors.adelicSiegelChamberReduction` (module `AdelicSiegelChamberReductionProof`), see below. |
| `AdelicSiegelFactors.AdelicGoodSiegelReductionStatement` | GH Thm 2.7.2, MW I.1.4 | Proved by `AdelicSiegelFactors.adelicGoodSiegelReduction` in `AdelicGoodSiegelReductionProof`. |
| `AdelicSiegelFactors.AdelicSiegelReductionStatement` | GH Thm 2.7.2 | Proved by `AdelicSiegelFactors.adelicSiegelReduction` in `AdelicGoodSiegelReductionProof`. |

`AdelicGroupPoints.connectedReductiveFiniteVolume` in `AdelicFiniteVolumeProof` proves
finite volume of the norm-one rational quotient using a covering by finitely many right
translates of a weak Siegel product. `AdelicGroupPoints.normOneRationalQuotientFiniteVolume`
extends it to smooth connected affine groups using the characteristic-zero Levi
decomposition and compactness of the unipotent rational quotient. Both theorems apply
at every universe.

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

The adelic theorem `AdelicGroupPoints.parabolicIwasawaStatement` applies
`parabolicIwasawaStatement_of_archimedean_finite_integral` to
`InfinitePlaceGroupPoints.parabolicIwasawaStatement`,
`FinitePlaceGroupPoints.parabolicIwasawaStatement` and `IntegralIwasawaFamily.existenceStatement`.
For every actual rational parabolic `P`, it gives a maximal compact subgroup `K` with
`P(𝔸_F) K = G(𝔸_F)` as in GH Theorem 2.7.1.
[AdelicIwasawaProof](../../Langlands/Global/AdelicIwasawaProof.md)

For a connected reductive `G`, `siegelAlgebraicSetupExistence` gives the maximal split
torus, generic cocharacter and derived split torus of the setup. The theorem
`AdelicSiegelFactors.adelicCompatibleIwasawaCompact` assembles the maximal compact for the
minimal parabolic from the Levi-compatible archimedean theorem and the same finite-place and
integral theorems, using `adelicCompatibleIwasawaCompactStatement_of_local`. In the archimedean
factors, an element in the intersection with the parabolic belongs to the minimal Levi,
which centralizes the split torus. In the finite factors, the positive torus has trivial
image. This gives `IsPositiveTorusCompatible` as required in the good covering, in the
setting of MW I.1.4.

The theorem `AdelicSiegelFactors.adelicGoodSiegelReduction` applies
`exists_isSiegelCover_of_chamber` to this setup and compact. Through
`exists_leviCompactCover_of_setup` it uses `centralSplitCompactQuotient`, the sufficiency
direction of Springer's (C) over number fields, on the minimal Levi. The lift of the
maximal split torus to that Levi is central and maximal split, so a compact subset of
`M(𝔸_F)^1` meets every principal rational coset in `M(𝔸_F)^1`. Compactness of the
unipotent rational quotient gives `Ω_N`, and `adelicSiegelChamberReduction` supplies
Springer's (F). The compact factors retain `K`, so `P(𝔸_F) ∩ K` commutes with the positive
torus and the ordered weak product `S = Ω_N Ω_M A_{T₀}(t) K` satisfies
`G(F) S = G(𝔸_F)^1`. The theorem
`AdelicSiegelFactors.adelicSiegelReduction` takes the covering clause, as in GH Theorem 2.7.2
and (2.25)–(2.26). Both apply at every universe to split, nonsplit and anisotropic
connected reductive groups. The chamber inequalities are vacuous when the relative root
system is empty.
[AdelicGoodSiegelReductionProof](../../Langlands/Global/AdelicGoodSiegelReductionProof.md)

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

Applying `connectedReductiveFiniteVolumeStatement_of_siegel` to `adelicGoodSiegelReduction`
and `siegelProductFiniteMeasure` gives the same reductive finite-volume proposition via the
single Siegel product. The set has finite Haar outer measure and meets every rational
coset in `G(𝔸_F)^1`.
The covolume criterion for the discrete principal subgroup applies to its measurable hull.
[AdelicSiegelFiniteVolume](../../Langlands/Global/AdelicSiegelFiniteVolume.lean)

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

**Compact covers and the finite-volume proof in `AdelicFiniteVolumeProof`.**
`AdelicParabolicCompactCover`
proves `AdelicGroupPoints.hasCompactParabolicCover`. For every connected reductive `G`
and every parabolic `p : P ⟶ G`, some compact set `Ω` of adelic points satisfies
`P(𝔸_F) · Ω = G(𝔸_F)`. The proof uses archimedean Iwasawa, the integral Iwasawa family and local
compact covers at the finite places (`FinitePlaceGroupPoints.exists_isCompact_parabolic_cover`,
from compactness of `P(F_v) \ G(F_v)`).
`AdelicSiegelFactors.IsSiegelAlgebraicSetup.hasCompactNormOneParabolicCover` gives such an `Ω`
inside `G(𝔸_F)¹` for the canonical minimal parabolic.

`AdelicFiniteVolumeProof` obtains the rational covering from a compact subgroup `K`,
an open subgroup `H₁` and finitely many right translates indexed by `W`.
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

The open-subgroup measure lemma applies to `K ≤ H₁ ⊆ P(𝔸_F) K`, and the rational covering in
this proof uses `S W`. The single-product measure theorem above uses
`IsParabolicIwasawaCompact` and `IsPositiveTorusCompatible` for `K` and applies at every
positive threshold.

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
`centralSplitCompactQuotient` applies it to the proofs above. In the single-product covering,
`exists_isSiegelCover_of_chamber` uses (C) for the minimal Levi to choose `Ω_M`.

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
in the case `P = G`, and GH Corollary 6.2.5 at infinity). The theorem applies
`adelicAutomorphicUniformGrowthReduction` to `lieGroupEllipticInteriorEstimate` and
`adelicAdaptedCasimir`. The adapted Casimir gives an elliptic equation for each left
translate of the form. The interior estimate bounds the enveloping derivatives by the
supremum of the translate near the identity, and submultiplicativity of the height gives
the common exponent.

`GroupSchemeSliceAdelicGrowthStatement` states the
slice-to-global growth comparison (`AdelicSliceModerateGrowthStatement`). Take a connected
reductive `G`, a closed matrix embedding `rho` of positive size, and a continuous rational-invariant
function with an open finite-level stabilizer whose infinite slices each have polynomial growth
(`GroupSchemeFunctions.HasPolynomialGrowth`). The statement asserts that such a function has one
moderate-growth bound `HasAdelicModerateGrowth` on all of `G(A_F)`. The converse is proved
(`HasAdelicModerateGrowth.polynomialGrowth`, module `GroupSchemeAdelicSliceGrowth`). The
statement is derived from MW I.2.1–I.2.3 and GH (6.17).

`GroupSchemeFunctions.adelicSliceModerateGrowthStatement` in `GroupSchemeSliceAdelicGrowthProof`
applies `adelicSliceModerateGrowthStatement_of_rationalHeightReduction` to
`RepresentationGrowth.adelicRationalHeightReduction_of_finiteRightSiegelCover`, using the
finite-right-translate covering of §2.
`adelicSliceModerateGrowthStatement_of_siegel` in `AdelicRationalHeightReduction` gives the
deduction via one Siegel product from the published theorems
`AdelicSiegelFactors.adelicSiegelReduction`, `AdelicSiegelFactors.siegelNormMinimalityStatement`
and `RepresentationGrowth.centralNormOneHeightFactorStatement`. These last two theorems are
proved in `AdelicSiegelNormMinimalityProof` and `AdelicCentralPositiveHeightProof`. They give the
polynomial bound `height(s) ≤ c · height(q s)^e` on a weak Siegel product for each rational
left translate `q s` (MW I.2.2 (vii)) and a central factor with trivial finite component and
polynomially bounded height in the norm-one decomposition (GH Lemma 2.6.2).
[AdelicRationalHeightReduction](../../Langlands/Global/AdelicRationalHeightReduction.lean)

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
For an actual parabolic inclusion, `AdelicGroupPoints.parabolicIwasawaStatement` supplies such a `K`.

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

`GroupSchemeFunctions.adelicConstantTermEnveloping` in `GroupSchemeConstantTermEnvelopingProof`
proves `AdelicConstantTermEnvelopingStatement`. Enveloping derivatives preserve identically
vanishing normalized constant terms along each proper rational parabolic.
`GroupSchemeCuspidalEnvelopingAction` uses this statement to give the uniform cusp forms the
enveloping action compatibly with `Kinf` and to realize the `GL_n` cusp forms under the
original operators (§4).

## 4. GL_n comparisons

**The split-centre quotient.** For `F : Type` and rank `n > 0`,
`GeneralLinearGroupPoints.splitCentreHomeomorph` identifies `A_{GL_n}` with the scalar
matrices from `PositiveRealIdeles.full F`. The same positive real parameter acts at all
infinite places, and the finite components are one. `splitCentreQuotientHomeomorph`
identifies `[GL_n]` with `AdelicGL.SplitCentreQuotient F n`, the left quotient of the
existing matrix group by the positive scalars and the principal matrices. The map on
representatives intertwines positive right translation. With the Borel measurable structure
on the matrix group, `splitCentreQuotientMeasure_isCompatible` gives the same Weil formula
with the transported ambient and subgroup Haar measures. The matrix quotient measure is
finite. This realizes GH (2.20)–(2.21) in the matrix carrier.
[AdelicGLSplitCentreQuotient](../../Langlands/Global/AdelicGLSplitCentreQuotient.md)

The specializations to the `Langlands.Automorphic` GL_n spaces are published in the
`Langlands/Automorphic/GeneralLinear*` modules. All use the actual general-linear group scheme
and the unchanged original carriers:
- forms and growth: `GeneralLinearAdelicForms` (`isAdelicAutomorphicForm_iff_generalLinear_and_adelicGrowth`,
  `adelicAutomorphicGeneralLinearMap`), `GeneralLinearAdelicUniformForms`,
  `GeneralLinearGrowthIndependence`;
- differential, enveloping and centre actions: `GeneralLinearFiniteAdelicDifferential`,
  `GeneralLinearFiniteAdelicEnveloping`, `GeneralLinearAdelicCenterFinite`;
- constant terms: `GeneralLinearConstantTermComparison` and `GeneralLinearIntrinsicConstantTerm`
  (`hasConvergentConstantTerm_generalLinearBlock_intrinsic` and
  `constantTerm_generalLinearBlock_intrinsic`), with `CompactSpace (AdeleQuotient F)`
  supplied by `compactSpace_adeleQuotient`;
- cusp forms: `GeneralLinearCuspidalComparison` (`generalLinearCuspidalEquiv`), the proved
  `GeneralLinearParabolicCuspidalComparisonStatement` (all proper rational parabolics against
  standard maximal blocks), `GeneralLinearParabolicCuspidalEquivalence` and
  `GeneralLinearParabolicCuspidalInclusion`.

**Operator realizations.**
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
  the original matrix operator action.
- `GeneralLinearFullAdelicComparison` exports `generalLinearAutomorphicForm_uniformGrowth`
  for every closed embedding of positive matrix size. The equalities
  `uniformGeneralLinearOperatorRealization_eq_top` and
  `uniformCuspidalGeneralLinearOperatorRealization_eq_cuspidal` identify the uniform
  realizations with the whole original stable operator space and the largest original
  cuspidal realization. For the standard embedding in rank `n > 0`,
  `canonicalUniformAdelicAutomorphicFormsEquiv` and `canonicalCuspidalRealizationAdelicEquiv`
  give continuous complex linear equivalences with the actual uniform forms and cusp forms,
  respectively. They act on the original functions via `finitePlotSmoothGeneralLinearEquiv`
  and use the induced compact-open topologies. The cusp comparison uses the same
  additive-quotient compactness instance as the matrix constant term. Borel–Jacquet §§3.3
  and 4.1–4.4 give the finite-level and cusp conventions, MW I.2.3 and I.2.17 give the
  common-exponent growth condition, and GH Definitions 6.3.1 and 6.5.1 give the adelic
  growth and all-parabolic vanishing conditions.
  [GeneralLinearFullAdelicComparison](../../Langlands/Automorphic/GeneralLinearFullAdelicComparison.md)

The original matrix slice growth transfers to the slice-growth hypothesis used in §3 by
`continuousGeneralLinearEquiv_mem_polynomialGrowth_of_closedImmersion` in
`GeneralLinearGrowthIndependence`. This gives the input for the uniform-growth argument
in `GeneralLinearFullAdelicComparison`.

## 5. Smooth-vector density and spectral analysis

`Langlands.Analysis.integratedIsometricSmoothDensity` proves norm density of smooth vectors
for isometric Lie-group actions with the stated orbit measurability and continuity
hypotheses. The proof integrates smooth kernels whose inverse weights have integral one
and concentrate near the identity.
[IntegratedIsometricSmoothDensityProof](../../Langlands/Representation/Unitary/IntegratedIsometricSmoothDensityProof.md)

`GroupSchemeFunctions.groupSchemeQuotientL2SmoothDensity` applies this theorem to the
infinite right action on the positive-torus quotient. Finite compact-open averaging
commutes with that action, so this also gives density of vectors that are simultaneously
archimedean smooth and fixed by an open finite-adelic subgroup. The result keeps the split
central torus data and right invariance of the norm-one Haar measure.
[GroupSchemeQuotientL2SmoothDensityProof](../../Langlands/Automorphic/GroupSchemeQuotientL2SmoothDensityProof.md)

`RestrictionSplitCentre.QuotientL2SmoothDensityStatement` states the two density assertions
for the restriction quotient with supplied splitting data. Its route uses the isometric
equivalence `quotientL2Equiv` and its intertwining of both right actions. The canonical
specialization is `RestrictionSplitCentre.CanonicalQuotientL2SmoothDensityStatement`.
[Restriction quotient density](../../Langlands/Automorphic/GroupSchemeRestrictionQuotientL2SmoothDensityStatement.md),
[Canonical quotient density](../../Langlands/Automorphic/GroupSchemeCanonicalQuotientL2SmoothDensityStatement.md)

The `GL_n` modules in `Langlands/Automorphic/CuspidalL2/` give cuspidal rapid decay and
band square integrability on the original matrix carrier. The comparison of algebraic and
Hilbert cuspidal spaces and the trace-class results are part of the analysis of GH Chapter 9.
[Getz–Hahn Chapter 9](getz-hahn-cuspidal-source-map.md)
