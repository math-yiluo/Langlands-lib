# Waldspurger on actual rational points: published modules and structural ledger

Coverage of the modules section, before the update of 16 November 2026, was checked against Library commit
`c2a69151fc91dc660bd8106a217845dbf5a561c4`. Its last row
(`DynamicCommonLeviScalar`) was checked there directly. Other modules in those earlier rows are
byte-identical at that commit to their versions at `544dba099880b57da5fdc3cbc715c01cf2579eb2`,
against which the row `DynamicCommonLeviComposition` was checked. The
modules named in the rows before that are also byte-identical to their versions at
`70eca2e4ea526de0ce0c41e4a9ea0e7d8087cbe7`, and those in the still earlier rows to their
versions at `7d0469f6b963a3184585874ef8a502809dcbd51b`, against which those rows were checked.
The topology and adjunction modules are checked against the commits at which they first appeared
in the Library (below); their Lean and Markdown files there match the present ones.
The section on weight estimates records later results checked at Library
`a11d1e75f52192f694c9901f4b7fd7098b0f8ff9`.
The final section records the scalar and common-Levi comparisons at
`b304c4f466feb1c522f6ac175d373bc1a9cab490`.

This note lists the Library modules that realize items of Waldspurger's article
on the actual rational points `G(F) = rationalPoints G` of a group scheme over a nonarchimedean
local field (canonical topology `rationalPointTopology F G.X`), the external structural
hypotheses they consume, and the open obligations on the chains through them. It complements the
item-by-item [source map](waldspurger-source-map.md), which records the generic (abstract)
Library coverage. A proposition definition below is a statement, not a proof. The note proves
nothing.

Source: J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques (d'après
Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333, source ID
`waldspurger-2003-plancherel`. Printed page numbers; the PDF page is the printed page minus 234.

## Modules

| Module | Main declarations | Source items | Hypotheses |
|---|---|---|---|
| `HarmonicAnalysis/HarishChandraSchwartz/FiniteFunctionUniqueness` | `HasFiniteExpansion`, `finiteCoeff`, `eq_zero_of_exponentialPolynomial_eq_zero`, `expansionCoeff_eq_of_exponentialPolynomial_eq`, `exists_uniform_growth_iff_unitary` | I.2 (pp.242–243): uniqueness of the expansion `Σ χ(a) P_χ(H_M(a))`, the minimal `X`, (1) ⇔ (2) | abstract commutative group `A` with additive `H_M : A → E` and a lattice section (as in the Library's `FiniteFunctionExpansion`) |
| `Representation/Plancherel/RationalPlancherelConstant` | `cocharacterSubmoduleCentralizer`, `rankOneCocharacterSet`, `leviGamma`, `rankOneGamma`, `rankOneGammaProduct`, `plancherelConstant`, `plancherelConstantReal`, `plancherelConstantReal_pos_of_smooth`, `plancherelConstant_zsmul` | derived encoding of I.1 (pp.240–241): `c = γ⁻¹ ∏ γ_α`, using actual subgroup integrals with common-compact normalized Haar measures; positive-multiple invariance with the compact fixed | affine, locally finite type `G` over arbitrary nonarchimedean local `F`, compact open `K`, commutative group-scheme homomorphism `i` and cocharacter `ζ`. Definitions do not require reductivity. The index set is finite for a split torus; the original positive-real-value lemma assumes smooth `G` and finite indexed factors, discharged under the next row's hypotheses. Formal source-object comparisons and general same-Levi independence remain open |
| `Representation/Plancherel/RationalPlancherelConstantFinite` | `exists_dynamicCentralizer_eq_cocharacterSubmoduleCentralizer`, `measurePreserving_subgroupEmbeddingEquiv`, `leviGamma_eq_gamma_of_isClosedSubgroup`, `rankOneGamma_ne_top`, `rankOneGammaProduct_ne_top_of_isSplitTorus`, `plancherelConstant_pos_ne_top`, `plancherelConstantReal_pos_of_isSplitTorus` | derived finiteness proof for the I.1 constants (pp.240–241): every integer-submodule centralizer is the centralizer of one generic cocharacter; exact common-compact Haar/integral transport identifies its constant with the published smooth-group `gamma`. Every rank-one factor, its finite product and `c` are finite, and the real `c` is positive | arbitrary nonarchimedean local `F`, affine locally finite type `G` that is smooth with connected underlying scheme, split `T`, homomorphism `i : T → G`, cocharacter `ζ`, compact open `K`. No reductivity, maximality of `T` or specialness of `K` is needed. Source root/Levi identifications, reductivity of these centralizers and fixed-Levi parabolic independence remain separate |
| `Representation/Plancherel/DynamicOppositeUnitaryScalarStatement` | `ConditionalDynamicOppositeUnitaryScalarStatement` (statement only), `RationalFunctionRegularAt`, `RationalFunctionNonnegAt`; proved predicate lemmas `rationalFunction_value_eq`, `RationalFunctionNonnegAt.regularAt` | derived target from IV.3(6) and its proof (p.287) and the regularity/nonnegativity claims of V.2.1 (pp.292–293): `j_P ≠ 0` in the rational function field and `j_P⁻¹` regular with a nonnegative real value at every unitary unramified character | arbitrary nonarchimedean local `F`, affine locally finite type connected reductive `G`, cocharacter `χ`, explicit `hRefl` and `hCST` (both have published dischargers below); compact open `K` with both `G(F) = P_G(χ)(F) K` and `G(F) = P_G(χ⁻¹)(F) K`; canonical smooth representation `A` of `M(F) = Z_G(χ)(F)`; actual whole-operator continuations `p, q`, two nonempty open subsets of their full convergence domains, a nonempty open generic irreducibility locus for the twisted normalized induction; normal central `C`, Borel quotient Haar measure, finite `M(F)/(M¹ C)` and square integrability of `A` modulo `C`. The convergence, continuation, irreducibility and square-integrability inputs are not structural hypotheses |
| `Representation/Plancherel/RationalPlancherelDensity` | `plancherelDensityConstant`, `plancherelDensity`, `plancherelDensity_mul_scalar`, `plancherelDensity_eq_zero_iff`, `plancherelDensity_continuation_independent`, `plancherelDensity_irreducibility_locus_independent`, `plancherelDensity_stabilizer_fixed`, `plancherelDensity_spec`, `conditionalContinuedComposite_eq_plancherelDensity_value` | derived V.2 expression (p.292), using the actual conditional IV.3 scalar (pp.285–287): `µ = C j_P⁻¹` on unramified characters, with `C = (rankOneGammaProduct.toReal)²`; independence, self-twist stabilizer invariance and conditional composite identities. No proof of V.2.1 | arbitrary nonarchimedean local `F`, affine locally finite type connected reductive `G`, commutative `T`, `i`, `ζ`, and `χ = ζ ≫ i`; same `K` for the constant and scalar, both compact-parabolic factorizations, canonical `SmoothRep A`, `hRefl`, `hCST`, whole-operator continuations and nonempty convergence subsets and generic irreducibility locus. Continuation independence needs the convergence subsets open; specification, stabilizer and locus-independence results also need the original irreducibility locus open. Constant positivity and the zero equivalence require finite product; `µ j_P = C` requires `j_P ≠ 0`; the pointwise composite formula requires both numerator and denominator of a presentation of `µ` to be nonzero at a point in the common regular region. These analytic inputs are not structural conclusions |
| `Representation/Plancherel/RationalPlancherelDensityPositivity` | `ConditionalPlancherelDensityUnitaryStatement` (target), `RationalFunctionNonnegAt.const_mul`, `conditionalPlancherelDensityUnitaryStatement_of_unitaryScalar` | derived first two claims of V.2.1 (pp.292–293), with the additional rational-field nonvanishing clause: `µ ≠ 0` if the gamma product is finite, and `µ` regular with a nonnegative real value at every unitary character | same data as the density and the square-integrable scalar target above, including central quotient Haar, finite `M(F)/(M¹ C)` and square integrability. The proved reduction assumes the unproved `ConditionalDynamicOppositeUnitaryScalarStatement`; it supplies neither that premise nor a proof of V.2.1 |
| `Representation/Plancherel/DynamicOppositeHermitianAdjunctionStatement` | `characterConjInv`, `unramifiedConjInv`, `compactPictureHermitianPairing`, `ConditionalDynamicOppositeHermitianAdjunctionStatement` (target proved in `DynamicOppositeHermitianAdjunctionProof`) | derived Hermitian form of IV.1 (11) and the proof of IV.3 (6) (pp.283, 287): adjunction of the actual forward integral at `z` with the reverse integral at `z† = conj(z)⁻¹`, on their convergence domains | arbitrary nonarchimedean local `F`, affine locally finite type connected reductive `G`, cocharacter `χ`, `hRefl`, `hCST`, both compact-parabolic factorizations; both Levi projections send the corresponding `P ∩ K` into `K`; canonical `SmoothRep A` with an invariant positive form; `z` in the forward full domain and `z†` in the reverse full domain. The compact pairing uses Haar probability on `K`. The involution and its fixed-point property on unitary characters are proved. The adjunction now has a published proof at exactly this scope; convergence-domain inclusion remains a premise |
| `Representation/Plancherel/DynamicOppositeUnitaryNonnegativity` | `compactPictureInnerCore`, `compactPictureSesq`, `continuedOperator_adjoint`, `continuedCompositeRationalScalar_nonnegAt`, `ConditionalDynamicOppositeUnitaryNonnegStatement`, `conditionalDynamicOppositeUnitaryNonneg_of_hermitianAdjunction` | derived squared-norm argument in the proof of IV.3 (6) (p.287): compact-pairing positivity, continuation of adjointness, and nonnegative values of `j_P` at unitary common regular points | both compact-parabolic factorizations and projection-stability premises, unitarizable `A`, actual continuations, nonempty open forward/reverse convergence subsets and generic irreducibility locus; additionally `hdag` sends the chosen forward subset into the reverse full domain. The proved reduction takes the Hermitian adjunction target, now discharged by its published proof. Its conclusion is restricted to `p.regularRegion ∩ q.regularRegion` |
| `Representation/Plancherel/DynamicOppositeUniformNonvanishing` | `compactTestVector`, `exists_forwardCompactFamily_eval_one_eq`, `continuedOperator_map_eq_of_eqOn`, `RationalFunctionPosAt`, `ConditionalDynamicOppositeUnitaryPositiveStatement`, `conditionalDynamicOppositeUnitaryPositive_of_hermitianAdjunction` | derived uniform version of IV.1 (10) (p.283) and strict squared-norm argument of IV.3 (6) (p.287): one compact-picture vector has constant nonzero forward evaluation at `1`; conditionally `j_P ≠ 0` as a rational function and both `j_P` and `j_P⁻¹` have positive values at unitary common regular points | the target retains exactly the preceding nonnegativity target's hypotheses, including unitarizability, compact projection stability and `hdag`; the reduction again takes the now-proved adjunction target. The uniform-vector and continuation lemmas are proved. No square-integrability premise is needed for this common-regular-point argument; regularity of `j_P⁻¹` at every unitary point is not established |
| `Representation/Plancherel/DynamicOppositeUnitaryInverseRegularity` | `RationalFunctionRegularAt.nonnegAt_of_unitary`, `ConditionalDynamicOppositeUnitaryInverseRegularStatement` (unproved target), `ConditionalDynamicOppositeUnitaryInverseNonnegStatement` (target), `conditionalDynamicOppositeUnitaryInverseNonneg_of_regular` | derived regularity half of IV.3 (6) as V.2.1 uses it (pp.287, 292–293): `j_P⁻¹` regular at every unitary unramified character; together with the adjunction, `j_P ≠ 0` and a nonnegative real value of `j_P⁻¹` at every unitary character | both targets take exactly the hypotheses of `ConditionalDynamicOppositeUnitaryPositiveStatement` (previous row). The reduction takes the now-proved Hermitian adjunction and the still-unproved regularity target. The generic lemma is proved: a rational function regular at a unitary `z`, with nonnegative real values at the unitary points where a fixed nonzero regular function does not vanish, has a nonnegative real value at `z` |
| `Representation/Plancherel/RationalUnitaryRegularValue` | `RationalFunctionUnitaryRegular`, `rationalUnitaryValue`, `rationalUnitaryValue_eq`, `isSmoothFiniteTorusFunction_rationalUnitaryValue`, `continuous_rationalUnitaryValue`, `rationalUnitaryValue_nonneg`, `plancherelDensity_unitaryRegular`, `plancherelWeight`, `isSmoothFiniteTorusFunction_plancherelWeight`, `continuous_plancherelWeight`, `plancherelWeight_nonneg`, `plancherelWeight_stabilizer_invariant` | derived value function `ω ↦ µ(ω)` on `Im X(M)` required by V.2.1 (p.292) and the wave packets of VI.3 (p.302) | generic part: connected reductive `G` and a rational function regular at every unitary unramified character; the value is independent of the presentation, smooth in the circle coordinates, continuous, and compatible with sums, products, translations and nonnegative values. Weight part: the density's data and `hreg`, regularity of `j_P⁻¹` at every unitary character (the unproved target of the previous row); the weight is nonnegative wherever `j_P⁻¹` has nonnegative real values |
| `Representation/Plancherel/StandardLeviPlancherelWeight` | `discreteSeriesOrbitDescend`, `standardLeviParameterIso`, `standardLeviDynamicHomeomorph`, `standardLeviCharacterRestrict`, `standardOrbitWeight`, `standardLeviPlancherelWeight` (with `_orbitMap`, `isSmoothFiniteTorusFunction_…`, `continuous_…`, `_nonneg`, `_nonneg_of_forall`), `exists_norm_standardLeviPlancherelWavePacket_le_rationalXi_rpow` | derived transport of the weight to the orbit `O` of a discrete series of a standard Levi `M_I(F)` (VI.3, p.302; V.2.1, p.292), and the wave-packet decay bound with the weight `µ` | standard cocharacter `ζ` of `I`, so that `Z_G(ζ ∘ i)` represents `M_I`; a discrete-series class `π` of `M_I(F)` with the density's data for its inducing representation; `hreg` as in the previous row. The decay corollary keeps the other hypotheses of `exists_norm_rationalInducedOrbitWavePacket_le_rationalXi_rpow` |
| `Representation/Plancherel/DynamicOppositeContragredientScalar` | `unramifiedRegularInversion`, `rationalUnramifiedFunctionFieldInversion`, `rationalFunctionRegularAt_inversion_iff`, `rationalFunctionNonnegAt_inversion_iff`, `compactPictureDualPairing`, `ConditionalDynamicOppositeDualAdjunctionStatement` (target proved in `DynamicOppositeDualAdjunctionProof`), `ConditionalDynamicOppositeContragredientScalarStatement` (unproved target), `plancherelDensity_contragredient_of_contragredientScalar` | derived bilinear IV.1 (11) (p.283) with the smooth contragredient, for the actual opposite integrals on their convergence domains; IV.3 (2) (p.286) as `j_P(Ǎ ⊗ z⁻¹) = j_P(A ⊗ z)`; the density form of the fourth item of V.2.1 (p.292) | connected reductive `G`, `χ`, `hRefl`, `hCST`, both compact-parabolic factorizations, both Levi-projection premises for `P ∩ K` and `P̄ ∩ K`, and `A`. The scalar target takes independent conditional data for `A` and `Ǎ`, and the inclusions `_hinvForward`, `_hinvReverse` of the inverted convergence subsets in the full domains for `Ǎ`. The density corollary assumes the scalar target |
| `Representation/Plancherel/DynamicOppositeContragredientScalarReduction` | `compactPictureDualBilin`, `exists_compactPictureDualPairing_ne_zero`, `continuedOperator_dualAdjoint`, `continuedCompositeRationalScalar_dual`, `conditionalDynamicOppositeContragredientScalar_of_dualAdjunction` | derived implementation of "IV.3 (2) … résulte de IV.1 (11)" (p.286) | takes the dual adjunction target of the previous row, proved as `conditionalDynamicOppositeDualAdjunction` (`DynamicOppositeDualAdjunctionProof`); that theorem can discharge that argument, with no hypotheses beyond those of the two targets |
| `Representation/Plancherel/PlancherelWeightPositivity` | `dense_rationalUnitaryValue_pos`, `isOpen_rationalUnitaryValue_pos`, `plancherelDensity_ne_zero`, `dense_plancherelWeight_pos`, `isOpen_plancherelWeight_pos`, `standardLeviCharacterRestrictHomeomorph`, `rankOneGammaProduct_ne_top_of_isMaximalSplitTorus`, `dense_standardLeviPlancherelWeight_pos`, `standardLeviPlancherelWeightReal` (with `continuous_…`, `_nonneg`, `exists_…_le`, `dense_…_pos`, `ofReal_…`) | internal derived positivity of `µ` on a dense open subset of `Im X(M)` and of `O`, used for the definiteness asserted at VII.2 (p.319); Waldspurger states only `µ ≥ 0` (V.2.1) | `j_P ≠ 0`, `hreg` and nonnegativity of the unitary values of `j_P⁻¹` are hypotheses (the conclusions of the two targets of `DynamicOppositeUnitaryInverseRegularity`); on the orbit a maximal split torus `i` gives the finiteness of the gamma product. The real weight is continuous, nonnegative and bounded |
| `HarmonicAnalysis/HarishChandraSchwartz/InducedOrbitWavePacketOrthogonalityDense` and `HarmonicAnalysis/HarishChandraSchwartz/RationalInducedOrbitWavePacketOrthogonalityDense` | `dense_pos_of_forall_pos`, `unitaryOrbitWeightedProductCore_of_dense` (with `_inner`), `fourierOrbitSection_eq_zero_iff_forall_pairing_inducedOrbitWavePacket_eq_zero_of_dense`; on actual points `rationalUnitaryOrbitWeightedProductCore_of_dense` (with `_inner`), `rationalFourierOrbitSection_eq_zero_iff_forall_pairing_rationalInducedOrbitWavePacket_eq_zero_of_dense`, `rationalInducedFourierTransform_eq_zero_of_forall_pairing_rationalInducedOrbitWavePacket_eq_zero_of_dense` | one-orbit Hermitian product and detection of `ψ_f[O, P]` by wave packets in the proof of Corollary VII.2.3 (p.319), for a weight positive only on a dense set | real, bounded, continuous weight `u ≥ 0` with `{u > 0}` dense, and a finite measure on `Im X(M_I)` charging nonempty open sets; otherwise the hypotheses of `RationalInducedOrbitWavePacketOrthogonality` (standard `P_I` only; the vanishing premise of the Fourier corollary is Proposition VII.2.2 (i), unproved on actual points) |
| `Representation/Plancherel/PlancherelOrbitWavePacketOrthogonality` | `standardLeviPlancherelWeightRealBound`, `standardLeviPlancherelOrbitProductCore` (with `_inner`: `⟪s, t⟫ = ∫_O µ(ω) (s_ω, t_ω) dω`), `rationalFourierOrbitSection_eq_zero_iff_forall_pairing_standardLeviPlancherelWavePacket_eq_zero`, `rationalInducedFourierTransform_eq_zero_of_forall_pairing_standardLeviPlancherelWavePacket_eq_zero` | the one-orbit term of the VII.2 product (p.319) with the weight `µ`, and the detection step of the proof of Corollary VII.2.3 with the Plancherel wave packets | `hreg`, `j_P ≠ 0` and nonnegativity of `j_P⁻¹` on unitary characters as hypotheses; one standard pair `(O, P_I)`; any finite `ρX` charging nonempty open sets; `hcoeff` and the remaining hypotheses of `rationalFourierOrbitSmoothSectionLinear`. The sum over `Θ`, its constants and `C^∞(Θ)_inv` are not formalized |
| `Representation/Plancherel/DynamicOppositeConjugationScalar` | `rationalUnramifiedRegularFunctionsEquiv`, `rationalUnramifiedFunctionFieldEquiv`, `rationalFunctionRegularAt_equiv_iff`, `rationalFunctionNonnegAt_equiv_iff`, `leviConjugation`, `conjugateRepresentation`, `parameterConjugationIso`, `conjugate_parabolic_mul_compact`, `conjugate_oppositeParabolic_mul_compact`, `ConditionalDynamicOppositeConjugationScalarStatement` (target), `conditionalDynamicOppositeConjugationScalar_of_eq` | derived IV.3 (3) `j(wπ) = j(π)` (p.286) in transport form for an arbitrary rational point `g`: the scalar of `(gχg⁻¹, gKg⁻¹, gA)` is the transport of the scalar of `(χ, K, A)` along the isomorphism of the actual centralizer schemes | connected reductive `G`, `χ`, `hRefl`, `hCST`, a rational point `g`, both compact-parabolic factorizations for `K`, `A`, and independent conditional data on both sides. `_of_eq` accepts any compact open `K₁ = gKg⁻¹`, for example `K` when `g ∈ K`. Proved, as `conditionalDynamicOppositeConjugationScalar` (`DynamicOppositeConjugationScalarProof`) |
| `Representation/Plancherel/RationalPlancherelConstantConjugation` | `Langlands.GroupScheme.innerConjugate`, `roots_comp_iso`, `rankOneCocharacterSet_comp_iso`, `leviGamma_eq_of_conjugation`, `rankOneGamma_eq_of_conjugation`, `rankOneGammaProduct_eq_of_conjugation`, `plancherelConstant_eq_of_conjugation`, `plancherelDensityConstant_eq_of_conjugation`, each with `_conjugateCompact` and `_conjugate_of_mem_compact` variants where applicable | derived invariance `c(G|s·M) = c(G|M)` used in the proof of Lemma V.2.2 (p.294), and invariance of `∏_α γ(M_α|M)` and of the density constant `∏_α γ(M_α|M)²` (V.2, p.292) | affine locally finite type `G`, homomorphism `i : T → G`, cocharacter `ζ`, rational `g`; `K` replaced by `gKg⁻¹`, or kept when `g ∈ K`. The products in `ℝ≥0∞` are compared with no finiteness hypothesis. All results proved; no targets |
| `Representation/Plancherel/RationalPlancherelDensityConjugation` | `conditionalDynamicOppositeConjugationScalar_of_heq`, `fieldConstant_conjugation`, `plancherelDensity_conjugation_of_conjugationScalar`, `PlancherelDensityConjugationStatement` (target), `plancherelDensityConjugation_of_conjugationScalar` | derived transport form of the third item of V.2.1, `µ(sω) = µ(ω)` (p.292), for every rational point `g` | the density's data for `(i, ζ, K, A)` and for `(innerConjugate i g, ζ, K₁, gA)` with `K₁ = gKg⁻¹`. The proof assumes the unproved conjugation scalar target |
| `Representation/Plancherel/DynamicOppositePairScalar` | `changeLevi_mem_iff`, `leviChange` (with `_apply_coe`), `changeRepresentation`, `parameterChangeIso` (with `_hom_comp`, `_hom_points`), `parameterHomeomorph_parameterChangeIso`, `inverse_oppositeParabolic`, `inverse_oppositeRadical`, `inverse_oppositeParabolic_mul_compact`, `ConditionalDynamicOppositePairScalarStatement` (target), `conditionalDynamicOppositeInverseScalar_of_pair` | derived IV.3 (1) (pp.285–286) for the two parabolics of one opposite pair, in transport form: for a cocharacter `ψ` with `Z_G(ψ) = Z_G(χ)` whose parabolics and radicals are those of `χ` in the same or the exchanged order, the scalar of `ψ` is the transport of the scalar of `χ` along the isomorphism of the actual centralizer schemes. For `P' = P̄` no composition formula is needed; for maximal `M` this is all of IV.3 (1) | connected reductive `G`, `χ`, `ψ`, `hRefl`, `hCST`, equality of the centralizer subgroup functors, the four subgroup equalities on rational points as hypotheses, a compact open `K` with the four compact-parabolic factorizations, `A` on `M(F)`, and independent conditional data for `(χ, K, A)` and for `(ψ, K, A)`, with `A` viewed on `Z_G(ψ)(F) = M(F)` by `changeRepresentation`. The proved corollary derives the case `ψ = χ⁻¹` (exchanged order) from the target, supplying the centralizer, subgroup and factorization premises; it still takes independent conditional data for `χ⁻¹`. Proved, as `conditionalDynamicOppositePairScalar` (`DynamicOppositePairScalarProof`) |
| `Representation/Plancherel/DynamicCommonLeviComposition` | `commonDecomposition`, `centralizer_inverseCocharacter_eq`, `pairIntersectionHaar`, `pairQuotientMeasure` (with `_isCompatible`), `pairFullDomainRegion`, `pairFamily` (with `_spec`), `forwardFullDomainRegion_eq_pair`, `pairFamily_inverse_eq_conditionalForwardFamily`, `IsDistanceAdditive`, `DistanceAdditiveRadicalFactorizationStatement` (structural target), `ConditionalDynamicCommonLeviCompositionStatement` (target) | derived IV.1 (12) (p.283; `J` defined p.278, distance and product decomposition p.279): `J_{P₂|P₀} = J_{P₂|P₁} J_{P₁|P₀}` when `d(P₂, P₀) = d(P₂, P₁) + d(P₁, P₀)`, for the actual standard integrals `pairFamily` between three dynamic parabolics `P_G(ψᵢ)` with the literal Levi `M = Z_G(χ)(F)`, pointwise on the intersection of the three full domain regions. `pairFamily` is the published `standardInductionIntertwinerFamily` for two such parabolics; for `ψ = χ` and `ψ' = χ⁻¹`, with the published conditional squared-modulus proof, it is the opposite family `conditionalForwardFamily` (`J_{P̄|P}`, by `rfl`). The distance condition is in group form: `U₀ ∩ U₂ ≤ U₁` and `Ū₀ ∩ Ū₂ ≤ Ū₁` | connected reductive `G` with `[Smooth G.X.hom]`, `χ`, `ψ₀`, `ψ₁`, `ψ₂` with `Z_G(ψᵢ) = Z_G(χ)` (equal subgroup functors), a compact open `K` with the `SplitsAlong K ψ₀ ψ₁` and `SplitsAlong K ψ₁ ψ₂` instead of a special `K`, the squared-modulus identity `SquaredModulusCompatibility` for each of the three pairs (derived in the Library only for opposite pairs), `A` on `M(F)` and a parameter in the three full domain regions. The main target takes the structural target, the ordered product charts `(U₀ ∩ U₁) × V = U₁`, `(U₁ ∩ U₂) × W = U₂`, `(U₀ ∩ U₂) × (V × W) = U₂` with `V = U₁ ∩ Ū₀` and `W = U₂ ∩ Ū₁`, as a hypothesis. Nonemptiness of the domains, the rational continuation, the existence of `K` splitting along both pairs for a general triple (the `exists_isCommonLeviSplitting` treats two cocharacters and their inverses) and the equivalence of the group form with the root count are not established. The main statement is proved, as `conditionalDynamicCommonLeviComposition` (`DynamicCommonLeviCompositionProof`), and the structural `DistanceAdditiveRadicalFactorizationStatement` as `exactDistanceAdditiveRadicalFactorization` (`DynamicCommonLeviScaledComposition`) |
| `Representation/Plancherel/DynamicCommonLeviScalar` | `splitsAlong_of_radical_eq`, `splitsAlong_of_radical_eq_opposite`, `isCommonLeviSplitting_of_pair`, `ConditionalDynamicCommonLeviScalarStatement` (unproved target), `conditionalDynamicOppositePairScalar_of_commonLevi` | derived IV.3 (1) (pp.285–286) for an arbitrary `P' = P_G(ψ) ∈ P(M)`, in the transport form of the opposite-pair target: the canonical scalar of `(ψ, K, Aψ)` is the transport of the canonical scalar of `(χ, K, A)` along `parameterChangeIso χ ψ hM`. The source proof uses four instances of IV.1 (12), for the triples `(ψ⁻¹, χ, ψ)`, `(ψ, χ⁻¹, ψ⁻¹)`, `(χ⁻¹, ψ⁻¹, χ)` and `(χ, ψ, χ⁻¹)`; up to `SplitsAlong.inverse` their splitting premises are exactly the four fields of the `IsCommonLeviSplitting K χ ψ`. The proved lemmas give `IsCommonLeviSplitting Q χ ψ` for every compact open `Q` when the radicals of `ψ` are those of `χ` in the same or the exchanged order, and derive the opposite-pair target `ConditionalDynamicOppositePairScalarStatement` from this target | connected reductive `G` with `[Smooth G.X.hom]`, `χ`, `ψ`, `hRefl`, `hCST`, `Z_G(ψ) = Z_G(χ)` (equal subgroup functors), a compact open `K` with `IsCommonLeviSplitting K χ ψ` and the four compact-parabolic factorizations `G(F) = Q K` for `Q ∈ {P, P̄, P', P̄'}`, `A` on `M(F)`, and independent conditional data for `(χ, K, A)` and for `(ψ, K, Aψ)` with `Aψ = changeRepresentation χ ψ hM A`. The existence of a `K` with both the splitting and the factorizations is not proved. A proof also needs the rational continuation (Théorème IV.1.1) of the four non-opposite operators `J_{P'|P}`, `J_{P|P̄'}`, `J_{P̄'|P̄}`, `J_{P̄|P'}`, which the Library lacks and the target does not take as data, and the squared-modulus identity for non-opposite pairs |
| `HarmonicAnalysis/HarishChandraSchwartz/RationalDiscreteSeriesOrbitFinitenessStatement` | `RationalDiscreteSeriesOrbitFinitenessStatement` (statement), `isConnectedReductive_centralizerScheme` | Thm VIII.1.2 (p.321) | connected reductive `G`, split component `s : T → G`, Haar measure on `G(F)/A_G(F)`; no structural input |
| `Representation/Jacquet/StandardCasselmanPairing` | `standardCasselmanPairingData`, `exists_standardCasselmanPairing`, `exists_standardCasselmanPairing_splitComponent`, `SimultaneousStandardBasisAt.exists_casselmanPairing` | Thm I.4.1 (p.245) for actual standard `P_J`, on the cones of the whole split component | S1, S2 (as data `hζ`) |
| `Representation/Jacquet/DynamicCasselmanConstantTerm` | `dynamicCasselmanPairingData`, `exists_dynamicCasselmanPairing`, `dynamicParabolicModulus`, `IsDynamicConstantTerm`, `dynamicConstantTerm`, `existsUnique_dynamicConstantTerm` | Thm I.4.1 and Prop. I.6.2 (pp.245, 249–250) for every dynamic `P(χ)`, along the powers of `χ(t)`; normalized by `δ_U` | smooth affine `G`; no structural input |
| `HarmonicAnalysis/HarishChandraSchwartz/RationalWeights` | `rationalMinimalModulus` (`δ₀`), `rationalXi` (`Ξ`), `rationalHeight` (`σ`), `RationalSchwartzSpace` (`C(G)`), `denseRange_rationalSchwartzOfTestFunction`, `integral_rationalXi_mul_mul` | II.1 (pp.250–251), I.1 (p.242, `σ`), III.6 (pp.271–272), Lemma II.1.3 | `K` compact open with `G(F) = P₀(F) K` (S3, as data); closed matrix representation `ρ` (S4, as data) |
| `HarmonicAnalysis/HarishChandraSchwartz/RationalXiLowerBound` | `rationalXi_lowerBound`, `exists_sqrt_rationalMinimalModulus_le_rationalXi`, `rationalMinimalModulus_eq_one_of_mem_unipotent` | Lemma II.1.1, first inequality, on the weak chamber `C_A^+` | one basis member `H` with the factorization and contraction clauses (S1 for `J = ∅`), maximal split torus |
| `HarmonicAnalysis/HarishChandraSchwartz/RationalXiUpperBoundStatement` | `RationalXiUpperBoundStatement` (statement), `RationalXiUpperBoundStatement.xiUpperBound` | Lemma II.1.1, second inequality, in the uniform form of the proof of Lemma II.1.2 | S1 (`SimultaneousStandardBasisAt`), S3, S4 |
| `Representation/Jacquet/StandardCasselmanUniformAsymptotics` | `waldspurgerFace`, `exists_uniform_standardCasselmanPairing`, `exists_waldspurger_uniform_asymptotics`, `SimultaneousStandardBasisAt.exists_waldspurger_uniform_asymptotics`, `standardUnipotentPoints_le_empty`, `standardOppositeUnipotentPoints_le_empty` | Prop. I.4.3 (p.245): one nondegenerate `M_J`-invariant pairing for every face `J ⊆ Δ`, and for each `v, ℓ` a threshold `t` with the asymptotic identity at every dominant point `x` of `S(F)` for the face `waldspurgerFace i ν t x` | S1, S2 (as the hypothesis that every `J ⊆ Δ` has a standard cocharacter); unnormalized Jacquet actions |
| `HarmonicAnalysis/HarishChandraSchwartz/RationalXiCoefficient` | `rationalMinimalInduced` (`I_{P₀}^G 1`), `rationalSphericalVector` (`e_K`), `rationalSphericalFunctional` (`ℓ_K`), `rationalXi_eq_sphericalCoefficient`, `rationalMinimalInduced_isAdmissible`, `isSemidirectDecomposition_minimalStandard`, `continuous_projection_minimalStandard`, `exists_admissible_ofReal_rationalXi_mem`, `rationalXi_hasDynamicConstantTerm` | II.1 (pp.250–251): `Ξ(g) = ⟨π(g)e, e⟩` for `π = I_{P₀}^G 1`; `Ξ ∈ A(G)` (I.6, p.249); Prop. I.6.2 applied to `Ξ` in the dynamic form | S3 (data); a decomposition `P₀(F) = M₀(F) ⋉ U₀(F)` as datum, supplied for connected reductive `G` and generic `ν`; no structural input |
| `Representation/Jacquet/StandardCasselmanConstantTerm` | `standardRadicalModulus` (`δ_{U_J}`), `standardCone`, `IsStandardConstantTerm`, `standardConstantTerm`, `existsUnique_standardConstantTerm`, `standardConstantTerm_spec`, `standardConstantTerm_mul_radical`, `standardConstantTerm_oppositeRadical_mul`, `standardConstantTerm_mul_left`, `standardConstantTerm_mul_right` | Prop. I.6.2 (pp.249–250) for actual standard `P_J`, on the cones `|α(a)|_F < ε`, `α ∈ Δ(P_J)`, of the whole split component `A(F)` (the module's Markdown explains the equivalence with the source's `Σ(P_J)`-cones); normalized by `δ_{U_J}` | S1 (one basis for `J` with a compatible split component), S2 (as data `hζ`) |
| `HarmonicAnalysis/HarishChandraSchwartz/RationalMinimalInducedJacquetStatement` | `rationalMinimalInducedJacquet` (`V_P`, normalized by `δ_{U_J}`), `RationalMinimalInducedJacquetUnipotentStatement` (statement), `RationalMinimalInducedJacquetUnipotentStatement.splitComponent` | proof of Lemma II.1.1 (p.251): "`(π_P(a) − 1)^d` annule `V_P`" for `a ∈ A_M`, stated for every `z` central in `M_J(F)` with `d` uniform in `z` | connected reductive `G`, maximal split torus, generic `ν`; no structural input |
| `HarmonicAnalysis/HarishChandraSchwartz/RationalModulusFactorization` | `isSemidirectDecomposition_standard`, `continuous_projection_standard`, `standardParabolicPoints_empty_le`, `isSemidirectDecomposition_minimalUnipotent`, `standardLeviMinimalModulus` (`δ₀^{M_J}`), `standardUnipotentModulus` (`δ_{U_J}`), `rationalMinimalModulus_eq_mul`, `rationalMinimalModulus_eq_standardUnipotentModulus_of_commute`, `rationalMinimalModulus_eq_standardUnipotentModulus_splitComponent` | the modulus identity behind I.3 (p.243, `I_P^G V ≃ I_{P'}^G(I_{P∩M'}^{M'} V)`) and Lemma II.1.6 (pp.252–253) for `P₀ ⊂ P_J`: `δ₀ = δ₀^{M_J} δ_{U_J}` on `P₀(F) ∩ M_J(F)`, hence `δ₀ = δ_{U_J}` on elements central in `M_J(F)` | connected reductive `G`, maximal split torus, generic `ν`; no structural input |
| `HarmonicAnalysis/HarishChandraSchwartz/RationalXiSquareIntegrable` | `RationalXiSquareIntegrableStatement` (statement), `rationalXi_inv`, `rationalL2Weights`, `rationalConvolutionWeights`, `RationalXiSquareIntegrableStatement.l2Weights`, `RationalXiSquareIntegrableStatement.convolutionWeights` | Lemma II.1.5 (p.252, statement: `∫_G Ξ(g)²(1 + σ(g))^{-d} dg < ∞` for some `d`); Lemma II.1.4 (p.252, `Ξ(g⁻¹) = Ξ(g)`, proved for connected reductive `G`); adapters to the Library's `L2Weights` and `ConvolutionWeights` (III.6) | the statement: S1 and S5 (Cartan covering) at one compact open `K0`; S3, S4 as data. `rationalXi_inv`: connected reductive `G`, S3; no structural input. `rationalConvolutionWeights` also assumes `K ≤ rationalHeightSubgroup ρ` (Waldspurger's `τ(K) ⊂ GL_n(𝒪)`) |
| `HarmonicAnalysis/HarishChandraSchwartz/RationalXiSquareIntegrableOfUpperBound` | `rationalCartanCell`, `exists_measure_doubleCoset_uniformizerPowers_le`, `exists_cocharacterCoordinates_norm_le`, `rationalXiSquareIntegrable_of_upperBound` | Lemma II.1.5 (p.252), proved conditionally on `RationalXiUpperBoundStatement`; I.1 (5) upper volume bound in `G(F)` (p.241) and I.1 (6) lower coordinate-height bound on uniformizer powers (p.242) | the main implication assumes the analytic upper-bound statement `RationalXiUpperBoundStatement`, which the Library proves (`rationalXiUpperBound`, `RationalXiUpperBoundProof`); the conclusion retains S1 and S5 at a compact open `K0`, S3 and S4. No equality of `K0` with the compact defining `Ξ`, or height invariance under either compact, is required |
| `HarmonicAnalysis/HarishChandraSchwartz/RationalXiLevi` | `rationalLeviXi` (`Ξ^{M_J}`), `rationalLeviData`, `rationalXi_eq_integral_rationalLeviXi`, `isIwasawaPair_standardLevi`, `rationalMinimalModulus_eq_one_of_mem_standardUnipotent`, `standardUnipotentModulus_eq_one` | II.1 (p.252, definition of `Ξ^M`) and Lemma II.1.6 (pp.252–253) for standard `P_J ⊇ P₀`: `Ξ(g) = ∫_K δ_{U_J}(m_P(kg))^{1/2} Ξ^{M_J}(m_P(kg)) dk` | connected reductive `G`, maximal split torus, generic `ν`; S3 (data); S5 (Levi Iwasawa decomposition `hM`, data) |
| `HarmonicAnalysis/HarishChandraSchwartz/RationalTemperedInduction` | `IsRationalTempered`, `IsRationalLeviTempered`, `isRationalTempered_iff`, `isRationalLeviTempered_iff`, `exists_rationalHeight_projection_le`, `rationalLeviSigmaBound`, `isUnimodularModulus_standardUnipotentPoints`, `modularCharacter_standardParabolicPoints`, `rationalHasTemperedCoefficients_normalizedInduction`, `IsRationalLeviTempered.normalizedInduction` | III.2 (p.265, tempered representations: coefficients bounded by `cΞ(1 + σ)^r`) for `G(F)` and `M_J(F)`, independent of the closed matrix representation; Lemma III.2.3 (p.266) for standard `P_J`, `J` the root set of a set of simple roots: normalized induction of an admissible tempered representation of `M_J(F)` is tempered | connected reductive `G`, maximal split torus, generic `ν`; S3 (data, with `K ≤ rationalHeightSubgroup ρ` for III.2.3); S4; S5 (`hM`, data) |
| `HarmonicAnalysis/HarishChandraSchwartz/RationalSquareIntegrableDecay` | `RationalSquareIntegrableRapidDecayStatement` (statement), `rationalXi_uniformTranslationBound`, `rationalTranslationWeights`, `hasRapidlyDecreasingCoefficientsOn_rationalHeight_iff`, `mul_mem_rationalSchwartz`, `RationalSquareIntegrableRapidDecayStatement.mul_mem_rationalSchwartz` | Corollary III.1.2 (p.263, statement): coefficients of a representation square integrable modulo `A_G(F)` decrease rapidly on `G¹`; Lemma II.1.2 (p.251, proved with `d = 0`); III.7 (p.273, second paragraph): `f φ ∈ C(G)` for `f ∈ A(π)`, `φ ∈ C_c(G/G¹)` (proved from rapid decay) | the statement: S1 and S5 (Cartan covering) at a compact open `K0`; S3, S4 as data. Lemma II.1.2 and III.7: S3; no structural input |
| `HarmonicAnalysis/HarishChandraSchwartz/RationalConstantTerm` | `RationalConstantTermEstimateStatement` (statement), `StandardLeviCartanCovering`, `rationalIsConjModulus`, `rationalConstantTermData`, `standardLeviMinimalModulusOf_eq_one`, `rationalLeviXi_pos`, `rationalConstantTerm`, `coe_rationalConstantTerm` | Proposition II.4.5 (p.262, statement) for the opposite `P̄_J` of a standard parabolic, in the form `ConstantTermEstimate`; the constant term `f ↦ f^{(P_J)}`, `C(G) → C(M_J)` of III.6 (p.272), defined from the estimate | the statement: S1, S5 (Cartan covering of `G`) and S6 (Cartan covering of `M_J`) at a compact open `K0`; S3, S4, `hM` as data. `ConstantTermData`, `IsConjModulus`: no structural input |
| `HarmonicAnalysis/HarishChandraSchwartz/RationalCentralProjection` | `RationalSplitCenterHeightStatement` (statement), `range_le_standardLeviPoints`, `range_le_standardParabolicPoints`, `rationalMinimalModulus_eq_one_of_mem_center`, `rationalXi_mul_of_mem_range`, `rationalCentralWeights`, `rationalCentralProjection`, `RationalSplitCenterHeightStatement.enorm_rationalCentralProjection_le` | VIII.4 (p.327): the projections `p_χ` on `C(G)`; the estimate on `G¹` of the proof of Proposition VIII.4.1 (p.328); the statement: two height properties of `A_G(F)` and `G¹` derived from I.1, used implicitly in VIII.4 | the statement: none (connected reductive `G`, split component, closed `ρ`). `A_G(F) ⊆ P_J(F)`, `Ξ(ag) = Ξ(g)`: central `s`, S3. `p_χ`: `CentralWeights` (supplied by the statement) |
| `HarmonicAnalysis/HarishChandraSchwartz/RationalLeviScheme` | `leviSchemeCompact` (`j⁻¹(K)`), `isGenericCocharacter_leviTorusHom`, `standardParabolic_leviTorusHom_empty`, `standardUnipotent_leviTorusHom_empty`, `leviSchemePointsEquiv`, `mem_standardParabolicPoints_leviTorusHom_iff`, `standardLeviMinimalModulus_leviHom`, `isIwasawaPair_leviSchemeCompact`, `rationalXi_leviScheme`, `rationalHeight_restrict_leviHom`, `xi_map` | I.1 (p.240, `M ∩ K` has for `M` the properties of `K` for `G`) and II.1 (p.252, `Ξ^M` is `Ξ` for `M`) for the Levi group scheme `L = Standard.leviScheme i ν J` with `j : L → G`: `P₀^L(F) = P₀(F) ∩ M_J(F)` and `U₀^L(F) = M_J(F) ∩ U₀(F)` through `j`, `δ₀^L = δ₀^{M_J}`, `Ξ` of `L` for `j⁻¹(K)` is `Ξ^{M_J} ∘ j`, `σ_{ρ ∘ j} = σ_ρ ∘ j` | connected reductive `G`, maximal split torus, generic `ν`; S3 (data); S5 (`hM`, data) for the Iwasawa pair and `Ξ`; no structural input for the parabolic, modulus and height comparisons |
| `Geometry/Building/SpecialCompactLeviMinimalParabolicProof` | `Langlands.GroupScheme.standardLeviMinimalParabolicCompatibility : StandardLeviMinimalParabolicCompatibilityStatement` | algebraic part of Renard V.5.1(5), printed p.122 / PDF p.128, used in Waldspurger I.1 (p.240): connected reductivity of the actual standard Levi, ambient and intrinsic minimal parabolicity, all-test pullback equality, and the literal rational-point image intersection | arbitrary nonarchimedean local `F`, connected reductive `G`, maximal split torus `i`, generic `ν`, `J ⊆ simpleRelativeRoots i ν`, arbitrary universe and characteristic; no extra structural or analytic premise. The same torus and cocharacter are retained. This proves no inherited compact, Iwasawa or Cartan assertion |
| `HarmonicAnalysis/HarishChandraSchwartz/RationalLeviTempered` | `hasXiBoundedCoefficients_comp_continuousMulEquiv_iff`, `hasTemperedCoefficients_comp_continuousMulEquiv_iff`, `leviSchemeRepresentation`, `hasXiBoundedCoefficients_leviSchemeRepresentation_iff`, `isRationalTempered_leviSchemeRepresentation_iff` | derived comparisons for III.2 (p.265) and the pure `cΞ^M` bound in the proof of VI.2.2 (pp.298–299), using I.1 (p.240) and II.1 (p.252): canonical same-carrier `SmoothRep` pullback identifies both the pure Xi bound and temperedness on `M_J(F)` with their counterparts on `L(F)` | generic comparisons: topological group isomorphism and corresponding arbitrary weights, using the same smooth algebraic dual and bound constants. Levi comparisons: connected reductive `G`, maximal split torus, generic `ν`, `J ⊆ Δ`, compact open `K`, S5 (`hM`, data). Only temperedness uses a finite nonempty matrix representation `ρ`; the pure Xi comparison uses no height or matrix representation. Closedness of `ρ` and admissibility are unnecessary |
| `HarmonicAnalysis/HarishChandraSchwartz/GroupTransport` | `nu_comp_equiv`, `CompactOpenSubgroup.comap`, `Level.comap`, `Space.comapEquiv`, `Space.nu_comapEquiv` | derived compatibility for III.6 (pp.271–272): pullback along a topological group isomorphism preserves every defining seminorm and identifies the existing locally convex inductive-limit Schwartz spaces | arbitrary groups in independent universes with topologies, a topological group isomorphism and corresponding real weights; no positivity, measure or structural hypothesis |
| `HarmonicAnalysis/HarishChandraSchwartz/RationalLeviSchwartz` | `rationalLeviSchwartzEquiv`, `rationalLeviSchwartzEquiv_apply`, `rationalLeviSchwartzEquiv_symm_apply`, `nu_rationalLeviSchwartzEquiv` | derived comparison for III.6 (pp.271–272): `C(M_J)` (the codomain of `rationalConstantTerm`) is continuously complex-linearly equivalent to the Schwartz space of `L(F)`, for `j⁻¹(K)` and `ρ ∘ j`, with equality of every `ν_r` | connected reductive `G`, maximal split torus, generic `ν`, `J ⊆ Δ`, compact open `K`, finite nonempty matrix representation `ρ`, S5 (`hM`, data); closedness or faithfulness of `ρ` is unnecessary |
| `HarmonicAnalysis/HarishChandraSchwartz/RationalLeviMeasure` (measure comparisons) | `leviSchemeMeasure`, `map_leviSchemeMeasure`, `leviSchemeMeasure_compact_eq_one`, `squareIntegrableWeight_leviSchemeMeasure_iff`, `l2Weights_leviSchemeMeasure_iff`, `pairing_rationalLeviSchwartzEquiv`, `eLpNorm_leviSchemeMeasure`, `memLp_leviSchemeMeasure_iff`, `convolution_leviSchemeMeasure`, `integrable_convolution_leviSchemeMeasure_iff` | derived change of variables for I.1 (p.240, inherited compact and subgroup Haar normalization), II.1.5 (p.252, square weight), III.6 (pp.271–272, convolution) and VII.1 (p.313, pairing): pull the chosen subgroup measure back to `L(F)` through `leviSchemePointsEquiv`, preserving its exact scale | arbitrary chosen measure for the map, compact-volume, pairing, norm, `MemLp` and convolution comparisons; Haar transport requires the chosen measure to be Haar. Weight and Schwartz specializations have the hypotheses of `RationalLeviSchwartz` (including explicit `hM`); these comparisons alone prove no convergence estimate |
| `HarmonicAnalysis/HarishChandraSchwartz/RationalLeviMeasure` (conditional II.1.5 consumers) | `RationalXiSquareIntegrableStatement.leviSquareIntegrableWeight`, `RationalXiSquareIntegrableStatement.leviL2Weights`, `rationalLeviSquareIntegrableWeight_of_upperBound`, `rationalLeviL2Weights_of_upperBound` | derived application of II.1.5 (p.252) to the actual standard Levi scheme, followed by measure transport: `SquareIntegrableWeight` and `L2Weights` on `M_J(F)` for `Ξ^{M_J}`, the restricted height and the original chosen Haar measure | connected reductive `G` (`hG`), maximal split torus (`hi`), generic `ν` (`hν`), `J ⊆ Δ` (`hJ`), compact open `K`, finite nonempty closed matrix representation `ρ`, explicit Levi Iwasawa `hM`, chosen Haar measure `μM`; S1 and S5 (`SimultaneousStandardBasisAt` and `FiniteCartanCovering`) at a separate compact open `K0L` in `L(F)`. The first pair also takes the global analytic `RationalXiSquareIntegrableStatement`; the second takes the global analytic `RationalXiUpperBoundStatement`. No additional ambient Iwasawa premise is needed; `K0L` need not be the inherited compact |
| `HarmonicAnalysis/HarishChandraSchwartz/RationalInducedCoefficients` | `rationalInducedCoefficientMap` (`E_P^G`), `rationalInducedCoefficientMap_integral`, `rationalInducedCoefficientMap_action`, `rationalInducedCoefficientMap_biInvariant`, `range_rationalInducedCoefficientMap`, `norm_rationalInducedCoefficientMap_le_rationalXi`, `rationalTwistedSection`, `norm_rationalInducedCoefficientMap_twist_le_rationalXi` | V.1 (p.288, `E_P^G`), Lemma VI.2.2 (p.298) for one representation and uniformly over unitary unramified twists (reduced form of its proof) | standard `P_I`; S3 (data), S5 (`hM`, data); coefficient bound of `ω` by `Ξ^{M_I}` (`hcoeff`, conclusion of Cor. III.1.2) |
| `HarmonicAnalysis/HarishChandraSchwartz/RationalInducedOrbitWavePacket` | `leviRationalUnitaryCoordinates` (circle coordinates of `Im X(M_I)`), `rationalInducedSmoothOrbitSections` (`C^∞(O, P)`), `rationalInducedOrbitCoefficientMap`, `exists_norm_rationalInducedOrbitCoefficientMap_le_rationalXi`, `rationalInducedOrbitWavePacket` (`f_ψ`), its `Ξ` bound, bi-invariance, integrability, linearity, parameter integral | VI.1 (p.295, `C^∞(O, P)`), Lemma VI.2.2 on `C^∞(O, P)`, VI.3 (p.302, `f_ψ` with a weight `w` for `µ`) | as above; orbit data `C`, `mu`, `hsq` general; finite stabilizer; a measure `ρX` on `Im X(M_I)` and a weight `w : O → ℂ`. The definition, bi-invariance and homogeneity hold for any `ρX` and `w`, the parameter integral needs `w` almost everywhere strongly measurable; the `Ξ` bound needs `ρX` finite, `w` bounded and the coefficient bound `hcoeff` for `π` (Cor. III.1.2); integrability of the integrand, additivity and the linear map `ψ ↦ f_ψ` need in addition `w` almost everywhere strongly measurable. No invariance of `ρX` is used here |
| `HarmonicAnalysis/HarishChandraSchwartz/RationalInducedOrbitWavePacketDecay` | `rationalValuationCoordinatesHom` (`n_G`, kernel `G(F)¹`), `latticeFactorMatrix`, `leviValuationRestrictionMatrix` (`Im X(G) → Im X(M_I)` in coordinates), `exists_norm_rationalInducedOrbitWavePacket_le_rationalXi_rpow` | first bound of the proof of Prop. VI.3.1 (p.303), `|f_ψ| ≤ c Ξ (1 + ‖n_G‖)^{-r}` | as above, with `ρX` finite **and left invariant** (`[IsFiniteMeasure ρ] [ρ.IsMulLeftInvariant]`, as for the normalized Haar measure of I.1 (p.239) and VI.3 (p.302)); `w` smooth in the circle coordinates (`IsSmoothFiniteTorusFunction`); `hcoeff` for `π`; `‖n_G‖` in place of `|H_G|`. Left invariance is essential: the proof is Fourier cancellation on the compact torus, and with `ρX` = Haar + a Dirac mass the bound fails for `r > 0` |
| `HarmonicAnalysis/HarishChandraSchwartz/RationalInducedFourierTransform` | `rationalInducedFourierTransform` (`f̂(ω, P)`), `compactOpenCofinal_standardLevi`, Lemma VII.1.1 (i)–(iii) on actual points, uniqueness from (ii) | VII.1 (p.313), Lemma VII.1.1 (p.314) | S3, S4, S5 (data); conclusion of Lemma II.1.5 (`hsw`); temperedness of `ω` (`hTA`) |
| `HarmonicAnalysis/HarishChandraSchwartz/RationalInducedOrbitFourierPairing` | `rationalFourierOrbitSection` (`ψ_f[O, P]`), coherence, `pairing_rationalInducedOrbitWavePacket_eq_integral_productPairing` | VII.1 (p.316, `ψ_f[O, P]`), formula (1) of the proof of Prop. VII.2.2 (p.319) for any `f ∈ C(G)` | as in the row `RationalInducedFourierTransform`; for the wave packet, `ρX` finite, `w` bounded and almost everywhere strongly measurable, and `hcoeff` for `π` (no invariance of `ρX`, no smoothness of `w`); `r = ψ_f[O, P]` given |
| `HarmonicAnalysis/HarishChandraSchwartz/RationalFourierOrbitSmoothness` | `rationalLeviXi_inv`, `rationalLeviTranslationWeights`, `laurentExponent_leviRationalUnitaryCoordinates`, `rationalFourierOrbitSmoothSectionLinear` (`f ↦ ψ_f[O, P] ∈ C^∞(O, P)`), `pairing_rationalInducedOrbitWavePacket_eq_integral_fourier` | Prop. VII.1.3 (p.316, without continuity), Lemmas II.1.2 and II.1.4 for `M_J`, formula (1) with `ψ_f[O, P]` from VII.1.3 | as above; Lemma II.1.5 for `M_I` (`hswM`), Prop. II.4.5 (`hE`), S5 (`K ∩ P = (K ∩ M)(K ∩ U)`), measure normalizations, `‖H_{M_I}‖ ≤ C(1 + σ)`, an integrability condition |
| `HarmonicAnalysis/HarishChandraSchwartz/RationalInducedOrbitWavePacketOrthogonality` | `rationalUnitaryOrbitWeightedProductCore` (+ `_inner`), `rationalFourierOrbitSection_eq_zero_iff_forall_pairing_rationalInducedOrbitWavePacket_eq_zero`, `rationalInducedFourierTransform_eq_zero_of_forall_pairing_rationalInducedOrbitWavePacket_eq_zero` | VII.2 (p.319): the hermitian product on `C^∞(O, P)` for one orbit, with a weight `u` in place of the Plancherel density `µ`; `ψ_f[O, P] = 0` iff `(f_ψ, f)_G = 0` for all wave packets `f_ψ` of weight `u` (the deduction of Cor. VII.2.3 for one orbit) | as in the row above, and `hcoeff` for `π` (Cor. III.1.2); finite stabilizer of the class of `π` and finite quotient `M_I/(M_I¹ C)`; a finite measure `ρX` on `Im X(M_I)` positive on nonempty open sets and a real, bounded, continuous, strictly positive weight `u` on the orbit. The conditional Plancherel weight need not be strictly positive, so its specialization goes through the dense versions listed above (`PlancherelOrbitWavePacketOrthogonality`); positivity of `u` is essential (for `u = 0` every wave packet vanishes) |
| `HarmonicAnalysis/HarishChandraSchwartz/RationalInducedConstantTermFourier` | `integrable_rationalCoefficientPairingIntegrand`, `rationalLeviL2Weights`, `rationalConstantTermInducedFourierTransform` (`f̂^{(P),Ind}(ω)`), `rationalInducedFourierTransform_eq_rationalConstantTermInducedFourierTransform`, vanishing of `f̂(ω, P)`, `ψ_f[O, P]` and `(f_ψ, f)_G` when `f^{(P),Ind} = 0` | VII.1 (p.315, `f̂^{(P),Ind}(ω)`), Lemma VII.1.2 and its absolute convergence, first sentence of the proof of Lemma VIII.2.1 (p.321), vanishing in the proof of Lemma VIII.2.3 (p.322), one `(O, P)` | as above; Cor. III.1.2 for `ω` and each orbit representative (`hcoeff`, `hcoeffA`); discharges the integrability condition of the row `RationalFourierOrbitSmoothness` |
| `HarmonicAnalysis/HarishChandraSchwartz/RationalCuspidalConvolution` | `RationalConstantTermIndVanishes` (`f^{(P),Ind} = 0`), `rationalUnipotentHaar_isInvInvariant`, `isUnipotentCuspidal_iff_rationalConstantTermIndVanishes`, `convolution_rationalInducedOrbitWavePacket_eq_zero`, `convolution_rationalInducedOrbitWavePacket_left_eq_zero` | Lemma VIII.2.1 condition for one standard `P`; proof of Lemma VIII.2.3 (p.322): `f₁ ∗ f_ψ = f_ψ ∗ f₁ = 0` | as in the row above; for the wave packet, `ρX` finite, `w` bounded and almost everywhere strongly measurable, and `hcoeff` for `π` (no invariance of `ρX`) |
| `HarmonicAnalysis/HarishChandraSchwartz/OrbitCoefficientBound` | `HasXiBoundedCoefficients`, `.of_equiv`, `.twist`, `.unitaryOrbitRepresentative`, `rationalLeviXi_coefficientBound_unitaryOrbitRepresentative` | proof of Lemma VI.2.2 (pp.298–299): coefficient bound `cΞ^M` from Cor. III.1.2, transferred to every member of the orbit | the bound for `π` (`hcoeff`) remains a hypothesis (Cor. III.1.2 is open and bounds only on `G¹`); supplies `hcoeffA` of the two rows above |
| `HarmonicAnalysis/HarishChandraSchwartz/RationalInducedFixedOrbits` | `HasInducedFixedVector`, `inducedDiscreteSeriesFixedOrbits` (`Θ^H` for one `P`), `inducedFourierTransform_eq_zero_of_fixedVectors_eq_bot`, `hasInducedFixedVector_twist_iff`, `mk_mem_inducedDiscreteSeriesFixedOrbits_iff`, `finite_inducedDiscreteSeriesFixedOrbits`, actual `finite_rationalInducedDiscreteSeriesFixedOrbits`, `rationalFourierOrbitSection_eq_zero_of_fixedVectors_eq_bot`, `exists_finite_rationalFourierOrbitSection_ne_zero` | VIII.1 (p.321, `Θ^H`), Remarque VIII.1.3 (i), (ii) for one standard `P_I` | Theorem VIII.1.2 for `M_I(F)` as hypothesis `hfin`; twist independence needs `H ≤ K`; hypotheses of `rationalInducedFourierTransform` |
| `HarmonicAnalysis/HarishChandraSchwartz/RationalLeviDiscreteSeriesOrbitFiniteness` | `centralSubgroupCoefficientNorm_pullback`, `isSquareIntegrableModCentralSubgroup_comp_iff`, `discreteSeriesOrbitPullback` (transport along `H ≃ₜ* G`), `finite_discreteSeriesFixedOrbits_of_pullback`, `rationalLeviSplitCenter` (`A_{M_I}(F)` in `M_I(F)`), `exists_isSplitComponent_standardLevi`, `finite_discreteSeriesFixedOrbits_standardLevi` | Théorème VIII.1.2 for the Levi subgroups `M_I(F)` (as used in Remarque VIII.1.3 and the induction of VIII) | the published, open `RationalDiscreteSeriesOrbitFinitenessStatement` (hypothesis `hVIII`); connected reductivity and split component of the Levi scheme are proved (`standardLeviSplitComponentStatement`) |
| `HarmonicAnalysis/HarishChandraSchwartz/RationalThetaFixedFiniteness` | `rationalThetaFixed` (`Θ^H` over standard `P_I`, Sigma set), `mem_rationalThetaFixed`, `finite_rationalThetaFixed`, `finite_rationalInducedDiscreteSeriesFixedOrbits_of_statement`, `exists_finite_rationalFourierOrbitSection_ne_zero_of_statement`, `exists_finite_sigma_rationalFourierOrbitSection_ne_zero_of_statement` | Θ (VI.3, p.305), `Θ^H`, Théorème VIII.1.2, Remarque VIII.1.3 (i), (ii) (p.321) over all standard `P_I` | the published, open `RationalDiscreteSeriesOrbitFinitenessStatement` (`hVIII`); semi-standard `P` not covered |
| `HarmonicAnalysis/HarishChandraSchwartz/RationalFourierOrbitContinuity` | `rationalInducedOrbitSectionSpace` (`C^∞(O, P)` with VI.3 topology), `productInducedOrbitRepresentation_rationalFourierOrbitSection`, `rationalFourierOrbitSmoothSectionLinear_mem_orbitSectionLevelSubmodule`, `rationalFourierOrbitSectionCLM`, `toSections_rationalFourierOrbitSectionCLM`, `rationalFourierOrbitSectionCLM_apply_val` | Proposition VII.1.3 second assertion (continuity, p.316), VI.3 topology (p.301), Lemma VII.1.1 (i) consequence | as in the row `RationalFourierOrbitSmoothness` |
| `Representation/Plancherel/DynamicOppositeHermitianAdjunctionProof` | `conditionalDynamicOppositeHermitianAdjunction` | Hermitian convergence-domain form of IV.1 (11), used in IV.3 (6), pp.283, 287 | exact published target, including both compact factorizations and splittings, invariant positive form, forward parameter and conjugate-inverse reverse-domain premise; no rational continuation is asserted |
| `Representation/Plancherel/DynamicOppositeDualAdjunctionProof` | `conditionalDynamicOppositeDualAdjunction` | bilinear contragredient convergence-domain form of IV.1 (11), p.283, in both orientations | exact published target, including both compact factorizations and splittings and inverse-parameter full-domain premises for the smooth contragredient; no reflexivity or admissibility premise is added |
| `HarmonicAnalysis/HarishChandraSchwartz/SmoothTorusTensorTopology` | `smoothTorusSeminorm`, `smoothTorusFunctionTopology`, `smoothTensorCoordinates`, `smoothTensorFiniteProductTopology`, `SmoothTensorBasisIndependenceStatement` | internal ordered-angle-derivative and finite-basis implementation of VI.1 and VI.3, pp.295–296, 301 | a finite product of circles and a finite complex coefficient basis; the basis-independence comparison is a target, not a proof |
| `HarmonicAnalysis/HarishChandraSchwartz/OrbitSectionFixedTensor` | `orbitSectionFixedCoefficients`, `orbitSectionProductLevi_isAdmissible`, `finiteDimensional_orbitSectionFixedCoefficients`, `orbitSectionLevelTensor`, `orbitSectionLevelTensor_evaluation`, `orbitSectionLevelTensor_injective` | actual product fixed coefficients and faithful algebraic tensor realization of sections, VI.1 and VI.3 | compact `K`, compact-open cofinal Levi and irreducible admissible `π` imply proved finite dimensionality of the actual `H × H` fixed submodule for every open `H ≤ K`; level maps use the existing semidirect, compact-picture and orbit-section data and retain self-twist compatibility |
| `HarmonicAnalysis/HarishChandraSchwartz/OrbitSectionFiniteProductTopology` | `orbitSectionLevelCoordinates`, `orbitSectionFiniteProductLevelTopology`, `orbitSectionFiniteProductTopology`, `OrbitSectionFiniteProductTopologyStatement` | independent finite-product level and locally convex inductive-limit topologies, VI.3, p.301 | actual sections and their injective coordinate map, any finite basis of actual fixed coefficients; the aggregate concludes a finiteness-witness family and every-basis level and total comparison. Finiteness is proved by the preceding adapter; the topology equalities are proved in `OrbitSectionFiniteProductTopologyProof`, under the hypothesis `CompactOpenCofinal M` |
| `HarmonicAnalysis/HarishChandraSchwartz/RationalOrbitSectionFiniteProductTopology` | `rationalOrbitSectionFixedCoefficients`, `finiteDimensional_rationalOrbitSectionFixedCoefficients`, `rationalOrbitSectionFiniteProductTopology`, `RationalOrbitSectionFiniteProductTopologyStatement` | actual standard-Levi specialization of VI.3's finite-product topology | arbitrary nonarchimedean local field, connected reductive `G`, maximal split torus, generic cocharacter, standard index, compact `K` with the minimal Iwasawa condition, irreducible admissible `π` on the literal standard Levi; actual fixed-coefficient finiteness is proved using `compactOpenCofinal_standardLevi`; the level and total comparisons remain open |

The analysis and Jacquet modules are in namespaces `Langlands.HarishChandraSchwartz`,
`Langlands.Jacquet` or `Langlands.BruhatTits.SpecialCompact`; the constant construction is in
`Langlands.Plancherel.RationalDynamicSource`, the density is in
`Langlands.Plancherel.RationalPlancherelDensity`, and the scalar target and its rational-function
predicates are in `Langlands.Plancherel`. Their paired Markdown files give the exact statements.

The four scalar and density modules below first appeared in the Library at the commits listed; their
Lean and Markdown files there match the present ones:

| Pair | First appeared at Library commit |
|---|---|
| [RationalPlancherelDensityPositivity](../../Langlands/Representation/Plancherel/RationalPlancherelDensityPositivity.md) | `0c3f30c24701c74d5474fca3fbb5324a99aa1d58` |
| [DynamicOppositeHermitianAdjunctionStatement](../../Langlands/Representation/Plancherel/DynamicOppositeHermitianAdjunctionStatement.md) | `0c3f30c24701c74d5474fca3fbb5324a99aa1d58` |
| [DynamicOppositeUnitaryNonnegativity](../../Langlands/Representation/Plancherel/DynamicOppositeUnitaryNonnegativity.md) | `85c2fe719cf62e96f22aaf4ca03961c5814d086b` |
| [DynamicOppositeUniformNonvanishing](../../Langlands/Representation/Plancherel/DynamicOppositeUniformNonvanishing.md) | `db8d6b3d466f2fd453a4df4624ce6c90db8eed46` |

These modules state the targets and prove the reductions at their displayed scope.
Those four modules alone do not prove Hermitian adjunction or the full-unitary scalar
assertion. The adjunction proof below closes the former at its stated convergence-domain scope.

The fifteen further modules below first appeared in the Library at the commits listed; their
Lean and Markdown files at commit `c2a69151…` are those of the commits listed:

| Pair | First appeared at Library commit |
|---|---|
| [DynamicOppositeUnitaryInverseRegularity](../../Langlands/Representation/Plancherel/DynamicOppositeUnitaryInverseRegularity.md) | `e5365902d74534dbf1622c06e695dffdc128d723` |
| [RationalUnitaryRegularValue](../../Langlands/Representation/Plancherel/RationalUnitaryRegularValue.md) | `e5365902d74534dbf1622c06e695dffdc128d723` |
| [StandardLeviPlancherelWeight](../../Langlands/Representation/Plancherel/StandardLeviPlancherelWeight.md) | `b3a1bdaf15715f16a43643513b7cbb6cbb58ef3a` |
| [DynamicOppositeContragredientScalar](../../Langlands/Representation/Plancherel/DynamicOppositeContragredientScalar.md) | `c40a01345b2f4172fa41e07ff31644b40e695003` |
| [DynamicOppositeContragredientScalarReduction](../../Langlands/Representation/Plancherel/DynamicOppositeContragredientScalarReduction.md) | `c40a01345b2f4172fa41e07ff31644b40e695003` |
| [PlancherelWeightPositivity](../../Langlands/Representation/Plancherel/PlancherelWeightPositivity.md) | `b3a1bdaf15715f16a43643513b7cbb6cbb58ef3a` |
| [InducedOrbitWavePacketOrthogonalityDense](../../Langlands/HarmonicAnalysis/HarishChandraSchwartz/InducedOrbitWavePacketOrthogonalityDense.md) and [RationalInducedOrbitWavePacketOrthogonalityDense](../../Langlands/HarmonicAnalysis/HarishChandraSchwartz/RationalInducedOrbitWavePacketOrthogonalityDense.md) | `b3a1bdaf15715f16a43643513b7cbb6cbb58ef3a` |
| [PlancherelOrbitWavePacketOrthogonality](../../Langlands/Representation/Plancherel/PlancherelOrbitWavePacketOrthogonality.md) | `b3a1bdaf15715f16a43643513b7cbb6cbb58ef3a` |
| [DynamicOppositeConjugationScalar](../../Langlands/Representation/Plancherel/DynamicOppositeConjugationScalar.md) | `b3a1bdaf15715f16a43643513b7cbb6cbb58ef3a` |
| [RationalPlancherelConstantConjugation](../../Langlands/Representation/Plancherel/RationalPlancherelConstantConjugation.md) | `b3a1bdaf15715f16a43643513b7cbb6cbb58ef3a` |
| [RationalPlancherelDensityConjugation](../../Langlands/Representation/Plancherel/RationalPlancherelDensityConjugation.md) | `b3a1bdaf15715f16a43643513b7cbb6cbb58ef3a` |
| [DynamicOppositePairScalar](../../Langlands/Representation/Plancherel/DynamicOppositePairScalar.md) | `7f5b5f04a855fc0b4671393213c87415a6ee2aaf` |
| [DynamicCommonLeviComposition](../../Langlands/Representation/Plancherel/DynamicCommonLeviComposition.md) | `aeb3911c4e1bf6e3a2f653e874e4ebc422d2a61a` |
| [DynamicCommonLeviScalar](../../Langlands/Representation/Plancherel/DynamicCommonLeviScalar.md) | `4abbe7aabd9c92005d91c9d5bba86b879e928bb3` |

As above, these modules state the targets and prove the reductions at their displayed scope; none
of the targets becomes a theorem by the statement or a reduction alone. The
dual-adjunction proof below separately discharges that reduction's adjunction argument.

## Topology and adjunction modules, 16 November 2026

The following six modules are in the Library. The four topology
modules are definitions and statements for VI.1 and VI.3; they do not prove topology equality.
The last two modules are exact proofs of adjunction statements of the modules above.

| Pair | First appeared at Library commit |
|---|---|
| [SmoothTorusTensorTopology](../../Langlands/HarmonicAnalysis/HarishChandraSchwartz/SmoothTorusTensorTopology.md) | `ba00e0970dd9ba6222ccc056ca2ee7f06bcc8181` |
| [OrbitSectionFixedTensor](../../Langlands/HarmonicAnalysis/HarishChandraSchwartz/OrbitSectionFixedTensor.md) | `ba00e0970dd9ba6222ccc056ca2ee7f06bcc8181` |
| [OrbitSectionFiniteProductTopology](../../Langlands/HarmonicAnalysis/HarishChandraSchwartz/OrbitSectionFiniteProductTopology.md) | `af5d652c2f2ff5b35b4ce4dbbf7cbec8bbf3e99e` |
| [RationalOrbitSectionFiniteProductTopology](../../Langlands/HarmonicAnalysis/HarishChandraSchwartz/RationalOrbitSectionFiniteProductTopology.md) | `af5d652c2f2ff5b35b4ce4dbbf7cbec8bbf3e99e` |
| [DynamicOppositeHermitianAdjunctionProof](../../Langlands/Representation/Plancherel/DynamicOppositeHermitianAdjunctionProof.md) | `b3dcc8cc4c93f1140c6b34374f589ccc637a1a22` |
| [DynamicOppositeDualAdjunctionProof](../../Langlands/Representation/Plancherel/DynamicOppositeDualAdjunctionProof.md) | `ccd5c6bb63352c109b2bfde422a65c2dd78e57fd` |

The actual section coordinate maps are injective and recover the original compact
restriction at each parameter. They do not assert surjectivity onto arbitrary smooth
fixed-coefficient families. Self-twist covariance remains part of the actual section
carrier. Fixed-coefficient finite dimensionality is already proved, generically and on
actual rational standard Levi subgroups, using product and contragredient admissibility
and the existing compact-fixed-vector theorem. The optional derivative-permutation
target is not a premise of the section comparisons.

The remaining topology comparisons are three statements (declaration prefix
`Langlands.HarishChandraSchwartz.`):

| Target | Proof in the Library |
|---|---|
| `SmoothTensorBasisIndependenceStatement` | `smoothTensorBasisIndependence` (`SmoothTorusTensorBasisIndependenceProof`) |
| `OrbitSectionFiniteProductTopologyStatement` | `orbitSectionFiniteProductTopologyStatement_holds` (`OrbitSectionFiniteProductTopologyProof`), under the hypothesis `CompactOpenCofinal M` |
| `RationalOrbitSectionFiniteProductTopologyStatement` | `rationalOrbitSectionFiniteProductTopologyStatement_holds` (`RationalOrbitSectionFiniteProductTopologyProof`) |

The separate
scalar basis-independence result need not be a prerequisite for a generic proof that
directly establishes the comparison for every basis. No additional finiteness statement is
needed.

The two full conclusions of VI.3.1 are stated in
`Langlands/HarmonicAnalysis/HarishChandraSchwartz/StandardLeviPlancherelWavePacketSchwartz.lean`
(`StandardLeviPlancherelWavePacketMembershipStatement`,
`StandardLeviPlancherelWavePacketContinuityStatement`,
`StandardLeviPlancherelWavePacketSourceNormalizedStatement`; this note records no proof of
them; the Library derives the last, the conjunction of the first two, from the derivative estimates `StandardLeviPacketDerivativeEstimates`, by `standardLeviPlancherelWavePacketSourceNormalized_of_estimates`): every actual
mu-weighted smooth orbit section has pointwise integrable coefficient and full
`RationalSchwartzSpace` wave packet, and the integral is realized by a continuous
complex-linear map from the existing `rationalInducedOrbitSectionSpace`. The principal
source specialization is meant to use `standardLeviPlancherelWeight`, retain its continuation,
convergence, generic irreducibility and inverse-scalar regularity premises, and
not add a coefficient Xi bound or the desired output-seminorm estimates as premises.
The central-valuation decay theorem already in `StandardLeviPlancherelWeight` retains
`hcoeff` and does not supply this full Schwartz conclusion. The compact subgroup used
for the scalar and the one used for wave-packet estimates may differ.

The I.1 source measure fixes probability Haar on the split-component character group,
not generally on the full unramified character group or its orbit. The full character
measure has mass equal to the finite restriction-kernel cardinality; the orbit measure
is the reciprocal stabilizer cardinality times its pushforward. The source normalization
reuses `RationalCharacterHaar`, `RationalNormalizedOrbitMeasure` and the proved finite-measure
interface `RationalOrbitIntegration`, supplying the thin standard-Levi transport
adapter and keeping the valuation-image finite-index and subgroup-identification
obligations visible. Topology comparison, full sigma decay, source normalization,
semistandard indexing, global invariant spectral spaces, isometry and inversion are
separate obligations of the Plancherel formalization.

The Hermitian and dual adjunction proofs close their exact convergence-domain
obligations, including the reverse-parameter convergence premises. They do not
construct nonempty simultaneous convergence sets or establish continuation to every
unitary parameter. The existing scalar reductions can use these proofs, with
their remaining hypotheses retained; this note records no proof of full-unitary inverse
regularity, of the square-integrable scalar target or of V.2.1. The underlying proof and
topology modules were read, and the twelve affected construction and target modules were
recompiled without diagnostics.

## Structural hypotheses consumed

Each entry is an explicit hypothesis of the declarations named; none is a representation-theoretic
or analytic conclusion.

| Entry | Source | Lean form | Consumers above | Status in the Library |
|---|---|---|---|---|
| S1 Renard's simultaneous standard basis | Renard V.5.2(i)–(iv), rows S20–S23 of [chapter-v-structural-inputs](../renard/chapter-v-structural-inputs.md) | `CompactOpenNormalBasis K0 B` with `StandardParabolicBasisMember i ν J q K` and `IsCompatibleStandardSplitComponent i ν J A q`, or `SimultaneousStandardBasisAt i ν K0` | `StandardCasselmanPairing`, `StandardCasselmanUniformAsymptotics`, `StandardCasselmanConstantTerm`, `RationalXiLowerBound` (`J = ∅` member), `RationalXiUpperBoundStatement`, `RationalXiSquareIntegrableStatement` and its conditional proof `rationalXiSquareIntegrable_of_upperBound` (including the actual-group volume upper bound), `RationalSquareIntegrableRapidDecayStatement`, `RationalConstantTermEstimateStatement`; the four conditional consumers in `RationalLeviMeasure` (basis on `L(F)` at `K0L`) | unproved; existence at a special compact subgroup is the statement `JointSpecialCompactBasisExistenceStatement` |
| S2 standard cocharacters | Borel–Tits §4.2, §5.12; Renard V.4.2 | `IsStandardCocharacter i ν J ζ` | `StandardCasselmanPairing`, `StandardCasselmanConstantTerm` (as the datum `hζ`), `StandardCasselmanUniformAsymptotics` (existence for every face, as a hypothesis) | existence proved: `standardCocharacter : StandardCocharacterStatement` |
| S3 compact open `K` with `G(F) = P₀(F) K` | Waldspurger I.1, p.240 (special `K`) | `IsIwasawaPair (standardParabolicPoints i ν ∅) K`, `K` open and compact | `rationalXi`, `RationalSchwartzSpace`, the `Ξ` bounds, `RationalXiCoefficient`, `RationalXiSquareIntegrable`, `RationalXiLevi`, `RationalTemperedInduction`, `RationalLeviScheme` | `K` is data; existence of a special one is the unproved `IwasawaExistenceStatement` |
| S4 closed matrix representation | Waldspurger I.1, p.242 (`τ : G → GL_n`) | `ρ : MatrixRepresentation G (Fin N)` with `IsClosedSubgroup ρ` | `rationalHeight`, the density, upper-bound and square-integrability statements, `isRationalTempered_iff`, Lemma III.2.3 | existence proved: `affineLinearEmbeddingStatement`; Waldspurger's `τ(K) ⊂ GL_n(𝒪)` is assumed only where stated (`K ≤ rationalHeightSubgroup ρ` in `rationalConvolutionWeights` and Lemma III.2.3) |
| S5 Renard's special compact subgroup, Cartan and Levi clauses | Renard V.5.1 (Cartan decomposition (4), `K₀ ∩ P = (K₀ ∩ M)(K₀ ∩ N)`, properties inside standard Levis), row S19 of [chapter-v-structural-inputs](../renard/chapter-v-structural-inputs.md); Waldspurger I.1 (4), p.241 | covering clause of the Cartan decomposition `Aubert.General.RationalPointFamily.FiniteCartanCovering F i ν K0`; Levi Iwasawa decomposition `hM : IsIwasawaPair (P₀(F) ∩ M_J(F)) (K ∩ M_J(F))` | `RationalXiSquareIntegrableStatement` and its conditional proof `rationalXiSquareIntegrable_of_upperBound`, `RationalSquareIntegrableRapidDecayStatement`, `RationalConstantTermEstimateStatement` (covering, at the compact open `K0` of S1); `rationalLeviXi`, `rationalXi_eq_integral_rationalLeviXi`, `IsRationalLeviTempered`, Lemma III.2.3, `isIwasawaPair_leviSchemeCompact`, `rationalXi_leviScheme`, `hasXiBoundedCoefficients_leviSchemeRepresentation_iff`, `isRationalTempered_leviSchemeRepresentation_iff`, `rationalLeviSchwartzEquiv` and the weight/Schwartz specializations of `RationalLeviMeasure` (`hM`); its four conditional II.1.5 consumers also retain `hM` and require the covering on `L(F)` at `K0L` | unproved for actual `K`; the covering clause is among the clauses of `JointSpecialCompactBasisExistenceStatement`; `isIwasawaPair_standardLevi` derives `hM` from `G(F) = P₀(F)K` and `m_P(P_J(F) ∩ K) ⊆ K`, which follows from Renard's `K ∩ P = (K ∩ M)(K ∩ N)` |
| S6 Cartan covering of the standard Levi subgroups | Renard V.5.1 (5) applied to (4), row S19 of [chapter-v-structural-inputs](../renard/chapter-v-structural-inputs.md); Waldspurger, proof of Proposition II.4.5, p.262 (`M = (K ∩ M) M̄₀^{M+} (K ∩ M)`) | `StandardLeviCartanCovering F i ν J K0`: a finite set `F₀` of torus-centralizer points with `M_J(F) = ⋃ (K0 ∩ M_J(F)) f a (K0 ∩ M_J(F))`, `f ∈ F₀`, `a` in the chamber `C_A^+` of the simple roots `J` | `RationalConstantTermEstimateStatement` | unproved; same form as `FiniteCartanCovering`, which is mathematically its case `J = Δ` |

The scalar target explicitly quantifies over `hRefl : RelativeRootReflectionExistenceStatement`
and `hCST : CentralSplitTorusCharacterStatement`. The Library supplies both without additional
hypotheses: `Langlands.GroupScheme.relativeRootReflectionExistence` in
`GroupScheme/Rational/RootReflectionExistenceProof` and
`Langlands.GroupScheme.centralSplitTorusCharacter` in
`GroupScheme/Rational/CentralSplitTorusCharacterProof`. They are not open structural
obligations. Its two compact-parabolic factorizations, for `P_G(χ)` and `P_G(χ⁻¹)`, remain
explicit data and are distinct from S3's minimal-parabolic factorization. Its analytic and
representation-theoretic inputs remain listed in the published-module rows and the obligations
below. The new Hermitian and positivity targets also retain two compact projection-stability
premises, the dynamic-parabolic form of the product clause in S5:
`m_P(P ∩ K) ⊆ K` and `m_P̄(P̄ ∩ K) ⊆ K`. The note supplies no realization of those premises.
Their `hdag` convergence-domain inclusion and unitarizability premises are analytic and
representation-theoretic obligations, outside the permitted structural boundary.

Facts that were once expected to be hypotheses and are proved: the inclusions `U_J ⊆ U_∅`,
`Ū_J ⊆ Ū_∅` for faces with a standard cocharacter (from the Library's
`relativeRootSignInclusions` and `IsStandardCocharacter.root_pairing_implications_of_subset`);
`P_J(F) ≤ N(U_J(F))` (from the intersection definitions); `δ₀ = 1` on `P₀(F) ∩ K`
(`rationalMinimalModulus_eq_one`); the decomposition `P₀(F) = M₀(F) ⋉ U₀(F)` for connected
reductive `G` and generic `ν` (from `standardCocharacter` and the dynamic decomposition), and
for every `J ⊆ Δ` the continuous decomposition `P_J(F) = M_J(F) ⋉ U_J(F)`, the inclusion
`P₀(F) ⊆ P_J(F)` and `U₀(F) = (M_J(F) ∩ U₀(F)) ⋉ U_J(F)` (`RationalModulusFactorization`);
`δ₀ = 1` on all of `U₀(F)` for connected reductive `G`
(`rationalMinimalModulus_eq_one_of_mem_standardUnipotent`, `RationalXiLevi`); the Levi height
bound `σ(m_P(q)) ≤ c + σ(q)` on `P_J(F)` for closed `ρ` (`exists_rationalHeight_projection_le`,
`RationalTemperedInduction`); the unimodularity of `U_J(F)` for `J` the root set of a set of
simple roots (`isUnimodularModulus_standardUnipotentPoints`); Lemma II.1.2 for the actual `Ξ`
(`rationalXi_uniformTranslationBound`); for a central `s : T → G`, the inclusions
`A_G(F) ⊆ M_J(F)` and `A_G(F) ⊆ P_J(F)` for every `J` and `Ξ(a g) = Ξ(g)` for `a ∈ A_G(F)`
(`RationalCentralProjection`); the hypotheses `ConstantTermData` and `IsConjModulus` of the
generic constant term for a Haar measure on `U_J(F)` and `δ_{U_J}` (`RationalConstantTerm`);
for the Levi group scheme `L` of `J`, connected reductivity, genericity of `ν` and the equality
`P₀^L(F) = P₀(F) ∩ M_J(F)` through `j` (`RationalLeviScheme`); a split component of `L` whose
image is the split centre `A_{M_I}(F)` of `M_I(F)` (`standardLeviSplitComponentStatement`, used in
`RationalLeviDiscreteSeriesOrbitFiniteness`); ambient and intrinsic Levi minimal parabolicity,
with all-test pullback equality and the literal image intersection
(`Langlands.GroupScheme.standardLeviMinimalParabolicCompatibility`, detailed below); the
integrability condition `hint` of
`RationalFourierOrbitSmoothness`, given the coefficient bound `hcoeff` of Corollary III.1.2
(`integrable_rationalCoefficientPairingIntegrand`, `RationalInducedConstantTermFourier`).

## Moduli conventions

The constant terms and Jacquet normalizations of these modules use `δ_U`, the Haar modulus of
conjugation on the radical (the Library's `HaarModulus.closedRestrictCharacter`). For connected
reductive `G` and actual standard parabolics, the Library proves that it is Mathlib's modular
character of the group: `rationalMinimalModulus_eq_modularCharacter` (`δ₀` and `P₀(F)`,
`RationalXiSquareIntegrable`) and `modularCharacter_standardParabolicPoints` (`δ_{U_J}` and
`P_J(F)`, `J` the root set of a set of simple roots, `RationalTemperedInduction`), both from the
`RationalParabolicModulusStatement`, which the Library proves through
`rationalParabolicModulus_of_reductiveUnimodularity`. These modules do not compare it with Waldspurger's
algebraic formula `δ_P(m) = |det Ad(m)|_{Lie U}|_F` (II.2 (1), p.253), and the dynamic
parabolics `P(χ)` of `DynamicCasselmanConstantTerm` are not covered; for nonreductive smooth
groups the radical modulus and the group modulus differ (`𝔾_m ⋉ 𝔾_a`, see
`DynamicCasselmanConstantTerm.md`).
Among radical moduli the Library proves `δ₀ = δ₀^{M_J} δ_{U_J}` on `P₀(F) ∩ M_J(F)` and
`δ₀ = δ_{U_J}` on elements central in `M_J(F)` (`RationalModulusFactorization`);
`standardRadicalModulus`, `standardUnipotentModulus` and the modulus normalizing
`rationalMinimalInducedJacquet` are the same `HaarModulus.closedRestrictCharacter` term.

## Source correction (I.2)

The last assertion of I.2 (p.243), "if `∏_{χ ∈ Y}(ρ(a) − χ(a))^D` annule `V` for all `a`, then
`X ⊂ Y` and one can take `d ⩽ D − 1`", is false as printed. For `A = ℤ^2`, `V` the constants and
`Y` the three characters `(-1)^x`, `(-1)^y`, `(-1)^{x+y}`, the hypothesis holds with `D = 1`
(at each `a` one of the three factors vanishes) but `X = {1} ⊄ Y`; `FiniteFunctionUniqueness.md`
gives the details and the correct pointwise conclusion `χ(a) ∈ {ψ(a) ; ψ ∈ Y}`.

## Obligations at Library commit `c2a69151`

This section records the obligations of the modules above as they stood at Library commit
`c2a69151…`. Where a named statement has since been proved, its proof is given in
parentheses. The next section records later proofs of the `Ξ` upper
bound and split-center height estimates, and later spectral constructions
and proper-Levi comparisons.

- **Upper bound of Lemma II.1.1** (`RationalXiUpperBoundStatement`; unproved at that commit, now proved as
  `rationalXiUpperBound` in `RationalXiUpperBoundProof`). Of the inputs of Waldspurger's proof (p.251), the
  following are published on actual points: `Ξ` as the coefficient `⟨π(g)e, e⟩` of
  `I_{P₀}^G 1` (`RationalXiCoefficient`); Proposition I.4.3 for the standard parabolics, uniformly
  on the dominant points (`StandardCasselmanUniformAsymptotics`, under S1); the modulus identity
  `δ₀ = δ_{U_J}` on central elements (`RationalModulusFactorization`); and a one-sided form of
  I.1 (6) on cones of uniformizer powers, the proved `RationalUniformizerCoordinateHeightStatement`
  (`Langlands.Plancherel`, stated with `rationalMatrixNorm`). The geometric lemma (I.3,
  p.244) is proved in its general represented-parabolic form:
  `Langlands.Aubert.General.RepresentedParabolic.representedGeometricLemma` (module
  `Representation/Geometric/RepresentedGeometricLemmaProof`, Renard VI.5.1) proves
  `RepresentedGeometricLemmaStatement` without further hypotheses. It enumerates the finitely
  many double cosets `P(F) \ G(F) / Q(F)` and constructs representatives and intersection data,
  and shows that `r_Q ∘ i_P` is glued from the pieces `i^L_{Q'} ∘ ι ∘ r^M_{P'}`. Still open:
  the unipotence `RationalMinimalInducedJacquetUnipotentStatement` (statement in the Library; now proved, as
  `rationalMinimalInducedJacquetUnipotent` in `RationalMinimalInducedJacquetProof`). Its proof needs three further steps.
  First, the published geometric lemma must be compared with the standard parabolics
  `P₀(F)`, `P_J(F)` and with the coinvariant model `rationalMinimalInducedJacquet` of these
  modules. Second, each piece must be evaluated on the trivial representation of `M₀(F)`.
  Third, unipotence must be deduced from the resulting finite filtration. The assembly of the
  upper bound (face decomposition of dominant cocharacters, passage from a unipotent action to
  a polynomial bound) also remains open.
- **Lemma II.1.5: the remaining input.** The published
  `rationalXiSquareIntegrable_of_upperBound : RationalXiUpperBoundStatement →
  RationalXiSquareIntegrableStatement` proves the reduction in Waldspurger's proof (p.252).
  `rationalCartanCell` covers `G(F)` by cells indexed by dominant cocharacters and a finite
  centralizer set, from S5. `exists_measure_doubleCoset_uniformizerPowers_le` supplies the upper
  bound of I.1 (5) in `G(F)` itself from S1, and finite translates give the volume bound on the
  cells. `exists_cocharacterCoordinates_norm_le` proves the lower coordinate-height bound of
  I.1 (6) on uniformizer powers for a closed matrix representation. Uniform bounds on the cells
  then feed the proved `CartanSquareBound.squareIntegrableWeight` and its lattice summation.
  The analytic upper bound `RationalXiUpperBoundStatement` was unproved at that commit (it is now
  proved, above);
  S1 and S5 remain structural premises of the resulting II.1.5 statement. The lower volume
  bound of I.1 (5) and the upper height bound of I.1 (6) are not supplied by this reduction.
  The four conditional consumers of `RationalLeviMeasure` apply this result to the Levi scheme
  and transport its conclusion to `M_J(F)`. They retain the global analytic input (II.1.5 or
  the upper bound), closed `ρ`, Levi Iwasawa `hM`, and separate S1/S5 inputs on `L(F)`; no
  unconditional Levi integrability theorem follows.
- **Corollary III.1.2** (`RationalSquareIntegrableRapidDecayStatement`; unproved at that commit, now proved as
  `rationalSquareIntegrableRapidDecay` in `RationalSquareIntegrableDecayProof`). It needs Casselman's criterion in the necessity
  direction for the actual standard parabolics and square integrability modulo `A_G(F)` (the
  represented-parabolic `ArbitraryParabolicCasselmanCriterionStatement`, of which this note records
  no proof), Proposition I.4.3 for the given representation, the
  finite-function expansion of I.2 and Lemma II.1.1. The consequence that square-integrable
  representations are tempered on all of `G(F)` (III.2) is not stated.
- **Proposition II.4.5** (`RationalConstantTermEstimateStatement`, unproved; the Library has only the conditional
  `rationalConstantTermEstimate_of_analyticInputs`, in `RationalConstantTermAnalyticReduction`). The Library's abstract `constantTermEstimate_of_bounds`
  (`ConstantTermBound`) reduces it to Lemmas II.4.4, II.3.1, II.4.2 and II.1.1 for `M_J`, which
  are not established on actual points.
- **Heights on the split centre** (`RationalSplitCenterHeightStatement`; unproved at that commit, now proved as
  `rationalSplitCenterHeight` in `RationalSplitCenterHeightProof`). Its two clauses
  supply the integrability field of `CentralWeights` and the estimate on `G¹` for `p_χ`; the
  module's Markdown sketches a proof through the character valuations `H_G`.
- **Levi subgroups as group schemes: what remains.** `RationalLeviScheme` identifies `Ξ`, `σ`,
  `P₀`, `U₀` and `δ₀` of the Levi group scheme `L = Standard.leviScheme i ν J` with `Ξ^{M_J}`,
  `σ|_{M_J(F)}`, `P₀(F) ∩ M_J(F)`, `M_J(F) ∩ U₀(F)` and `δ₀^{M_J}`, so that the statements for a
  group (II.1.5, III.1.2, VIII.1.2) apply to `L` with the data `(iL, ν, j⁻¹(K), ρ ∘ j)`.
  `RationalLeviDiscreteSeriesOrbitFiniteness` proves the comparisons needed for Theorem VIII.1.2,
  along any topological group isomorphism and in particular along `L(F) ≃ₜ* M_I(F)`
  (`leviRationalPointHomeomorph`, the same map as `leviSchemePointsEquiv`): classes of irreducible
  admissible representations, fixed vectors and twists; coefficient norms modulo central subgroups
  (`centralSubgroupCoefficientNorm_pullback`) and square integrability
  (`isSquareIntegrableModCentralSubgroup_comp_iff`), for central subgroups matched by the
  isomorphism and quotient Haar measures related by pushforward; discrete-series classes and their
  `Im X` orbits (`discreteSeriesOrbitPullback`, with the norm characters matched by
  `leviRationalNormCharacters_apply_points`); the split centre `A_{M_I}(F)`, realized as
  `rationalLeviSplitCenter I a`, the image of `a(T(F))` for a split component `a` of `L`, which
  exists for connected reductive `G` (`exists_isSplitComponent_standardLevi`); and the quotient Haar
  measure on `L(F)/a(T(F))`, the pushforward of a Haar measure on `M_I(F)/A_{M_I}(F)`.
  `RationalLeviTempered` now identifies `IsRationalLeviTempered` with `IsRationalTempered` of
  `leviSchemeRepresentation`, the same-carrier canonical `SmoothRep` pullback. The coefficient
  bounds use corresponding `Ξ` and height, with the same constants and exponents; this proves
  no new representation tempered. It also proves
  `hasXiBoundedCoefficients_leviSchemeRepresentation_iff`: the bound
  `‖ℓ(π(m)v)‖ ≤ c Ξ^{M_J}(m)` for every vector and smooth algebraic-dual functional is
  equivalent to the corresponding bound on `L(F)`. The same positive constant works in both
  directions, with no height or matrix representation. This transports a supplied bound; the
  analytic deduction of such a bound from discrete series, including the passage from rapid
  decay on `G¹` to the whole group, remains open. The transported bound can supply `hcoeff`
  for `RationalInducedCoefficients` and the orbit constructions once the bound on `L(F)` is given.
  `RationalLeviSchwartz` now identifies `C(M_J)` with the
  Schwartz space of `L` by the continuous complex-linear equivalence
  `rationalLeviSchwartzEquiv`, preserving every defining extended-real seminorm `ν_r` for
  real `r` and both existing inductive-limit topologies. Both comparisons retain the explicit
  Levi Iwasawa premise `hM`; neither needs a closed matrix representation.
  `RationalLeviMeasure` now transports a chosen measure on `M_J(F)` itself by
  `leviSchemeMeasure`, preserving Haar measure when supplied, its exact scale and the volume of
  the inherited compact (hence any volume-one normalization). It identifies the square-weight
  integrals for every real exponent, the natural-exponent `SquareIntegrableWeight` conclusion
  and all fields of `L2Weights`. It also preserves the integral pairing, extended `Lᵖ` norms
  and `MemLp`, and identifies the convolution integrals pointwise, with a separate equivalence
  of integrability of their integrands. The pairing, norm and convolution identities specialize
  to `rationalLeviSchwartzEquiv`. The total Bochner integral identities require no integrability
  premise; they prove no convergence estimate or convolution closure. The weight and Schwartz
  comparisons retain `hM` and need no closed matrix representation.
  The conditional consumers in that same module go further only with their additional
  premises: `RationalXiSquareIntegrableStatement.leviSquareIntegrableWeight` and
  `.leviL2Weights` apply the global analytic II.1.5 input to `L`, then give
  `SquareIntegrableWeight` and `L2Weights` for `Ξ^{M_J}`, `σ|_{M_J(F)}` and the original chosen
  Haar measure `μM`. The wrappers `rationalLeviSquareIntegrableWeight_of_upperBound` and
  `rationalLeviL2Weights_of_upperBound` take the global analytic upper-bound statement
  instead. All four retain connected reductivity, maximality of the split torus, genericity
  of `ν`, `J ⊆ Δ`, compact open `K`, a finite nonempty closed matrix representation `ρ`, and
  `hM`. They require a compact open `K0L` in `L(F)` carrying
  `SimultaneousStandardBasisAt (Standard.leviTorusHom i ν J) ν K0L` and
  `FiniteCartanCovering F (Standard.leviTorusHom i ν J) ν K0L`. This compact may differ from
  `leviSchemeCompact K i ν J`; no additional ambient `hPK` is needed. Measure transport
  preserves the chosen Haar scale. These conditional applications supply neither the
  analytic input nor the Levi basis, covering or Iwasawa data, and prove no convolution
  closure.
  The structural premises of the group-level statements for `L` (S1 and S5 at a compact open
  subgroup of `L(F)`) remain separate inputs; the conditional proof of II.1.5 does not supply
  them. The algebraic target `StandardLeviMinimalParabolicCompatibilityStatement` is now
  proved by `Langlands.GroupScheme.standardLeviMinimalParabolicCompatibility` in the published
  [proof pair](../../Langlands/Geometry/Building/SpecialCompactLeviMinimalParabolicProof.md).
  Write `L = Standard.leviScheme i ν J`, `j = Standard.leviHom i ν J`,
  `iL = Standard.leviTorusHom i ν J`, and `Q_L = Standard.leviGenericParabolic i ν J`,
  the dynamic parabolic of `ν ≫ iL`. For connected reductive `G`, maximal split `i`,
  generic `ν` and `J ⊆ simpleRelativeRoots i ν`, its five clauses prove:

  1. Connected reductivity of this actual `L`.
  2. Minimal parabolicity of the chosen ambient `standardParabolic i ν ∅`.
  3. Minimal parabolicity of the intrinsic `Q_L`.
  4. `Q_L = (standardParabolic i ν ∅).comap j` as subgroup functors on every test scheme.
  5. `j(Q_L(F)) = P₀(F) ∩ M_J(F)` as literal subgroups of `G(F)`, using
     `rationalPoints.map j`.

  The same torus factors through `iL ≫ j = i` and the same `ν` remains generic in `L`.
  Minimality requires actual parabolic representability and comparison with every rational
  parabolic subgroup functor by inclusion on every test scheme; it is not inferred from
  rational points. The local-field wrapper has no characteristic, splitness or quasisplitness
  restriction; the implemented algebraic proof uses only the field structure. The all-test
  formulation is a derived refinement of Renard V.5.1(5), whose original assertion concerns
  point groups.
  The module passed the Lake
  build and exact-target checks and first appeared in the Library at
  commit `73b1430a339b037d27e9096762b0400adb4fbd19`. It closes these five
  algebraic clauses only. The inherited apartment, compact/open/maximality, Weyl,
  compact-parabolic product, Iwasawa and Cartan obligations remain separate, as do S1 and S5
  on `L(F)`, the explicit `hM` of the conditional consumers, and all analytic inputs.
- **Normalization constant `c(G|M)`: construction and remaining comparisons.**
  `RationalPlancherelConstant` defines the actual common-compact integrals `leviGamma` on
  `P(F) ∩ L` and `Ū(F) ∩ L`, each with subgroup Haar measure assigning mass one to its
  intersection with the supplied `K`. `rankOneCocharacterSet` is the image of the positive
  relative roots under the cocharacter annihilator of the Levi roots together with that root;
  `cocharacterSubmoduleCentralizer` centralizes all cocharacters in the submodule on every
  test scheme. `rankOneGammaProduct` and `plancherelConstant` implement `∏ γ_α` and
  `γ⁻¹ ∏ γ_α`. The finite-product rewrite is proved for a split torus, and
  `plancherelConstant_zsmul` preserves `c` under positive integer scaling of `ζ`, with `K`
  fixed. The generic common-compact bound proves `γ_α ≥ 1`.
  The published companion `RationalPlancherelConstantFinite` now discharges every rank-one
  finiteness premise when `T` is split and the affine locally finite type `G` is smooth
  with connected underlying scheme. Over an arbitrary field, its cocharacter argument shows
  that every integer-submodule centralizer is `Z_G(ν ≫ i)` for one `ν` generic in that
  submodule. The affine centralizer scheme is a smooth closed subgroup scheme. On rational
  points, exact transport of the subgroup Haar measures normalized by the same compact
  identifies `leviGamma` with `gamma` of that scheme, with no scalar factor.
  The published smooth-group finiteness theorem then gives `rankOneGamma_ne_top` for every
  submodule, `rankOneGammaProduct_ne_top_of_isSplitTorus` and
  `plancherelConstant_ne_top_of_isSplitTorus`. Together with smooth-group nonvanishing this
  gives `plancherelConstant_pos_ne_top` and `plancherelConstantReal_pos_of_isSplitTorus`.
  These results hold over arbitrary nonarchimedean local fields and need neither reductivity
  nor a special compact.
  The formal identifications of the index set and centralizers with `Σ_red(P)`, `A_α` and
  Waldspurger's `M_α`, and the comparison with his normalized integrals, remain open.
  The companion identifies the intersections with dynamic parabolics and opposite radicals
  in a representing smooth centralizer, but proves no reductivity or Levi property for it.
  Independence from the parabolic with fixed Levi for the fixed special `K` also remains
  open (I.1 Remark (3)); positive-multiple invariance does not discharge it. These modules
  do not prove existence or the factorization properties of a special compact, or supply
  a Plancherel identity.
- **The square-integrable unitary scalar target: statement only.**
  `Langlands.Plancherel.ConditionalDynamicOppositeUnitaryScalarStatement` states nonvanishing
  of the actual conditional canonical scalar `j_P` as a rational field element and
  `RationalFunctionNonnegAt` for `j_P⁻¹` at every unitary unramified character. The latter
  means a regular presentation `m/n` with `n(z) ≠ 0` and a nonnegative real value; it allows
  the inverse scalar to vanish at a pole of `j_P`. The module proves only the two elementary
  predicate lemmas named in its row. That module alone proves no nonvanishing or positivity
  assertion about `j_P`, no adjunction of the intertwining integrals, and no part of V.2.1.
  The target retains both compact-parabolic factorizations, the actual whole-operator
  continuations `p, q`, two nonempty open convergence subsets, a nonempty open locus of
  irreducibility of the twisted normalized induction, and square integrability modulo a
  normal central `C` with a Borel quotient Haar measure and finite `M(F)/(M¹ C)`.
  Convergence, continuation, generic irreducibility and square integrability are analytic
  or representation-theoretic inputs; the published dischargers of `hRefl` and `hCST`
  supply none of them. The target uses arbitrary nonarchimedean local fields and connected
  reductive groups, with no characteristic-zero, splitness or quasisplitness restriction.
  It covers none of IV.3(1)–(5), the Weyl and contragredient invariance or the rank-one
  product formula of V.2.1. The later targets and reductions for some of these items, listed
  under "IV.3 and V.2.1 on actual points" below, neither assume this target nor establish it. It
  establishes no comparison of source normalizations or Plancherel identity.
- **Hermitian adjunction and the published common-regular-point reductions.**
  `ConditionalDynamicOppositeHermitianAdjunctionStatement` is proved by
  `Langlands.Plancherel.conditionalDynamicOppositeHermitianAdjunction` in
  `DynamicOppositeHermitianAdjunctionProof`. With the compact-picture
  pairing conjugate-linear in its first argument, it compares the forward integral at `z`
  and reverse integral at `z† = conj(z)⁻¹`. It retains both compact-parabolic factorizations,
  projection stability of `P ∩ K` and `P̄ ∩ K`, an invariant positive form on `A`, and
  membership in the two full convergence domains. The projection premises are needed for
  the Haar measures normalized by the supplied `K` to give the adjunction with constant one. The target
  does not itself provide nonempty convergence subsets or the inclusion `hdag`.
  The proof uses pointwise integral specifications, cancellation of the opposite
  half-moduli and conjugate-inverse characters, and a normalized Iwasawa cutoff exchange
  for the resulting Levi-invariant integrand. It proves the required absolute
  integrability before exchanging the complex integrals. The Levi Haar is right invariant
  by published rational reductive unimodularity. This is a proof of the supplied target,
  with both compact splitting and both parameter-domain premises retained.

  `DynamicOppositeUnitaryNonnegativity` proves that the compact-picture integral pairing
  is a positive definite Hermitian form. Its generic `continuedOperator_adjoint` clears
  the two denominators, applies the regular-function identity theorem on a nonempty open
  convergence subset and divides at regular points. Its actual-point reduction
  `conditionalDynamicOppositeUnitaryNonneg_of_hermitianAdjunction` assumes the adjunction
  target, now supplied by the published theorem, and with unitarizable `A` and `hdag`
  proves nonnegative regular values of `j_P`
  at unitary points in the common selected regular region.

  `DynamicOppositeUniformNonvanishing` proves
  `exists_forwardCompactFamily_eval_one_eq`: for every `v` of `A` there are a compact-picture
  vector `e` independent of the unramified twist and `c ≠ 0` such that the forward integral
  has value `c • v` at `1` throughout its full convergence domain. The vector comes from
  a small compact open subgroup with the proved local product factorization; `c` is its
  positive finite quotient-orbit mass. The generic
  `continuedOperator_map_eq_of_eqOn` carries this constant evaluation to every selected
  forward regular point. With a nonzero `v`, the continued image of `e` is nonzero there.
  The definite Hermitian pairing and the now-proved adjunction then give
  `j_P(z) = (J e, J e)/(e,e) > 0` at unitary common regular points. A unitary character
  avoiding both nonzero denominators exists, so `j_P ≠ 0` in the rational function field.
  Swapping numerator and denominator gives positive regular values of `j_P⁻¹` at these
  same points. This is the proved reduction
  `conditionalDynamicOppositeUnitaryPositive_of_hermitianAdjunction`.

  Both reductions retain the compact projection premises, actual whole-operator
  continuations, nonempty open convergence subsets and generic irreducibility locus,
  unitarizability and `hdag`. Their adjunction argument can now be discharged by the
  published theorem; the convergence-domain inclusion remains a premise. Neither controls
  every unitary point outside the common selected regular
  region, or establishes the full-unitary regularity of `j_P⁻¹` required by V.2.1.
  Their unitarizability, compact projection-stability and `hdag` hypothesis package differs
  from the central-quotient square-integrability package of
  `ConditionalDynamicOppositeUnitaryScalarStatement`;
  no implication to that older target is established here. The published uniform-vector
  argument therefore does not close IV.3 (6), the square-integrable scalar target or the
  density target. The exact
  convergence-domain Hermitian adjunction obligation (IV.1 (11)) is closed.
- **The conditional rational density: construction and remaining analysis.**
  `RationalPlancherelDensity` defines `plancherelDensity = fieldConstant C * j_P⁻¹` in the
  rational unramified function field of the actual centralizer scheme, with
  `C = (rankOneGammaProduct i ζ K hK).toReal²`. The constant and scalar use the same
  compact `K`; this is the derived expression of V.2 (p.292).
  The density definition retains both compact-parabolic factorizations, the canonical
  inducing `SmoothRep`, the actual whole-operator continuations and nonempty subsets of
  their full convergence domains, and a nonempty generic irreducibility locus. The
  continuation-independence result takes openness of the two convergence subsets;
  specification, stabilizer and locus-independence results also take openness of the
  original irreducibility locus. Neither the published dischargers of `hRefl`
  and `hCST` nor this algebraic assembly supplies those analytic and representation-theoretic
  inputs.
  `plancherelDensity_continuation_independent` and
  `plancherelDensity_irreducibility_locus_independent` remove dependence on those choices;
  the replacement irreducibility locus need only be nonempty.
  `plancherelDensity_stabilizer_fixed` proves invariance under unramified self-twists of the
  inducing representation. This is rational stabilizer invariance; it does not construct
  an everywhere-defined function on the unitary orbit or prove Weyl invariance.
  From the imported scalar presentation, `plancherelDensity_spec` supplies regular
  functions `a, b` with `b` nonzero throughout the common regular region, `µ = C b/a`,
  and the actual continued opposite composite acting by `a(z)/b(z)` there. The theorem
  `conditionalContinuedComposite_eq_plancherelDensity_value` gives the scalar
  `C n(z)/m(z)` for a presentation `µ = m/n` only when `z` lies in that region and
  both `m(z)` and `n(z)` are nonzero. It supplies no value at a zero or pole through
  this formula.
  `plancherelDensity_mul_scalar` assumes `j_P ≠ 0`; `plancherelDensity_eq_zero_iff` and
  strict positivity of `C` assume the rank-one product is finite. The latter premise
  can now be discharged by composing with the published
  `rankOneGammaProduct_ne_top_of_isSplitTorus` under its smooth connected split-torus
  hypotheses. This is a composition of published results, not a new theorem in this note
  or a premise removed from the density module. Without finiteness, `toReal ⊤ = 0`;
  with `j_P = 0`, field inversion gives `µ = 0`.
  Source root/Levi and integral-normalization comparisons, fixed-Levi parabolic independence
  and the special compact realization remain open. Neither this density module nor the scalar
  statement proves IV.3(1)–(6), nonvanishing of `j_P`, regularity and nonnegativity everywhere
  on the unitary locus, the product formula, or Weyl/contragredient invariance of V.2.1. The
  value function on `Im X(M)`, its transport to orbits, the contragredient and conjugation
  forms and the specialization to the wave-packet consumers are later conditional modules,
  described under "IV.3 and V.2.1 on actual points" below.
  The published `RationalPlancherelDensityPositivity` now states
  `RationalPlancherelDensity.ConditionalPlancherelDensityUnitaryStatement`: the density is
  nonzero as a rational function when the gamma product is finite, and has regular
  nonnegative values at every unitary unramified character. Its theorem
  `conditionalPlancherelDensityUnitaryStatement_of_unitaryScalar` proves this target
  **from** the still-unproved `ConditionalDynamicOppositeUnitaryScalarStatement`.
  `RationalFunctionNonnegAt.const_mul` supplies the nonnegative-constant multiplication
  step. Nonnegative values may be zero; rational-field nonvanishing is a separate clause.
  This reduction retains the full square-integrable scalar target's hypotheses and
  proves no new scalar assertion, full-unitary regularity, product formula, Weyl or
  contragredient invariance, orbit evaluation or wave-packet specialization.
- **IV.3 and V.2.1 on actual points.** Here `j_P` is the conditional canonical scalar
  `conditionalCanonicalRationalScalar` of `J_{P|P̄} J_{P̄|P}` for `P = P_G(χ)` and
  `P̄ = P_G(χ⁻¹)`, with radical measures normalized by an arbitrary compact open `K`
  satisfying both compact-parabolic factorizations. Each item below is a target or a
  reduction at the scope stated in its row; none removes the analytic data of the scalar.
  - IV.3 (1), independence of `P ∈ P(M)`: for an arbitrary `P' = P_G(ψ) ∈ P(M)` it is the
    unproved target `ConditionalDynamicCommonLeviScalarStatement` (`DynamicCommonLeviScalar`,
    first appeared at commit `4abbe7aa…`), for one compact open `K` with
    `IsCommonLeviSplitting K χ ψ` and the four compact-parabolic factorizations
    `G(F) = Q K`, `Q ∈ {P, P̄, P', P̄'}`, that the scalars `j_P` and `j_{P'}` use. The
    opposite pair `{P, P̄}` (all of `P(M)` for maximal `M`) is the earlier target
    `ConditionalDynamicOppositePairScalarStatement` (`DynamicOppositePairScalar`, first appeared at
    commit `7f5b5f04…`; unproved at that commit, now proved as
    `conditionalDynamicOppositePairScalar`). It is
    proved to follow from the general target (`conditionalDynamicOppositePairScalar_of_commonLevi`,
    which supplies the splitting for every `K` by `isCommonLeviSplitting_of_pair`). The source
    proof (pp.285–286) uses four instances of IV.1 (12), the composition formula, for the
    triples `(P₀, P₁, P₂) = (P̄', P, P')`, `(P', P̄, P̄')`, `(P̄, P̄', P)` and `(P, P', P̄)`.
    IV.1 (12) for actual dynamic parabolics with a common Levi is the target
    `ConditionalDynamicCommonLeviCompositionStatement` (`DynamicCommonLeviComposition`,
    first appeared at commit `aeb3911c…`; unproved at that commit, now proved as
    `conditionalDynamicCommonLeviComposition`, and its structural hypothesis
    `DistanceAdditiveRadicalFactorizationStatement` as `exactDistanceAdditiveRadicalFactorization`). Up to `SplitsAlong.inverse`, its splitting
    premises for the four triples are the four fields of `IsCommonLeviSplitting K χ ψ`. This note
    records no proof of the general target. A proof also needs: the rational continuation
    (Théorème IV.1.1) of the four non-opposite operators `J_{P'|P}`, `J_{P|P̄'}`, `J_{P̄'|P̄}`
    and `J_{P̄|P'}`, which the Library lacks and the target does not take as data; the
    squared-modulus identity for these non-opposite pairs; nonvanishing of the continued
    `J_{P'|P}`; and the passage from the pointwise identities on the full domain regions to the
    rational scalars. the `CommonLeviSplitting.exists_isCommonLeviSplitting` gives
    arbitrarily small compact open `K` with `IsCommonLeviSplitting K χ ψ`. Such a small `K`
    need not have the factorizations. A `K` with both properties, such as Waldspurger's
    special `K` (I.1, p.240), is not constructed. So, beyond the opposite-pair case, the Library
    supplies no `K` satisfying the hypotheses of the general target. How the Library's scalars
    for different `P'` compare under normalizations by different `K` is not established.
  - IV.3 (2), `j(π̌) = j(π)`: the unproved target
    `ConditionalDynamicOppositeContragredientScalarStatement`, reduced in `DynamicOppositeContragredientScalarReduction` to the bilinear dual
    adjunction target, now proved by
    `Langlands.Plancherel.conditionalDynamicOppositeDualAdjunction` in
    `DynamicOppositeDualAdjunctionProof`. The reduction can use this theorem.
    The proof covers both opposite-parabolic orientations, with inverse-parameter
    convergence premises and both compact splittings retained; it does not itself prove
    a rationally continued scalar identity. Its density form, the fourth item of V.2.1,
    is `plancherelDensity_contragredient_of_contragredientScalar`, which assumes the
    scalar target.
  - IV.3 (3), `j(wπ) = j(π)`: the transport-form target
    `ConditionalDynamicOppositeConjugationScalarStatement` for every rational point `g`
    (unproved at that commit, now proved as `conditionalDynamicOppositeConjugationScalar`). The conjugation
    invariance of `∏_α γ(M_α|M)`, `c(G|M)` and the density constant is proved
    (`RationalPlancherelConstantConjugation`), and the density form
    `PlancherelDensityConjugationStatement` is proved from the scalar target.
  - IV.3 (4) and (5), the composition formula with the rank-one scalars `j_α` and
    `j = ∏_α j_α`: not addressed. They need IV.1 (12), now stated as the conditional
    target above, IV.1 (14) for the actual radicals, which is not stated, and the
    identification of the rank-one Levi subgroups `M_α`.
  - IV.3 (6), `j(π) ≠ 0` for square-integrable `π`: the published reductions give
    `j_P ≠ 0` in the rational function field and positive values of `j_P` and `j_P⁻¹` at
    unitary common regular points from the now-proved Hermitian adjunction, with their
    other continuation and domain premises retained. Regularity of `j_P⁻¹` at every
    unitary character, which V.2.1 uses, is the
    unproved target `ConditionalDynamicOppositeUnitaryInverseRegularStatement`; this note
    records no proof of it.
  - V.2.1: regularity of `µ` and `µ ≥ 0` on the unitary orbit are conditional on the
    still-open regularity target and the now-proved adjunction
    (`DynamicOppositeUnitaryInverseRegularity`,
    `RationalUnitaryRegularValue`, `StandardLeviPlancherelWeight`). Weyl invariance is
    available only in transport form: the density of `(gχg⁻¹, gKg⁻¹, gA)` is the transport
    of the density of `(χ, K, A)`. The comparison on one Levi subgroup, where `gPg⁻¹` is
    another element of `P(M)`, is not formalized, even for maximal `M`. It would combine the
    conjugation target with IV.3 (1) for that parabolic. The IV.3 (1) targets above (general
    and opposite-pair) fix one `K`, so it would also need a comparison of the normalizations
    by `gKg⁻¹` and by `K`, and, beyond the opposite pair, a `K` with the splitting and the
    factorizations.
    The contragredient item is the conditional density form above.
    The product formula `µ_G = ∏_α µ_α` is open with IV.3 (5).
- **Proposition I.6.2: comparison of the two published forms.** The standard form
  (`standardConstantTerm`, source cones of `A(F)`, under S1 and S2) and the dynamic form
  (`dynamicConstantTerm`, tails of the powers of `χ(t)`, no structural input) are not compared in
  the Library for `P_J = P(χ)`, and the independence of the dynamic form from the choice of `t` is
  not proved.
- **Theorem VIII.1.2** (`RationalDiscreteSeriesOrbitFinitenessStatement`, unproved; the Library has the conditional
  `rationalDiscreteSeriesOrbitFiniteness_of_cuspidalInputs`, in `RationalCuspidalFinitenessReduction`). Its proof
  (VIII.2–VIII.5) uses `κ` and Theorem VII.2.5 and runs by induction on the semisimple rank
  together with VIII.1.1; a proof needs a statement of VII.2.5 on actual objects
  first. The set in the statement is `rationalDiscreteSeriesFixedOrbits` of the Library's
  `RationalDiscreteSeriesOrbitFiniteness`, which proves its finiteness
  for compact open `H` from the finiteness of the sets `E₂(G)^H_χ`
  (`finite_rationalDiscreteSeriesFixedOrbits_of_finite_central`), or from a finite-dimensional
  space containing their `H`-bi-invariant coefficients
  (`finite_rationalDiscreteSeriesFixedOrbits_of_finiteDimensional`, the role of Proposition
  VIII.4.1 and Theorem VIII.4.2, which are not proved there). So the statement reduces to that
  input for every unitary character `χ` of `A_G(F)` trivial on `A_G(F) ∩ H`. Conversely, the
  published statement gives Theorem VIII.1.2 for every standard Levi subgroup `M_I(F)`
  (`finite_discreteSeriesFixedOrbits_standardLevi`, through the Levi scheme), and with it
  Remarque VIII.1.3 (i) and (ii) for all standard parabolics `P_I(F)`: `Θ^H` restricted to them is
  finite and only finitely many `ψ_f[O, P_I]` are nonzero (`RationalThetaFixedFiniteness`). All of
  these take the statement as the hypothesis `hVIII`.
- **Wave packets and the Fourier transform on actual points: what remains.** The chain
  `RationalInducedCoefficients` → `RationalFourierOrbitContinuity` takes as hypotheses the
  conclusions of Lemma II.1.5 (for `G` and `M_I`), Proposition II.4.5, Corollary III.1.2
  (coefficient bounds and temperedness of the orbit), the structural fact
  `K ∩ P = (K ∩ M)(K ∩ U)` (S5) and the bound `‖H_{M_I}(m)‖ ≤ C(1 + σ(m))` (half of I.1 (6) for
  `M_I`); `RationalInducedConstantTermFourier` replaces its integrability condition by the
  coefficient bound of Corollary III.1.2, which `OrbitCoefficientBound` transfers along the orbit.
  These generic wave packets use a complex weight `w` on the orbit and a measure
  `ρX` on `Im X(M_I)`: the `Ξ` bound, integrability,
  linearity, the pairing formula and the cuspidal convolution results need `ρX` finite and `w`
  bounded and almost everywhere strongly measurable, while the rapid-decay bound
  `|f_ψ| ≤ c Ξ (1 + ‖n_G‖)^{-r}` needs `ρX` finite **and left invariant** (as for the normalized
  Haar measure of I.1 and VI.3) and `w` smooth in the circle coordinates
  (`RationalInducedOrbitWavePacketDecay`). Separately, the one-orbit hermitian product and the
  detection of `ψ_f[O, P]` by wave packets use a real, bounded, continuous, strictly positive
  weight `u` with a finite measure on `Im X(M_I)` positive on nonempty open sets, with no
  invariance assumed (`RationalInducedOrbitWavePacketOrthogonality`); the `…Dense` versions
  need `u ≥ 0` only, with `{u > 0}` dense. The Plancherel weight `µ` is now a conditional
  instance of these consumers. `StandardLeviPlancherelWeight` transports the value function
  of `RationalUnitaryRegularValue` from `Im X(Z_G(ζ ∘ i))` to `O` and gives the decay bound
  for the wave packets of weight `µ`; `PlancherelOrbitWavePacketOrthogonality` gives the
  one-orbit product `∫_O µ(ω) (s_ω, t_ω) dω` and the detection of `ψ_f[O, P]` by those wave
  packets. Both take `hreg`, regularity of `j_P⁻¹` at every unitary character, as a
  hypothesis; the product and detection also take `j_P ≠ 0`, nonnegativity of the unitary
  values of `j_P⁻¹` and, for finiteness of the gamma product, a maximal split torus `i`.
  The three scalar hypotheses are the conclusions of the unproved targets of
  `DynamicOppositeUnitaryInverseRegularity`. The comparison of `µ` with Waldspurger's
  normalizations remains open. Only standard parabolics `P_I(F)` are covered. Not treated on actual points:
  the full Schwartz membership and continuous synthesis conclusions of Proposition VI.3.1
  (stated in `StandardLeviPlancherelWavePacketSchwartz`; see the topology section above), the intertwining part of Proposition VII.2.2 and
  Lemma VII.1.4, Corollary VII.2.3 beyond one orbit, the spaces `C^∞(Θ)` and `C^∞(Θ)_inv`, the map
  `κ` and Theorem VII.2.5, `°C(G)`, Lemma VIII.2.1 beyond the first sentence of its proof, and
  Lemma VIII.2.3 beyond the vanishing of `f₁ ∗ f_ψ` and `f_ψ ∗ f₁`.
- **I.1 (6)** (`1 + σ(m) ≍ 1 + |H_0(m)|`) for the actual `rationalHeight` is not stated in two-sided
  form.

## Weight estimates, spectral families and rank induction, 21 November 2026

The modules below were checked at Library
`a11d1e75f52192f694c9901f4b7fd7098b0f8ff9`. The entries follow the
rank induction in VIII.1, the proper Fourier cutoff in VIII.2.1, and
the full-group residual argument on printed p. 332.

- `rationalXiUpperBound` proves the exact `RationalXiUpperBoundStatement`
  using the proved Jacquet unipotence. Combined with
  `rationalXiSquareIntegrable_of_upperBound`, it supplies the analytic
  input to II.1.5 with the simultaneous standard basis and finite
  Cartan covering still explicit.
  [Xi upper bound](../../Langlands/HarmonicAnalysis/HarishChandraSchwartz/RationalXiUpperBoundProof.md)
- `rationalSplitCenterHeight` proves the exact
  `RationalSplitCenterHeightStatement`. Its two estimates give the
  height comparison on translates by `G¹` and integrability of an
  inverse power of the height on the split center.
  `rationalCuspidalCentralImage_subset_of_specialCompact` uses this
  proof and the II.1.5 weight estimate for the upper inclusion of
  VIII.4.2, with explicit structural inputs and finite projected levels.
  [Split-center heights](../../Langlands/HarmonicAnalysis/HarishChandraSchwartz/RationalSplitCenterHeightProof.md),
  [Upper inclusion](../../Langlands/HarmonicAnalysis/HarishChandraSchwartz/RationalCuspidalRankZero.md)
- `rationalSemistandardThetaSmoothSections` constructs `C^∞(Θ)` as
  the finite-support submodule of the coherent smooth components
  on the full actual semistandard index. `weightedSynthesis` uses
  this submodule as its domain and evaluates the raw weighted sum
  over its finite literal support. The invariant Fourier lift and
  the VII.2.5 identity on synthesis remain separate obligations.
  [Smooth spectral families](../../Langlands/HarmonicAnalysis/HarishChandraSchwartz/RationalSemistandardSpectralFamily.md),
  [Weighted synthesis](../../Langlands/HarmonicAnalysis/HarishChandraSchwartz/RationalSemistandardWeightedSynthesis.md)
- `semistandardProperLeviRank` proves strict rank decrease for each
  proper intrinsic semistandard parabolic, using its literal closed
  reductive Levi model and the inherited maximal split torus. The
  ambient and Levi ranks use their relative root spans.
  [SemistandardProperLeviRankProof](../../Langlands/GroupScheme/Rational/SemistandardProperLeviRankProof.md)
- `RationalExactRankDiscreteSeriesOrbitFinitenessStatement` restricts
  VIII.1.2 to one rank. `rationalStrictlyLowerRankOrbitFiniteness_succ_iff`
  adds the next rank to a strict bound, and
  `rationalStrictlyLowerRankOrbitFiniteness_one_iff` uses the rank-zero
  proposition.
  `allLeviOrbitFiniteness_of_rank_lt` takes orbit finiteness at all
  ranks below a strict bound containing the ambient rank and supplies
  every semistandard Levi premise of VIII.1.3. The rank equivalences
  and all-Levi deduction are in the module linked below.
  [RationalOrbitFinitenessByRank](../../Langlands/HarmonicAnalysis/HarishChandraSchwartz/RationalOrbitFinitenessByRank.md)
- `rationalSemistandardLeviFourierVanishing` takes zero proper Fourier
  cutoff to the vanishing of the actual Fourier product of each
  translated constant term on the proper Levi. Its premises include
  coverage by the lifted nested indices with the specified measure
  and weight comparisons, and the outer radical conjugation modulus.
  A zero-kernel statement for the Levi Fourier product then gives
  vanishing of those constant terms.
  [RationalSemistandardLeviFourierVanishing](../../Langlands/HarmonicAnalysis/HarishChandraSchwartz/RationalSemistandardLeviFourierVanishing.md)
- `fullLeviSplitCenter_map` identifies the actual split-center point
  images under the full standard Levi equivalence. With this
  comparison, `rationalFullLeviFourierActionVanishing` turns zero
  induced Fourier tensors at the full index into zero actions of
  the inverted Schwartz function on the ambient discrete series.
  The hypotheses include the ambient `SquareIntegrableWeight` and
  tempered coefficient bounds for the normalized inductions of the
  inducing discrete series. The proof uses the actual induction
  equivalence, positivity of the inducing formal degree and square
  integrability under either central-quotient Haar scale.
  [Full Levi split center](../../Langlands/HarmonicAnalysis/HarishChandraSchwartz/RationalSemistandardFullLeviSplitCenter.md),
  [Full Levi Fourier action](../../Langlands/HarmonicAnalysis/HarishChandraSchwartz/RationalFullLeviFourierAction.md)
- `rationalCuspidalDiscreteActionSeparation` proves that such action
  vanishing separates the intrinsic cuspidal subspace under the
  displayed ambient and central weight estimates and finite
  projected cuspidal levels. It applies the upper coefficient
  inclusion of VIII.4.2 and split-center Fourier uniqueness. Its
  carrier universe is `max u uV`. The separate
  `discreteSeriesCentralCoefficientSpace_eq_of_separable` compares
  the coefficient sums at independent carrier universes, by
  equivalent realizations preserving the quotient Haar measure.
  [Cuspidal separation](../../Langlands/HarmonicAnalysis/HarishChandraSchwartz/RationalCuspidalDiscreteActionSeparation.md),
  [Small realization](../../Langlands/HarmonicAnalysis/HarishChandraSchwartz/DiscreteSeriesSmallRealization.md)
- `compactQuotientCentralProjectionFinite` proves finite dimension
  of the actual central projection span at an open bi-invariant
  level on a compact central quotient. It evaluates character
  equivariant functions at finitely many coset representatives.
  This supplies the finiteness part of VIII.4.1 when the actual
  split-central quotient is compact.
  [Central projection on a compact quotient](../../Langlands/HarmonicAnalysis/HarishChandraSchwartz/CentralProjectionCompactQuotient.md)

The general reconstruction step still needs the intrinsic
proper-Levi cuspidality criterion, an invariant finite-support
Fourier lift, and the VII.2.5 identity on the actual synthesis
image. The general VIII.4.1 finite-level conclusion remains a
premise of the published cuspidal separation theorem.

## The unitary scalar and common-Levi comparisons

- `Langlands.Plancherel.conditionalDynamicOppositeUnitaryScalar` proves
  `ConditionalDynamicOppositeUnitaryScalarStatement`. It gives nonvanishing
  of \(j_P\) as a rational function and regularity and nonnegativity of
  \(j_P^{-1}\) at every unitary unramified character. This is the opposite
  scalar input from IV.3(6) to the regularity and positivity clauses of
  V.2.1, printed pp. 287 and 292–293. The theorem uses the actual
  open compact with both opposite Iwasawa factorizations, the forward
  and reverse continuations with their convergence regions, a nonempty
  open generic-irreducibility locus, and square integrability with the
  specified central-quotient Haar measure and finite-index condition.
  The root-reflection and central-torus character premises have the
  dischargers listed above. `plancherelDensity_unitaryRegular` carries an
  inverse-scalar regularity proof to the density at the same
  normalization.
  [Opposite scalar proof](../../Langlands/Representation/Plancherel/DynamicOppositeUnitaryScalarProof.md)
  [Unitary density comparison](../../Langlands/Representation/Plancherel/RationalUnitaryRegularValue.md)

- `Langlands.Plancherel.ActualCommonLeviV3.closedV31` proves the
  same-Levi `ClosedV31Statement` for V.3.1, printed p. 295. Its input
  representations are irreducible and square integrable modulo the
  actual split center with the given inversion-invariant quotient Haar
  measure. For two parabolics with the literal common Levi and Iwasawa
  factorizations at one compact, the proof constructs the continued
  comparisons for the inducing representation and its smooth
  contragredient. The resulting regular unitary family preserves the
  actual coefficient map and formal-degree form.
  [Common-Levi comparison](../../Langlands/Representation/Plancherel/ActualCommonLeviV3Proof.md)

- `Langlands.Plancherel.ActualCommonLeviCoherence.closedCommonLeviCoherence`
  proves the identity, composition, inverse and presentation-independence
  laws for these literal common-Levi comparisons. It uses the pairwise
  theorem and dense unitary irreducibility. For translated comparisons,
  `ActualConjugateLeviV3.ClosedV31Statement` specifies the family with the
  source compact and the transported quotient Haar measure.
  `ActualConjugateLeviCoherence.ClosedV32Statement` specifies existence
  and coherence of comparisons with actual conjugation and the same
  source normalization.
  [Common-Levi coherence](../../Langlands/Representation/Plancherel/ActualCommonLeviCoherenceProof.md)
  [Translated comparison](../../Langlands/Representation/Plancherel/ActualConjugateLeviV3Statement.md)
  [Translated coherence](../../Langlands/Representation/Plancherel/ActualConjugateLeviCoherenceStatement.md)

### Association representatives in VII.2.4

`Langlands.HarishChandraSchwartz.RationalSemistandard.Association.associationFormula_of_transport`
proves `AssociationFormulaStatement` under the premises below. It
rewrites the synthesis and Hermitian form of finite-support invariant
families as sums over arbitrary actual association representatives.
Both sums have the coefficient
\[
 c(G\mid M)^{-2}\gamma(G\mid M)^{-1}/|\operatorname{Stab}(\mathcal O,M)|.
\]
`card_association_mul_unquotientedWeight` identifies this coefficient
with the unquotiented coefficient multiplied by the size of the
association class. The two sums are those of Waldspurger Remark VII.2.4,
printed p. 320 (PDF p. 86).
[Association formulas](../../Langlands/HarmonicAnalysis/HarishChandraSchwartz/RationalSemistandardAssociationFormula.md)
[Association count](../../Langlands/HarmonicAnalysis/HarishChandraSchwartz/RationalSemistandardAssociationCount.md)

- `WeylSectionComparisonData` fixes the cocharacter presentations and
  the intrinsic source normalization at each orbit. Its
  `closedSectionComparison` field supplies `ClosedSectionComparisonStatement`
  for every actual compact lift of a Weyl transporter. That statement gives
  the regular comparison on fibres and the smooth section equivalence
  respecting compact levels. The comparison data supplies a lift reaching
  each associated index, and invariance identifies that index's component
  with the transported section.
  [Comparison data](../../Langlands/HarmonicAnalysis/HarishChandraSchwartz/RationalSemistandardInvariantComparison.md)
  [Section comparison](../../Langlands/HarmonicAnalysis/HarishChandraSchwartz/RationalSemistandardWeylSectionStatement.md)
- `OrbitPacketData` at the chosen base of each orbit supplies the two
  opposite-parabolic factorizations, the continued standard operators
  with their open convergence regions, the generic irreducibility region
  and full-unitary regularity of the inverse of their canonical composition
  scalar. It also includes the structural reflection and character inputs
  for that scalar. The orbit measure construction uses
  `(RenardCartan.splitValuationImage (a p)).FiniteIndex` for the split
  component of every intrinsic Levi.
  [Packet data and synthesis](../../Langlands/HarmonicAnalysis/HarishChandraSchwartz/RationalSemistandardWeightedSynthesis.md)
- The chosen maximal split torus and generic cocharacter carry
  `SpecialCompactProperties` at the same compact open `K0`. The explicit
  equalities `(d p).compact = K0` and `(Q t).compact = K0` for every
  semistandard index `p` and orbit index `t` tie the coefficient and
  packet compact pictures to it. The split-central quotients use their
  Borel Haar measures with inversion invariance.
  `IntrinsicQuotientNormalization` normalizes each quotient Haar measure
  using the compact restricted to that Levi.
  [Common normalization](../../Langlands/HarmonicAnalysis/HarishChandraSchwartz/RationalSemistandardComparisonHaar.md)
- `SemistandardSpectralDynamicCoverageStatement` presents every
  semistandard index via a cocharacter.
  `SemistandardSpectralFiberFinitenessStatement` gives finite nonempty
  fibres of parabolics at each literal semistandard Levi.
  `SourceConstantParabolicIndependenceStatement` supplies equality of
  \(\gamma(G\mid M)\) and \(c(G\mid M)\) for presentations of the same
  Levi, from Waldspurger I.1(3), printed pp. 240–241 (PDF pp. 6–7).
  `CoefficientTransportStatement`, `DensityTransportStatement` and
  `PairingTransportStatement` supply the three one-orbit transport laws
  used to make the packet and form summands constant on association classes.
  [Semistandard index](../../Langlands/GroupScheme/Rational/SemistandardSpectralIndex.md)
  [Source constants](../../Langlands/HarmonicAnalysis/HarishChandraSchwartz/RationalSemistandardSourceConstants.md)
  [Orbit transport](../../Langlands/HarmonicAnalysis/HarishChandraSchwartz/RationalSemistandardOrbitIntegralTransport.md)
