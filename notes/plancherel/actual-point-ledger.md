# Waldspurger on actual rational points: published units and structural ledger

Author: Worker 3642 (formerly Worker 19), task `1ef6854b-f0e9-4d96-bbe5-cb8c4b52f927`
(revision 1). Checked against Library commit `75b596ae10e6e11de687b1de9e6e1e7fed212daf`.

This note lists the published modules of this task that realize items of Waldspurger's article
on the actual rational points `G(F) = rationalPoints G` of a group scheme over a nonarchimedean
local field (canonical topology `rationalPointTopology F G.X`), the external structural
hypotheses they consume, and the open obligations on the chains through them. It complements the
item-by-item [source map](waldspurger-source-map.md), which records the generic (abstract)
Library coverage. A proposition definition below is a statement, not a proof. The note proves
nothing.

Source: J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques (d'après
Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333, source ID
`waldspurger-2003-plancherel`. Printed page numbers; the PDF page is the printed page minus 234.

## Published units

| Module | Main declarations | Source items | Hypotheses |
|---|---|---|---|
| `HarmonicAnalysis/HarishChandraSchwartz/FiniteFunctionUniqueness` | `HasFiniteExpansion`, `finiteCoeff`, `eq_zero_of_exponentialPolynomial_eq_zero`, `expansionCoeff_eq_of_exponentialPolynomial_eq`, `exists_uniform_growth_iff_unitary` | I.2 (pp.242–243): uniqueness of the expansion `Σ χ(a) P_χ(H_M(a))`, the minimal `X`, (1) ⇔ (2) | abstract commutative group `A` with additive `H_M : A → E` and a lattice section (as in the Library's `FiniteFunctionExpansion`) |
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
| `HarmonicAnalysis/HarishChandraSchwartz/RationalXiLevi` | `rationalLeviXi` (`Ξ^{M_J}`), `rationalLeviData`, `rationalXi_eq_integral_rationalLeviXi`, `isIwasawaPair_standardLevi`, `rationalMinimalModulus_eq_one_of_mem_standardUnipotent`, `standardUnipotentModulus_eq_one` | II.1 (p.252, definition of `Ξ^M`) and Lemma II.1.6 (pp.252–253) for standard `P_J ⊇ P₀`: `Ξ(g) = ∫_K δ_{U_J}(m_P(kg))^{1/2} Ξ^{M_J}(m_P(kg)) dk` | connected reductive `G`, maximal split torus, generic `ν`; S3 (data); S5 (Levi Iwasawa decomposition `hM`, data) |
| `HarmonicAnalysis/HarishChandraSchwartz/RationalTemperedInduction` | `IsRationalTempered`, `IsRationalLeviTempered`, `isRationalTempered_iff`, `isRationalLeviTempered_iff`, `exists_rationalHeight_projection_le`, `rationalLeviSigmaBound`, `isUnimodularModulus_standardUnipotentPoints`, `modularCharacter_standardParabolicPoints`, `rationalHasTemperedCoefficients_normalizedInduction`, `IsRationalLeviTempered.normalizedInduction` | III.2 (p.265, tempered representations: coefficients bounded by `cΞ(1 + σ)^r`) for `G(F)` and `M_J(F)`, independent of the closed matrix representation; Lemma III.2.3 (p.266) for standard `P_J`, `J` the root set of a set of simple roots: normalized induction of an admissible tempered representation of `M_J(F)` is tempered | connected reductive `G`, maximal split torus, generic `ν`; S3 (data, with `K ≤ rationalHeightSubgroup ρ` for III.2.3); S4; S5 (`hM`, data) |
| `HarmonicAnalysis/HarishChandraSchwartz/RationalSquareIntegrableDecay` | `RationalSquareIntegrableRapidDecayStatement` (statement), `rationalXi_uniformTranslationBound`, `rationalTranslationWeights`, `hasRapidlyDecreasingCoefficientsOn_rationalHeight_iff`, `mul_mem_rationalSchwartz`, `RationalSquareIntegrableRapidDecayStatement.mul_mem_rationalSchwartz` | Corollary III.1.2 (p.263, statement): coefficients of a representation square integrable modulo `A_G(F)` decrease rapidly on `G¹`; Lemma II.1.2 (p.251, proved with `d = 0`); III.7 (p.273, second paragraph): `f φ ∈ C(G)` for `f ∈ A(π)`, `φ ∈ C_c(G/G¹)` (proved from rapid decay) | the statement: S1 and S5 (Cartan covering) at a compact open `K0`; S3, S4 as data. Lemma II.1.2 and III.7: S3; no structural input |
| `HarmonicAnalysis/HarishChandraSchwartz/RationalConstantTerm` | `RationalConstantTermEstimateStatement` (statement), `StandardLeviCartanCovering`, `rationalIsConjModulus`, `rationalConstantTermData`, `standardLeviMinimalModulusOf_eq_one`, `rationalLeviXi_pos`, `rationalConstantTerm`, `coe_rationalConstantTerm` | Proposition II.4.5 (p.262, statement) for the opposite `P̄_J` of a standard parabolic, in the form `ConstantTermEstimate`; the constant term `f ↦ f^{(P_J)}`, `C(G) → C(M_J)` of III.6 (p.272), defined from the estimate | the statement: S1, S5 (Cartan covering of `G`) and S6 (Cartan covering of `M_J`) at a compact open `K0`; S3, S4, `hM` as data. `ConstantTermData`, `IsConjModulus`: no structural input |
| `HarmonicAnalysis/HarishChandraSchwartz/RationalCentralProjection` | `RationalSplitCenterHeightStatement` (statement), `range_le_standardLeviPoints`, `range_le_standardParabolicPoints`, `rationalMinimalModulus_eq_one_of_mem_center`, `rationalXi_mul_of_mem_range`, `rationalCentralWeights`, `rationalCentralProjection`, `RationalSplitCenterHeightStatement.enorm_rationalCentralProjection_le` | VIII.4 (p.327): the projections `p_χ` on `C(G)`; the estimate on `G¹` of the proof of Proposition VIII.4.1 (p.328); the statement: two height properties of `A_G(F)` and `G¹` derived from I.1, used implicitly in VIII.4 | the statement: none (connected reductive `G`, split component, closed `ρ`). `A_G(F) ⊆ P_J(F)`, `Ξ(ag) = Ξ(g)`: central `s`, S3. `p_χ`: `CentralWeights` (supplied by the statement) |
| `HarmonicAnalysis/HarishChandraSchwartz/RationalLeviScheme` | `leviSchemeCompact` (`j⁻¹(K)`), `isGenericCocharacter_leviTorusHom`, `standardParabolic_leviTorusHom_empty`, `standardUnipotent_leviTorusHom_empty`, `leviSchemePointsEquiv`, `mem_standardParabolicPoints_leviTorusHom_iff`, `standardLeviMinimalModulus_leviHom`, `isIwasawaPair_leviSchemeCompact`, `rationalXi_leviScheme`, `rationalHeight_restrict_leviHom`, `xi_map` | I.1 (p.240, `M ∩ K` has for `M` the properties of `K` for `G`) and II.1 (p.252, `Ξ^M` is `Ξ` for `M`) for the Levi group scheme `L = Standard.leviScheme i ν J` with `j : L → G`: `P₀^L(F) = P₀(F) ∩ M_J(F)` and `U₀^L(F) = M_J(F) ∩ U₀(F)` through `j`, `δ₀^L = δ₀^{M_J}`, `Ξ` of `L` for `j⁻¹(K)` is `Ξ^{M_J} ∘ j`, `σ_{ρ ∘ j} = σ_ρ ∘ j` | connected reductive `G`, maximal split torus, generic `ν`; S3 (data); S5 (`hM`, data) for the Iwasawa pair and `Ξ`; no structural input for the parabolic, modulus and height comparisons |

All modules are in namespaces `Langlands.HarishChandraSchwartz`, `Langlands.Jacquet` or
`Langlands.BruhatTits.SpecialCompact`; their paired Markdown files give the exact statements.

## Structural hypotheses consumed

Each entry is an explicit hypothesis of the declarations named; none is a representation-theoretic
or analytic conclusion.

| Entry | Source | Lean form | Consumers above | Status in the Library |
|---|---|---|---|---|
| S1 Renard's simultaneous standard basis | Renard V.5.2(i)–(iv), rows S20–S23 of [chapter-v-structural-inputs](../renard/chapter-v-structural-inputs.md) | `CompactOpenNormalBasis K0 B` with `StandardParabolicBasisMember i ν J q K` and `IsCompatibleStandardSplitComponent i ν J A q`, or `SimultaneousStandardBasisAt i ν K0` | `StandardCasselmanPairing`, `StandardCasselmanUniformAsymptotics`, `StandardCasselmanConstantTerm`, `RationalXiLowerBound` (`J = ∅` member), `RationalXiUpperBoundStatement`, `RationalXiSquareIntegrableStatement`, `RationalSquareIntegrableRapidDecayStatement`, `RationalConstantTermEstimateStatement` | unproved; existence at a special compact subgroup is the statement `JointSpecialCompactBasisExistenceStatement` |
| S2 standard cocharacters | Borel–Tits §4.2, §5.12; Renard V.4.2 | `IsStandardCocharacter i ν J ζ` | `StandardCasselmanPairing`, `StandardCasselmanConstantTerm` (as the datum `hζ`), `StandardCasselmanUniformAsymptotics` (existence for every face, as a hypothesis) | existence proved: `standardCocharacter : StandardCocharacterStatement` |
| S3 compact open `K` with `G(F) = P₀(F) K` | Waldspurger I.1, p.240 (special `K`) | `IsIwasawaPair (standardParabolicPoints i ν ∅) K`, `K` open and compact | `rationalXi`, `RationalSchwartzSpace`, the `Ξ` bounds, `RationalXiCoefficient`, `RationalXiSquareIntegrable`, `RationalXiLevi`, `RationalTemperedInduction`, `RationalLeviScheme` | `K` is data; existence of a special one is the unproved `IwasawaExistenceStatement` |
| S4 closed matrix representation | Waldspurger I.1, p.242 (`τ : G → GL_n`) | `ρ : MatrixRepresentation G (Fin N)` with `IsClosedSubgroup ρ` | `rationalHeight`, the density, upper-bound and square-integrability statements, `isRationalTempered_iff`, Lemma III.2.3 | existence proved: `affineLinearEmbeddingStatement`; Waldspurger's `τ(K) ⊂ GL_n(𝒪)` is assumed only where stated (`K ≤ rationalHeightSubgroup ρ` in `rationalConvolutionWeights` and Lemma III.2.3) |
| S5 Renard's special compact subgroup, Cartan and Levi clauses | Renard V.5.1 (Cartan decomposition (4), `K₀ ∩ P = (K₀ ∩ M)(K₀ ∩ N)`, properties inside standard Levis), row S19 of [chapter-v-structural-inputs](../renard/chapter-v-structural-inputs.md); Waldspurger I.1 (4), p.241 | covering clause of the Cartan decomposition `Aubert.General.RationalPointFamily.FiniteCartanCovering F i ν K0`; Levi Iwasawa decomposition `hM : IsIwasawaPair (P₀(F) ∩ M_J(F)) (K ∩ M_J(F))` | `RationalXiSquareIntegrableStatement`, `RationalSquareIntegrableRapidDecayStatement`, `RationalConstantTermEstimateStatement` (covering, at the compact open `K0` of S1); `rationalLeviXi`, `rationalXi_eq_integral_rationalLeviXi`, `IsRationalLeviTempered`, Lemma III.2.3, `isIwasawaPair_leviSchemeCompact`, `rationalXi_leviScheme` (`hM`) | unproved for actual `K`; the covering clause is among the clauses of `JointSpecialCompactBasisExistenceStatement`; `isIwasawaPair_standardLevi` derives `hM` from `G(F) = P₀(F)K` and `m_P(P_J(F) ∩ K) ⊆ K`, which follows from Renard's `K ∩ P = (K ∩ M)(K ∩ N)` |
| S6 Cartan covering of the standard Levi subgroups | Renard V.5.1 (5) applied to (4), row S19 of [chapter-v-structural-inputs](../renard/chapter-v-structural-inputs.md); Waldspurger, proof of Proposition II.4.5, p.262 (`M = (K ∩ M) M̄₀^{M+} (K ∩ M)`) | `StandardLeviCartanCovering F i ν J K0`: a finite set `F₀` of torus-centralizer points with `M_J(F) = ⋃ (K0 ∩ M_J(F)) f a (K0 ∩ M_J(F))`, `f ∈ F₀`, `a` in the chamber `C_A^+` of the simple roots `J` | `RationalConstantTermEstimateStatement` | unproved; same form as `FiniteCartanCovering`, which is mathematically its case `J = Δ` |

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
`P₀^L(F) = P₀(F) ∩ M_J(F)` through `j` (`RationalLeviScheme`).

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

## Open obligations on these chains

- **Upper bound of Lemma II.1.1** (`RationalXiUpperBoundStatement`, unproved; proof task Task
  5326 `d27429ee-ab4e-47b4-8486-8cdd92ff4d34`). Of the inputs of Waldspurger's proof (p.251), the
  following are published on actual points: `Ξ` as the coefficient `⟨π(g)e, e⟩` of
  `I_{P₀}^G 1` (`RationalXiCoefficient`); Proposition I.4.3 for the standard parabolics, uniformly
  on the dominant points (`StandardCasselmanUniformAsymptotics`, under S1); the modulus identity
  `δ₀ = δ_{U_J}` on central elements (`RationalModulusFactorization`); and a one-sided form of
  I.1 (6) on cones of uniformizer powers, the proved `RationalUniformizerCoordinateHeightStatement`
  (`Langlands.Plancherel`, stated with `rationalMatrixNorm`). Still open: the unipotence
  `RationalMinimalInducedJacquetUnipotentStatement` (statement published; proof task Task 5325
  `53ad424f-5caa-4396-bbcc-361818d50f3a`, which needs the geometric lemma for `P₀ \ G / P_J`; the
  general represented-parabolic version is the unproved `RepresentedGeometricLemmaStatement`,
  Task 4822), and the assembly (face decomposition of dominant cocharacters, passage from a
  unipotent action to a polynomial bound).
- **Lemma II.1.5** (`RationalXiSquareIntegrableStatement`, unproved). Waldspurger's proof
  (p.252) combines the Cartan decomposition (S5), the upper bound of Lemma II.1.1 (Task 5326
  above), the volume bound I.1 (5) (proved modulo the center as `rationalLatticeQuotientVolume`)
  and I.1 (6); the Library's generic `CartanSquareBound.squareIntegrableWeight` and the proved
  one-sided `RationalUniformizerCoordinateHeightStatement` cover the summation. No proof task is
  published; one waits for the proof of `RationalXiUpperBoundStatement`.
- **Corollary III.1.2** (`RationalSquareIntegrableRapidDecayStatement`, unproved; proof task Task
  5461 `7f9ba483-3cd4-4733-a87b-b5651bdbd06a`). It needs Casselman's criterion in the necessity
  direction for the actual standard parabolics and square integrability modulo `A_G(F)` (the
  represented-parabolic `ArbitraryParabolicCasselmanCriterionStatement` has proof task
  `2e8d370f-f1ed-4ad4-a529-5083212ebae0`), Proposition I.4.3 for the given representation, the
  finite-function expansion of I.2 and Lemma II.1.1. The consequence that square-integrable
  representations are tempered on all of `G(F)` (III.2) is not stated.
- **Proposition II.4.5** (`RationalConstantTermEstimateStatement`, unproved; proof task Task 5460
  `cdf027c8-1a9c-410f-9630-3fb913f227c8`). The Library's abstract `constantTermEstimate_of_bounds`
  (`ConstantTermBound`) reduces it to Lemmas II.4.4, II.3.1, II.4.2 and II.1.1 for `M_J`, which
  are not established on actual points.
- **Heights on the split centre** (`RationalSplitCenterHeightStatement`, unproved). Its two clauses
  supply the integrability field of `CentralWeights` and the estimate on `G¹` for `p_χ`; the
  module's Markdown sketches a proof through the character valuations `H_G`.
- **Levi subgroups as group schemes: what remains.** `RationalLeviScheme` identifies `Ξ`, `σ`,
  `P₀`, `U₀` and `δ₀` of the Levi group scheme `L = Standard.leviScheme i ν J` with `Ξ^{M_J}`,
  `σ|_{M_J(F)}`, `P₀(F) ∩ M_J(F)`, `M_J(F) ∩ U₀(F)` and `δ₀^{M_J}`, so that the statements for a
  group (II.1.5, III.1.2, VIII.1.2) apply to `L` with the data `(iL, ν, j⁻¹(K), ρ ∘ j)`. Not
  compared: representations (temperedness, square integrability and coefficients along
  `leviSchemePointsEquiv`), the split centre of `L` and `M_J(F)¹`, Haar measures on `M_J(F)`, and
  `C(M_J)` with the Schwartz space of `L`. The structural premises of those statements for `L`
  (S1 and S5 at a compact open subgroup of `L(F)`) are separate inputs; the minimality assertions
  of `StandardLeviMinimalParabolicCompatibilityStatement` remain unproved.
- **Proposition I.6.2: comparison of the two published forms.** The standard form
  (`standardConstantTerm`, source cones of `A(F)`, under S1 and S2) and the dynamic form
  (`dynamicConstantTerm`, tails of the powers of `χ(t)`, no structural input) are not compared in
  the Library for `P_J = P(χ)`, and the independence of the dynamic form from the choice of `t` is
  not proved.
- **Theorem VIII.1.2** (`RationalDiscreteSeriesOrbitFinitenessStatement`, unproved). Its proof
  (VIII.2–VIII.5) uses `κ` and Theorem VII.2.5 and runs by induction on the semisimple rank
  together with VIII.1.1; a proof task is deferred until a statement of VII.2.5 on actual objects
  exists. The set in the statement is `rationalDiscreteSeriesFixedOrbits` of the Library's
  `RationalDiscreteSeriesOrbitFiniteness` (written in another task), which proves its finiteness
  for compact open `H` from the finiteness of the sets `E₂(G)^H_χ`
  (`finite_rationalDiscreteSeriesFixedOrbits_of_finite_central`), or from a finite-dimensional
  space containing their `H`-bi-invariant coefficients
  (`finite_rationalDiscreteSeriesFixedOrbits_of_finiteDimensional`, the role of Proposition
  VIII.4.1 and Theorem VIII.4.2, which are not proved there). So the statement reduces to that
  input for every unitary character `χ` of `A_G(F)` trivial on `A_G(F) ∩ H`.
- **I.1 (6)** (`1 + σ(m) ≍ 1 + |H_0(m)|`) for the actual `rationalHeight` is not stated in two-sided
  form.
