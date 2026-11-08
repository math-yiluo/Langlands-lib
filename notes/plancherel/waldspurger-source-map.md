# Waldspurger 2003 Plancherel formula: source map

Author: Worker 249, task `1ef6854b-f0e9-4d96-bbe5-cb8c4b52f927` (revision 1).
Lean coverage below was checked against Library commit
`ce52163e150fe772fdb773627f006a99df1688af`; the rows III.1 (2), (3) and
III.7, the module entries `AdmissibleFitting` and `TraceCoefficientFamily` and the
entry for `TraceFamilyScalar`, `OrbitPolynomialOperator`, `TemperedTwistIntegrability`
and `QuotientMeasureCompatibility` were updated against Library commit
`2816ea5d81e2fb9b0512bd1d8dec2ad7797026fd`; the rows I.6 and III.2 and the module entries
`AdmissibleCoefficientSpace`, `AdmissibleCoefficientSpaceLeft` and
`InducedTemperedCoefficients` were updated against Library commit
`568f1cff4df2c51ba08b932716bf99235d0032c7`; the rows I.2, I.3, Thm I.4.1, I.6,
Lemmes III.3.1–III.3.3, Lemme III.5.1, Lemmes VI.2.1–VI.2.3, VIII.2 (Lemme VIII.2.1),
Rem. VIII.2.2 and Lemme VIII.2.3 and Thm VIII.4.2, two entries of "Notation and source
corrections" and the module entries `FiniteFunctionExpansion`, `WeakConstantTermExistence`,
`ExponentDecomposition`, `PositivePartDecay`, `CuspidalWavePacketOrthogonality`,
`RationalOrbitCentralProjection`, `RightFiniteUniqueness` and `StablePairingAsymptotics` were
updated against Library commit `3f1412571c4c931abb11fdcd373eaf66fd0c5385`.

This note maps every numbered item of Waldspurger's article to its page, its
content, the items of the article it uses, and the external sources it cites.
It classifies each item for the task's structural ledger and lists the
Library declarations that currently formalize part of it. It proves nothing.
A proposition definition listed here is a statement, not a proof. Where no
declaration is listed, the item is open.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333,
DOI 10.1017/S1474748003000082. Source ID `waldspurger-2003-plancherel`,
SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`,
file `Waldspurger--La formule de Plancherel pour les groupes p-adiques
d'apres Harish-Chandra--2003.pdf` in the central library.

Page numbers are printed numbers; the PDF page is the printed page minus 234.
All eight chapters were read in full.

## Classes

The task's completion condition 1 separates four kinds of input. Each item
below gets one or more of these labels.

- **Data**: a definition or a fixed choice (groups, measures, spaces, maps).
- **Struct**: a fact about the reductive group, its subgroups, decompositions
  or measures. Such a fact may be kept as an explicit hypothesis only if it is
  external at the Renard Chapter V boundary. That decision belongs to the
  task's structural ledger, not to this note.
- **Book**: a statement the article proves. It must be proved in Lean or
  imported from a published proof. The elementary facts of I.2, which the
  article states without proof or citation, are also labeled Book.
- **Ext**: a representation-theoretic or analytic theorem that the article
  cites from another source without proof. It is not structural input. It
  must be proved, or imported from a published proof.

## External sources cited

The bibliography is on p.333 (PDF p.99). The article cites outside results at
these places:

| Citation | Where | Used for |
|---|---|---|
| [BZ, 2.12] Bernstein–Zelevinsky | I.3, p.244 | the geometric-lemma filtration of `(I_P^G V)_{P'}` |
| [C, Prop. 4.2.3, Thm 4.2.4] Casselman | Thm I.4.1, p.245 | the canonical pairing on Jacquet modules |
| [C, Thm 4.3.3] | Prop. I.4.3, p.245 | coefficients equal Jacquet coefficients on cones `P_{m,t}` |
| [BD, 2.5, 3.1] Bernstein–Deligne | I.5, p.245 | the Jacquet module and the induced representation of an admissible `B`-family are admissible `B`-families |
| [BD, Prop. 3.5.2] | I.5, p.247 | `j_P` maps `V^H` onto `V_P^{H∩M}` (B-family version of I.4.1) |
| [H, Thm 4.6; Ex. 8 p.115] Humphreys | II.2 (6), p.254 | the image of the orbit map `θ` of `Ū` is closed (Ex. 8, any characteristic); in characteristic zero `θ` is an isomorphism onto its image (Thm 4.6), so `Q = Q' ∘ θ` for every polynomial `Q` on `Ū`; in characteristic `p > 0` (stated in II.2 without a citation) the function field of `Ū` is a purely inseparable extension of that of the image, and `Q^{p^d} = Q' ∘ θ` for a fixed `d ≥ 0` |
| [C, Thm 4.4.6] | Prop. III.1.1, p.263 | square integrability via exponents |
| [C, Prop. 5.2.4] | III.1 (2), (3), p.265 | Schur orthogonality and the formal degree `d(π)` |
| [B, §4.6, Prop. 9] Bourbaki EVT | III.6, p.271 | the inductive-limit topology on `C(G)` is locally convex and complete |
| [S, Thm IV.1] Sauvageot | IV.3, p.285 | generic irreducibility of `I_P^G π'`; for square-integrable `π` the article derives it from IV.2.2 instead |

The introduction (pp.235–238) also cites Harish-Chandra [HC1], [HC2] and
Silberger [Si] as background; the proofs do not use them.

## Notation and source corrections

- `γ(G|M)` and `c(G|M) = γ(G|M)^{-1} ∏_{α ∈ Σ_red(P)} γ(M_α|M)` are defined in
  I.1, p.241. On p.305 (VI.3, definition of `κ̃`) the constant is printed as
  `C(G|M)^{-2}`, with a capital C. Everywhere else, including VII.2.4 and
  VIII.1 (2), (3) on p.320, it is `c(G|M)^{-2}`. The capital is a misprint for
  the same constant `c(G|M)`.
- p.325 (proof of Prop. VIII.3.1) cites "Lemme VII.2.1" for `f_1^{(P̄)} = 0`.
  The cuspidality lemma is VIII.2.1; VII.2.1 is a proposition about `(f_ψ)^`.
- p.330 (proof of Prop. VIII.4.1) cites "Corollaire III.3.2". There is no such
  corollary (III.3.2 is a lemma about weak constant terms). The convergence
  used is Cor. VIII.3.2.
- p.270 (proof of Lemma III.5.1, existence): "Ces conditions assurent que
  `lim_{a →_P ∞} ϕ(a) = 0`" fails for (1) as stated. The roots `α ∈ Σ(P)` vanish on `a_G`, while
  `Q_χ` may depend on the `a_G`-component of `H_M(a)`: for `G = GL_2`, `St` the Steinberg
  representation and `f(g) = val_F(det g)⟨St(g)v, v̌⟩ ∈ A^w(G)`, no `f^w_B` exists. The argument
  is correct when every `Q_χ` is a polynomial in linear forms in the span of `Σ(P)`, for instance
  when `A_G` acts on the representation generated by `f` through a character
  (`WeakConstantTermExistence`).
- p.301 (proof of Lemma VI.2.3): the inequality `r|H_0(m)| ⩽ n` fails when `|H_0(m)|` is close to
  `tδ^{-1}` (then `n` can be `0`); `n > (δ|H_0(m)| − t)/c − 1` suffices and only changes the
  constant (`PositivePartDecay`).

## Main targets

| Target | Page | Statement |
|---|---|---|
| Thm VII.2.5 | p.320 | `κ` is an isometry of `C^∞(Θ)_inv` onto its image in `C(G)`, and `ψ_{κ(ψ)}[O,P] = ψ[O,P]` |
| Rem. VII.2.4 | p.320 | the formulas for `κ` and the Hermitian product over association classes `Θ/ass`, with `\|Stab(O,M)\|^{-1}` |
| Thm VIII.1.1 | p.320 | `κ` is surjective; equivalently (1) finitely many `ψ_f[O,P] ≠ 0` and (2) `f = Σ c^{-2} γ^{-1} \|W^M\|\|W^G\|^{-1}\|P(M)\|^{-1} f_{ψ_f[O,P]}` |
| VIII.1 (3) | p.320 | pointwise inversion `f(g) = Σ_{Θ/ass} c(G\|M)^{-2} γ(G\|M)^{-1} \|Stab(O,M)\|^{-1} ∫_O μ(ω) d(ω) θ^G_ω(λ(g) f̌) dω` |
| Thm VIII.1.2 | p.321 | for every compact open `H`, `Θ^H_G` is finite |

The coefficient of `f_{ψ[O,P]}` in `κ̃` (VI.3, p.305) and in VIII.1 (2) is
`c(G|M)^{-2} γ(G|M)^{-1} |W^M| |W^G|^{-1} |P(M)|^{-1}`.

## Chapter I. Notation and Jacquet modules (pp.238–250)

| Item | Page | Content | Uses | Class | Lean coverage |
|---|---|---|---|---|---|
| I.1 | 238–242 | `F`, `G`, `A_0`, `M_0`, `P_0`, `Rat(G)`, `a_G`, `H_M`, roots `Σ`, `W`, special `K`; left Haar measures with `mes(H ∩ K) = 1`, the functional `∫_{H\G}` on `δ_H`-covariant functions and the integration formulas (2) (p.240); `G = P K`, Iwahori factorization, `γ(P)` depends only on `M` (proof on p.241), `c(G\|M)`, Cartan decomposition (4), `mes(KmK) ≍ δ_0(m)^{-1}` (5), the norm `‖·‖` via `τ : G → GL_n` with `τ(K) ⊆ GL_n(O)`, `σ = log‖·‖`, (6) `1 + σ(m) ≍ 1 + \|H_0(m)\|` | — | Data, Struct; `γ(P)` independence and (5) are Book | (2), first formula: `lintegral_eq_lintegral_unipotent_levi` (generic); (2), second formula, with `γ(P)` and `0 < γ(P) < ∞`: `lintegral_eq_openCellConstant_inv_mul`, `openCellConstant`, `openCellConstant_eq_lintegral` (generic, in the coordinates `(p, v) ↦ p v^{-1}`) and `lintegral_eq_openCell_levi_unipotent` (generic, in the coordinates `m u v^{-1}`); the topological hypotheses `hι` of `lintegral_eq_openCellConstant_inv_mul` and `hhomeo` of `leviUnipotentMeasure_isHaarMeasure` on rational points, for the dynamic subgroups `P_G(χ)`, `U_G(χ^{-1})`, `Z_G(χ)`, `U_G(χ)` of an affine group scheme over a topological field with open units: the open cell `isOpenEmbedding_openCellMap_rationalPoint` (smooth `G`) and the Levi coordinates `isHomeomorph_leviUnipotentCoord_rationalPoint` (`G` locally of finite type); Haar-nullness of the complement of the dynamic open cell `P(χ)(F) U(χ⁻¹)(F)`, for every cocharacter `χ` and every left Haar measure on the rational points of a connected reductive group: `rationalDynamicOpenCellConull` (proves `RationalDynamicOpenCellConullStatement`; through the Zariski boundary of the cell, `rationalDynamicOpenCellBoundary`, proving `RationalDynamicOpenCellBoundaryStatement`); the generic formula for an ambient Haar measure that is only right invariant under `V` and a conull cell, `lintegral_eq_openCellConstant_inv_mul_of_rightInvariantOn` (`RestrictedOpenCellIntegration`, with `RestrictedOpenCellGamma`, `LocalOpenCellGamma`); on actual rational points, for the dynamic subgroups of a cocharacter and the Haar measures with mass one on their intersections with one supplied compact open `K` (`RationalDynamicSource.gamma`, `parabolicHaar`, `leviHaar`, `radicalHaar` in `RationalDynamicSourceHaar`, `ambientHaar` in `RationalSourceGammaAmbientHaar`): (2), second formula, for connected reductive `G`, `ambientHaar_eq_gamma_inv_smul`, `lintegral_eq_gamma_inv_mul` (`RationalSourceGammaGlobal`), in the source coordinates `u m v` with the inverse radical conjugation modulus `inverseLeviModulus`, given that the dynamic limit maps `P ∩ K` into `K` (`hstable`), `lintegral_eq_source_order_of_limit_stable` (`RationalSourceOpenCellCoordinates`) and its Bochner form `integral_eq_source_order_of_limit_stable` (`RationalSourceOpenCellBochner`); `0 < γ < ∞` for smooth `G`, `gamma_ne_zero_ne_top_of_smooth`, `gammaReal_pos_of_smooth`, and `γ` as the integral over the opposite radical of the modulus at the Iwasawa Levi component, given `G = P K`, `hstable` and right invariance of the Levi Haar measure, `gammaReal_eq_integral_of_levi_rightInvariant` (`RationalSourceGammaAmbientHaar`, with `RationalSourceGammaIntegral`); (2), first formula, given `G = P K` and `hstable`, in the source order `u m k` with `inverseLeviModulus`: `lintegral_eq_iwasawa_source_order_of_limit_stable`, with the two-factor form `lintegral_eq_parabolic_compact` (`RationalSourceIwasawaIntegration`), and its Bochner form for every ambient integrable function, `integral_eq_iwasawa_source_order_of_limit_stable` (`RationalSourceIwasawaBochner`); invariance of `γ` under conjugation by elements of `K`, `gamma_conjugate_of_mem_compact` (`RationalSourceGammaConjugation`), and the corresponding measure-preserving conjugations of the subgroup Haar measures, `measurePreserving_parabolicSourceConjugation`, `measurePreserving_radicalSourceConjugation` (`RationalSourceHaarConjugation`); independence of `γ` of the cocharacter describing the same dynamic subgroups, `gamma_eq_of_dynamic_subgroups_eq`, `gamma_precomp_power` (`RationalSourceGammaChoice`); the generic semidirect versions and their transport, `semidirectSourceGamma`, `lintegral_eq_semidirectSourceGamma_inv_mul`, `compactNormalizedSourceGamma` (`SemidirectSourceGamma`, `SemidirectSourceGammaIntegral`, `SemidirectSourceHaarNormalization`), `compactNormalizedSourceGamma_eq_of_transport` (`SourceGammaTransport`); these take `K` as data, and the existence of a special `K` with `G = P K` and `hstable` is not proved; (3), steps of its proof on actual rational points (Worker 200; `M`, `U`, `Ū` the Levi, radical and opposite radical of a cocharacter, `γ` normalized on `K`): for a compact open `H ≤ K` such that `m u v ∈ H` if and only if `m, u, v ∈ H`, the index expression `γ(P) = [K : H] [M ∩ K : M ∩ H]^{-1} [U ∩ K : U ∩ H]^{-1} [Ū ∩ K : Ū ∩ H]^{-1}` of the proof, given connected reductive `G` and `hstable`, `gamma_eq_gammaIndex`, with `gammaIndex` and `sourceTraceIndex` (`RationalSourceGammaIndex`); a compact open `H ≤ K` with this factorization in both orders `m u v`, `m v u`, `gammaAuxiliarySubgroup` (from `exists_dynamic_oppositeIwahoriContractionBasis`), and `γ(P̄) = γ(P)` for the opposite parabolic, given `hstable` for both, `gamma_oppositeCocharacter` (`RationalSourceGammaOpposite`); the change of `γ` when `K` is replaced by a compact open `H ≤ K`, for connected reductive `G` (no `hstable`), `γ_H(P) = γ_K(P) [P ∩ K : P ∩ H] [Ū ∩ K : Ū ∩ H] [K : H]^{-1}`, `gamma_eq_mul_gammaCompactIndex`, with `gammaCompactIndex` (`RationalSourceCompactComparison`); the generic index expression `openCellConstant_eq_relIndex_mul`; (3) itself (one `H` for all semi-standard `P`, the root-subgroup product of the radical indices, and dependence of `γ(P)` on `M` only): none; (5): `measure_doubleCoset_le_of_doubleCosetIndex` (generic, from bounds on `[H : H ∩ mHm^{-1}]`), upper bound for `GL_n`: `exists_measure_doubleCoset_le_delta`; a related upper bound modulo the full center on actual rational points, `rationalLatticeQuotientVolume` (given a supplied simultaneous standard basis, the unproved Prop `StandardCocharacterStatement` and the topological premises listed below); restriction `Im X(G) → Im X(A_G)` surjective with finite kernel and the measures on `Im X(A_G)` and `Im X(G)` (p.239): `rationalUnitaryUnramifiedCharacterRestrict_surjective` (without `hindex`), `finite_rationalUnitaryUnramifiedCharacterRestrict_ker` and `rationalUnitaryUnramifiedCharacterHaar` (given the open finite-index premise `hindex`, Renard V.2.6); unimodularity of `G(F)` and the modular characters of standard parabolics: the Props `RationalReductiveUnimodularityStatement`, `RationalParabolicModulusStatement` (the second follows from the first and `DynamicCentralizerReductiveStatement`, `rationalParabolicModulus_of_reductiveUnimodularity`, and `DynamicCentralizerReductiveStatement` is proved, `dynamicCentralizerReductive` (`CentralizerReductiveProof`); the first follows from six structural Props, `rationalReductiveUnimodularity_of_structural_inputs`, of which `IwahoriHaarProductStatement`, `GenericCentralizerStatement`, `FiniteCoverCharacterStatement` and `ModularCharacterRegularityStatement` are proved, `iwahoriHaarProduct`, `genericCentralizer`, `finiteCoverCharacter`, `modularCharacterRegularity`, and `RationalOppositeHaarReciprocityStatement` and `JointSpecialCompactBasisExistenceStatement` are not; `rationalParabolicModulusAssembly` proves `RationalParabolicModulusAssemblyStatement`, the second from the seven structural Props); see below |
| I.2 | 242–243 | finite-dimensional `ρ(A_M)`-stable spaces `V ⊂ C^∞(A_M)`: expansion `f(a) = Σ_{χ ∈ X} χ(a) P_{χ,f}(H_M(a))` with `deg P_{χ,f} ≤ d`; for minimal `X`, polynomial growth on `A_M` ⇔ `Re χ = 0` for all `χ ∈ X`; if `∏_{χ ∈ Y} (ρ(a) − χ(a))^D` kills `V`, then `X ⊂ Y` and `d ≤ D − 1`; the same for `A_M`-finite `f` | I.1 | Book (stated without proof or citation) | for an abstract commutative group `A` in place of `A_M`, an additive `H_M : A → E` with a lattice section (a homomorphism `s : ℤ^d → A` with linear coordinates and `A = ker(H_M) s(ℤ^d)`) and a nonnegative subadditive `L` in place of `σ` (generic, Worker 249): the functions `a ↦ Σ_j χ_j(a) Q_j(H_M(a))` (`exponentialPolynomial`, `WeakConstantTermUniqueness`); the expansion of a function `f` whose right translates span a finite-dimensional space `V_f` (`translateSpan`) and such that every `c ∈ ker(H_M)` has a positive power `c^N` with `f(a c^N) = f(a)` for all `a` (hypothesis `hfin`, which cannot be dropped: `f(n) = n` on `ℤ` with `H_M = 0` has no such expansion), `exists_exponentialPolynomial_of_finiteDimensional`; `hfin` holds when `ker(H_M)` is compact and `f` is invariant under an open subgroup (`exists_pow_mul_eq_of_isCompact`), which gives the form for such smooth `f`, `exists_exponentialPolynomial_of_smooth`; (1) ⇒ (2) in the form "polynomial growth (`HasPolynomialGrowth`) gives an expansion with unitary characters", again under `hfin`, `exists_unitary_exponentialPolynomial_of_hasPolynomialGrowth` (`FiniteFunctionExpansion`); the minimality of `X`, (2) ⇒ (1), `X ⊂ Y` with `d ≤ D − 1` and the uniform degree bound: none; related: Renard App. C.III for `ℤ^d`, `Langlands.IntegerLatticeMatrixCoefficientExponentialPolynomialStatement` (statement and proof in `Langlands/Representation/MatrixCoefficient/IntegerLattice*`), not adapted to I.2 |
| I.3 | 243–244 | Jacquet functor, normalized induction `I_P^G`, filtration `F_w` of `(I_P^G V)_{P'}` | [BZ] | Data, Ext | generic, for actual subgroups with `P = M ⋉ U` and `U` closed in a locally compact nonarchimedean `G`: the normalized Jacquet functor `Langlands.Aubert.General.normalizedJacquetFunctor` and normalized induction `Langlands.Aubert.General.normalizedInductionFunctor` (full-parabolic normalization); the Levi-inflated normalization of I.3 (`LeviNormalizedCovariant`) and its comparison with that functor when `U` is unimodular, `normalizedInductionLeviEquiv` (generic) and `standardNormalizedInductionLeviIsoOfStandardCocharacter` (actual standard rational points, given `StandardCocharacterStatement`); exactness of coinvariants for a group in which every finite subset lies in a compact open subgroup (an explicit premise, not implied by the data above), `smoothCoinvariantExactness`, with that premise for the actual dynamic unipotent radicals `U_G(χ)(F)` of connected reductive groups over local fields supplied by `dynamicUnipotentCompactOpenContainment` (every compact subset of `U_G(χ)(F)` lies in a compact open subgroup); admissibility of Jacquet modules given an Iwahori contraction basis, `isAdmissible_normalizedJacquetFunctor_obj_of_iwahoriContraction`. Toward `F_w`: the Mackey support filtration of compact induction from a closed subgroup `P`, restricted to a closed subgroup `Q`, with its graded pieces (compactly induced orbit pieces), `closedSubgroupMackeyFiltration` (generic); the filtration of the Jacquet module of an induced representation and its graded pieces (Bernstein–Zelevinsky's geometric lemma) only for `GL_n`, `padicGeometricLemma` and its Grothendieck-group form `geometricLemmaGrothendieck`; the Grothendieck-group identity for general groups only as the unproved Props `GeometricK0ExpansionStatement`, `RationalGeometricK0ExpansionStatement`. The identification of the smooth contragredient of `I_P^G V` with `I_P^G V̌` by the quotient integral: `normalizedInductionIntegralDualEquiv` (actual topological subgroup data); the exponents of I.3 for a commutative group `A` acting on a vector space (generic, Worker 249): the joint generalized eigenspace `V_χ` for `χ : A → ℂ` (with `∀ a ∃ k` in place of `∃ d ∀ a`), `jointGenEigenspace`; the eigenvalue function of a nonzero joint generalized eigenvector is a character, `map_mul_of_mem_jointGenEigenspace`, `jointCharacter`; a vector of a finite-dimensional stable subspace is a finite sum of joint generalized eigenvectors, `exists_sum_mem_jointGenEigenspace` (`ExponentDecomposition`); the direct sum `V = ⊕ V_χ` of an admissible `π` and the finiteness of `𝓔xp(π)`: none |
| Thm I.4.1 | 245 | Casselman pairing `⟨·,·⟩_P` on `V_P × V̌_{P̄}` | [C] | Ext | an abstract form of the pairing, between the Jacquet module of `V̌` for one radical and that of `V` for the opposite radical, characterized by evaluation on stable vectors: `StablePairingData.IsStablePairing`, `exists_isStablePairing`, nondegenerate (`IsStablePairing.injective`, `IsStablePairing.flip_injective`) and invariant (`IsStablePairing.map_action`), for supplied `StablePairingData` satisfying `Admits` (generic); `Admits` follows from admissibility and opposite Iwahori contractions, `admits_of_iwahoriContractions`; for the block parabolics of `GL_n` the data are constructed (`standardPairingData_admits`, `refinedPairingData_admits`); the asymptotic formula in the same abstract setting (Worker 249), for a stable pairing `b` under `Admits`, a good `K`, a `K`-fixed vector `v` and a functional `ℓ` of the smooth contragredient fixed by the same `K`: there is a finite `F ⊆ Nbar` (`Nbar` in the role of `U`) with `ℓ(ρ(a) v) = b [ℓ] [ρ(a) v]` for every `a` commuting with `M` and `g`, with `a (K ∩ Nbar) a⁻¹ ⊆ K`, `a⁻¹ (K ∩ N) a ⊆ K` and `a F a⁻¹ ⊆ K`, `IsStablePairing.exists_finset_asymptotics`; as a property `HasAsymptotics` of `b` (for the elements `IsContractingElement`, the four conditions for every good `K`), `IsStablePairing.hasAsymptotics`, its `δ^{1/2}`-normalized form for a character `δ` of `M` and `a ∈ M`, `HasAsymptotics.normalized`, along the powers of `g⁻¹` from some power on, `IsStablePairing.exists_pow_asymptotics`, and the existence of a pairing nondegenerate on both sides, invariant under `M` and with `HasAsymptotics`, `exists_nondegenerate_invariant_hasAsymptotics` (`StablePairingAsymptotics`); that the cone `\|α(a)\|_F < ε` of `A_M` consists of such elements, and the data for parabolics of actual reductive groups other than the `GL_n` blocks: none |
| Cor. I.4.2 | 245 | `V̌_{P̄}` is the contragredient of `V_P` | I.4.1 | Book | for the block parabolics of `GL_n`: `standardNaturalJacquetDuality`, `refinedNaturalJacquetDuality` (natural families `r_P(V̌) ≅ (r_{P̄}(V))^∨` on admissible objects, proving `NaturalNormalizedJacquetDualityStatement` as `naturalNormalizedJacquetDuality`); generic, for closed `U`, `O` normalized by `M`, an element commuting with `M` with an opposite Iwahori contraction basis (`HasOppositeIwahoriContractionBasis`) and reciprocal Haar characters on `U` and `O`: a natural family `r_U(V̌) ≅ (r_O(V))^∨` on admissible objects, `exists_naturalNormalizedJacquetDuality_of_iwahoriContractions_of_reciprocalModulus` and `naturalNormalizedJacquetDualityOfIwahoriContractionsOfReciprocalModulus`; on actual rational points only the unproved Prop `RationalNaturalJacquetDualityStatement` |
| Prop. I.4.3 | 245 | coefficients equal Jacquet coefficients on `M_0^+` cones | [C] | Ext | the equality: none; a related strict exponential coefficient bound for `GL_n` from normalized Jacquet bounds, `glStrictCartanCoefficientBound` (proof of `GLStrictCartanCoefficientBoundStatement`) |
| Cor. I.4.4 | 245 | polynomial growth: `\|⟨π(g)v, v̌⟩\| ≤ c‖g‖^d` | I.1 (4), I.4.3 | Book | both assertions as Props on actual rational points, with the norm `rationalMatrixNorm` of I.1: `RationalCoefficientModerateGrowthStatement`, `RationalFiniteLengthModerateGrowthStatement` and their conjunction `RationalModerateGrowthStatement`; the second follows from the first, `rationalFiniteLengthModerateGrowth_of_coefficientGrowth` (`RationalModerateGrowthUniformization`, Worker 1564), through the internal step `FiniteLengthCoefficientGrowthUniformizationStatement`, proved by `finiteLengthCoefficientGrowthUniformization` (`CoefficientGrowthUniformizationProof`, Worker 1564); the first follows from the unproved structural Props `StandardCocharacterStatement` and `JointSpecialCompactBasisExistenceStatement`: `rationalCoefficientModerateGrowthAssembly` proves the implication `RationalCoefficientModerateGrowthAssemblyStatement` (`RationalCoefficientModerateGrowthAssemblyProof`); its internal intermediate Props are proved: `RationalMatrixNormComparisonStatement` (`rationalMatrixNormComparison`), `RationalCompactLatticePolynomialBoundStatement` (`rationalCompactLatticePolynomialBound`), `RationalUnrestrictedLatticeBoundStatement` (`rationalUnrestrictedLatticeBound`), `UnrestrictedCompressedLatticeBoundStatement` (`unrestrictedCompressedLatticeBound`), `RationalUniformizerCoordinateHeightStatement` (`rationalUniformizerCoordinateHeight`), `RationalFiniteChartModerateGrowthStatement` (`rationalFiniteChartModerateGrowth`) and `RationalFiniteSignedCartanCoverStatement` (`rationalFiniteSignedCartanCover`), the last two with supplied structural data in their hypotheses; and polynomial growth in `rationalMatrixNorm` of the regular functions of a group scheme with a closed matrix embedding, `regularFunction_rationalMatrixNorm_powerBound` (`MatrixRepresentationPolynomialGrowth`) |
| I.5 | 245–248 | `B`-families (`B` finitely generated commutative Noetherian), contragredient, Jacquet modules, induction, exponents, rationality; analogue of I.4.1 | I.4.1, [BD, 2.5, 3.1], [BD, 3.5.2] | Data, Book, Ext | for the algebra `B = unramifiedRegularFunctions ν` of regular functions on the unramified characters (generic): normalized induction and normalized Jacquet modules of `B`-linear representations, `UnramifiedNormalized.normalizedInductionFunctor`, `UnramifiedNormalized.normalizedJacquetFunctor` (`UnramifiedNormalizedModels`, Worker 1585), the smooth `B`-linear normalized induced model of the universal twist of an arbitrary complex representation of `M` and its normalized Jacquet model, `UnramifiedNormalized.universalInducedRepresentation`, `UnramifiedNormalized.UniversalJacquet`, with the base change of intertwiners `UnramifiedNormalized.tensorMap` (`UnramifiedNormalizedTensorModels`, Worker 1585); these are the coefficient-ring construction underlying I.5, smooth `B`-linear representations, not `B`-families in Waldspurger's sense: condition (ii) of the definition (the invariants under each compact open subgroup are projective `B`-modules of finite type) is not proved for them, and the universal twist `universalUnramifiedRepresentation` (`UnramifiedUniversalTwist`); on actual rational points of a connected reductive group (for a topology in which the valuation-image projection is continuous), `B` is of finite type, Noetherian and a domain, with fraction field `rationalUnramifiedFunctionField`: `rationalUnramifiedRegularFunctions_finiteType`, `rationalUnramifiedRegularFunctions_isNoetherianRing`, `rationalUnramifiedRegularFunctions_isDomain` (`RationalUnramifiedFunctionField`, Worker 1615), it has unique factorization, `rationalUnramifiedRegularFunctions_uniqueFactorizationMonoid` (`RationalUnramifiedFactorization`), and an element vanishing on a nonempty open set of characters is zero, `rationalUnramifiedRegular_eq_zero_of_isOpen` (`RationalUnramifiedDensity`); for the actual rational normalized induced model of the universal unramified twist over the algebra of regular functions on the unramified characters of an actual Levi, `RationalNormalized.Induced` over `RegularAlgebra` (`UnramifiedRationalNormalizedModels`), statements from Renard VI.8.1–VI.8.2 with explicit structural premises (closed unipotent image, continuous semidirect projection, compact `P(F)\G(F)`): flatness and condition (ii) for admissible `π`, the Prop `UniversalInducedCoefficientFinitenessStatement` (`UnramifiedRationalNormalizedInducedFiniteness`, Worker 1761), proved by `universalInducedCoefficientFiniteness` (`UnramifiedRationalNormalizedInducedFinitenessProof`, Workers 1754 and 1582), and the bijectivity of the specialization `ℂ ⊗_B Induced → complexInduced` at each unramified character, `inducedScalarExtension`, the Prop `RationalNormalizedInducedSpecializationStatement` (`RationalNormalizedInducedSpecializationStatement`, Worker 1759), proved by `rationalNormalizedInducedSpecialization` (`RationalNormalizedInducedSpecializationProof`, Worker 1635); flatness and condition (ii) for the universal twist `B ⊗ E` of an admissible representation `E` of the actual Levi (Renard VI.8.1), the Prop `RationalUniversalTensorFinitenessStatement` (Worker 1759), proved by `rationalUniversalTensorFiniteness` (`RationalUniversalTensorFinitenessProof`, Worker 1780); Jacquet modules of the universal induced supercuspidal family (Renard VI.9.2): finite generation of their compact-open invariants is the unproved Prop `RationalSupercuspidalJacquetFamilyFiniteStatement` (`UnramifiedRationalJacquetFinitenessStatement`, Workers 1775 and 1780), and compact compression in three different scopes, each also assuming an Iwahori contraction `hc` and the centrality `hcentral` of the contracting element in the output Levi: (a) one positive exponent, chosen before all unramified characters, making the compressed action on every specialization of one universal induced family stable, given finite generation of the native compact-fixed module of that family and of its native Jacquet fixed module and bijectivity of every specialization (`hbij`), `complexInducedCompressedAction_uniform_of_native_finite` (`UnramifiedRationalFamilyCompression`); (b) eventual stability (some positive stable power, depending on the object) of the compressed action on the actual normalized induction of each cuspidal object `E` of the Levi, given `StandardCocharacterStatement`, connected reductivity of `G` and `M` and the standard-family structure, the whole cuspidal inertia product decomposition `hdecomp` (`IsRationalCuspidalInertiaProductDecomposition`), finiteness of the cuspidal inertia classes with nonzero fixed vectors at each compact open level `hfinite`, the norm-kernel small-progenerator property `hgen` (`IsRationalNormKernelSmallProgenerator`) of every irreducible cuspidal representative, admissibility and native output-Jacquet finiteness of every irreducible cuspidal representative `hNative` (`RationalCuspidalNativeJacquetInputs`), compactness of the inducing quotient and continuity of the semidirect projection, `rationalCuspidalInduction_eventuallyStable_of_nativeJacquet` (`RationalCuspidalInductionCompression`, Worker 1751); (c) one positive threshold for all objects of the lifted inertia block of one fixed representative `π` (`RationalInducedInertiaBlockEventuallyStationary`), given the small-progenerator property `hgen` of `π`, admissibility of `π`, native output-Jacquet finiteness `hJac` for `π`, compactness of the inducing quotient and continuity of the semidirect projection, `rationalInducedInertiaBlock_stationary_of_nativeJacquet` (`RationalInertiaBlockCompression`, Worker 1751); these premises are explicit there and not proved, and no exponent uniform over inertia classes or over all smooth representations is asserted; the support filtration of the Jacquet modules of the universal induced family with orbit grades, given supplied ordered double-coset orbit geometry, compactness of the inducing quotient and connected reductivity of `G`, `universalOutputJacquetSupportGradedOrbitIso`, and their admissibility from that of the orbit quotients, `universalOutputJacquet_isAdmissible_of_orbits` (`UnramifiedRationalJacquetSupport`); contragredients, exponents, rationality and the analogue of I.4.1 for `B`-families: none |
| Lemme I.6.1, Prop. I.6.2 | 249–250 | `C_lisse(G)`, `ρ`, `λ`; `A_ρ = A_λ = A(G)`; constant term `f_P` of `A(G)` and `f_P^{Ind}` | I.4 | Data, Book | the coefficient space `A(π)` of a smooth representation as the range of `coefficientTensorMap` (`range_coefficientTensorMap`: the span of the coefficients); Lemma I.6.1 for right translation, for a topological group with a compact open subgroup, with `A_ρ` as `IsRightAdmissible` (bi-invariance under a compact open subgroup and admissibility of `ρ_f` on `V_ρ(f) = rightTranslateSpan f`) and `A(G)` as the union of the `A(π)` over admissible `π` on carriers in the universe of `G`: `V_{ρ×λ}(f) = A(ρ_f)`, `twoSidedTranslateSpan_eq_coefficientFunctionSpace`, `A_ρ = A(G)`, `isRightAdmissible_iff`, and the closure of the union under addition, `exists_admissible_coefficient_add` (`AdmissibleCoefficientSpace`, Worker 249); Lemma I.6.1 for left translation in the same setting, with `λ` the Library's `GroupAction.leftFunctions`, `A_λ` as `IsLeftAdmissible` and `λ̌_f` the smooth contragredient `contragredientRep` of `λ_f`: `A_λ = A(G)`, `isLeftAdmissible_iff`, and `V_{ρ×λ}(f) = A(λ̌_f)` for `f ∈ A_λ`, `twoSidedTranslateSpan_eq_coefficientFunctionSpace_left` (`AdmissibleCoefficientSpaceLeft`, Worker 249); the uniqueness part of Prop. I.6.2 (generic, Worker 249), with `A_M` replaced by a subgroup `Z` whose elements commute with all of `M` and the cones `\|α(a)\|_F < ε` by nonempty `C ⊆ Z` with `C S ⊆ C` for a generating `S ⊆ Z`: two elements of `A(M)` (each in `A(π)` for an admissible `π`) that coincide on `m C_m` for every `m` are equal, `eq_of_mem_coefficientFunctionSpace_of_eqOn_cones`, from right finiteness `IsRightFinite` (`isRightFinite_of_mem_coefficientFunctionSpace`) and `IsRightFinite.eq_of_eqOn_cones` (`RightFiniteUniqueness`); that the source's cones are of this form: none; the existence of the constant term `f_P` and `f_P^{Ind}`: none |

## Chapter II. `Ξ`, `σ` and estimates (pp.250–263)

| Item | Page | Content | Uses | Class | Lean coverage |
|---|---|---|---|---|---|
| II.1 | 250–251 | `Ξ(g) = ⟨π(g)e, e⟩ = ∫_K δ_0(m_0(kg))^{1/2} dk` | I.1, I.3 | Data | `xi` (generic, see below) |
| Lemme II.1.1 | 251 | `Ξ` bi-`K`-invariant; `C_1 δ_0^{1/2} ≤ Ξ ≤ C_2 δ_0^{1/2}(1+σ)^d` on `M̄_0^+` | I.1, I.3, I.4.3 | Book | bi-invariance `xi_mul_mul`; lower bound `xiLowerBound_of_factorization` (generic, from an Iwahori-type factorization); the upper bound is the hypothesis `XiUpperBound` (open; needs I.4.3) |
| Lemme II.1.2 | 251 | translation bound `Ξ(g_1 g g_2) ≤ C Ξ(g)(1+σ(g))^d` | I.1 (4), I.4.3, II.1.1 | Book | `xi_uniformTranslationBound` (generic, with `d = 0`; proof via II.1.3, not the article's) |
| Lemme II.1.3 | 252 | `∫_K Ξ(g_1 k g_2) dk = Ξ(g_1) Ξ(g_2)` | II.1 | Book | `integral_xi_mul_mul` (generic) |
| Lemme II.1.4 | 252 | `Ξ(g^{-1}) = Ξ(g)` | II.1 (`π ≅ π̌`) | Book | `xi_inv` (generic; `G` unimodular and `δ` the modular character of `P` as hypotheses, see below) |
| Lemme II.1.5 | 252 | `∫_G Ξ^2 (1+σ)^{-d} < ∞` for some `d` | I.1 (4)–(6), II.1.1 | Book | `CartanSquareBound.squareIntegrableWeight` (generic; the Cartan, measure, norm and II.1.1 bounds as hypotheses, see below) |
| Lemme II.1.6 | 252 | `Ξ(g) = ∫_K δ_P(m_P(kg))^{1/2} Ξ^M(m_P(kg)) dk` | II.1 | Book | `LeviData.xi_eq_integral` (generic; direct Fubini proof, not the article's induction in stages) |
| II.2 | 253–254 | algebraic representation `τ_P` with properties (1)–(5); (6) `1 + σ(ū) ≍ 1 + log‖τ_P(ū)e_1‖` | [H] | Book (the construction is on p.253 and (6) is proved on p.254 from (7), (8) and [H]) | (6) as stated: none; the properties used are explicit hypotheses of `TauEstimates` and `OpenCellLemma`; a different route to the upper bound of `σ` in (6) (not through (7), (8) and [H]), for the opposite unipotent subgroup `Ū = U(χ⁻¹)` of a cocharacter `χ` on actual rational points of an affine group scheme over a nonarchimedean local field: the height of `ū ∈ Ū(F)` in a closed matrix representation is at most `C max(1, ‖ρ(ū)v‖)^D` when `v` is an eigenvector of every `ρ(χ(t))` fixed by no `ū ≠ 1`, `exists_rationalMatrixNorm_le_of_weightVector` (`OppositeUnipotentHeight`; from the diagonal case `exists_rationalMatrixNorm_le_of_diagonal` in `OppositeUnipotentDisplacement` and the contraction lemmas `exists_offIdentityNorm_le_mul_pow`, `exists_le_mul_pow_of_contractionScaling` in `DiagonalContraction`, `ContractionScaling`); such a vector on a Chevalley line with stabilizer `P(χ)`, `exists_parabolic_line_rationalMatrixNorm_le` (`ParabolicLineHeight`); and the bound in terms of the character `χ_P` of `P(χ)` on that line, for `ū = p k` with `k` in a fixed compact set, `exists_parabolic_line_character_bounds` (`ParabolicLineCharacter`; the comparison of `χ_P` with `δ_P` is not proved); the same two kinds of bound for an arbitrary nonzero eigenvector of `P(χ)(F)` or of its Levi, `exists_abs_eigenvalue_le`, `exists_le_abs_eigenvalue` (`EigenlineIwasawaBounds`), applied to the determinant line of the adjoint action on `Lie U(ψ)`, `exists_le_abs_adjointDeterminant` (`ParabolicDeterminantLine`); the height of the Levi component, `‖m‖ ≤ C ‖m u‖` for `m ∈ Z(χ)(F)`, `u ∈ U(χ)(F)`, `exists_rationalMatrixNorm_levi_le` (`LeviProjectionHeight`) |
| Lemmes II.3.1–II.3.5 | 254–259 | estimates for `δ_P(m_P(ū))`, `σ` on `Ū` | II.2, I.1 | Book | generic, from properties of `τ_P` as hypotheses: II.3.1 `sigmaProductBound_height` (given the block form; for the standard block parabolics of `GL_n` without hypotheses, `sigmaProductBound_glBlock`), II.3.2 `cartanWeightComparison_of_norm`, II.3.3 `conj_height_le_of_tau`, II.3.4 `modulusHeightBounds_of_tau`, II.3.5 `openCellBound_of_mul`; related, not stated in the article: polynomial growth of the Haar volume of the height balls of closed subgroups of `U(χ⁻¹)(F)` normalized by `χ`, `exists_measure_rationalMatrixNorm_le_pow`, `exists_measure_rationalMatrixNorm_le_mul_pow` (`UnipotentHeightVolume`), and the integrability of negative powers of the height on such subgroups, `exists_integrable_rationalMatrixNorm_rpow_neg` (`UnipotentHeightIntegrability`, from `HasPolynomialSublevelVolume`) |
| Lemmes II.4.1–II.4.4, Prop. II.4.5 | 259–263 | integrals over `Ū`; constant term of functions bounded by `Ξ(1+σ)^{-d'}` | II.1, II.3 | Book | generic: II.4.1 `levelSetMeasureBound_of_torusXiFormula`, II.4.2 `unipotentWeightIntegrable_of_levelSets`, II.4.3 `LeviData.unipotentWeightIntegrable`, II.4.4 `XiUpperBound.unipotentXiBound`, II.4.5 `constantTermEstimate_of_bounds` (it proves the Prop `ConstantTermEstimate` of `ConstantTerm`); the inputs are listed in the modules below |

## Chapter III. Tempered representations and `C(G)` (pp.263–276)

| Item | Page | Content | Uses | Class | Lean coverage |
|---|---|---|---|---|---|
| III.1 | 263 | square integrable modulo `A_G` | I.1 | Data | `IsSquareIntegrableModCentralSubgroup` |
| Prop. III.1.1 | 263 | square integrability via exponents | [C] | Ext | `GL_n` (see Library coverage); on actual rational points of connected reductive groups, the sufficiency of strict normalized Jacquet exponents for square integrability modulo the full center: the Prop `RationalStrictJacquetSquareIntegrabilityStatement` (with `StandardCocharacterStatement` among its premises), proved from the unproved Prop `JointSpecialCompactBasisExistenceStatement` by `rationalStrictJacquetSquareIntegrabilityReduction`; the criterion along arbitrary rational parabolics in Renard's form (Renard VII.1.2, a derived cone formulation): the Prop `ArbitraryParabolicCasselmanCriterionStatement` (`ArbitraryParabolicCasselmanStatement`, Worker 6; statement only) |
| Cor. III.1.2 | 263–264 | coefficients bounded by `c Ξ(1+σ)^{-r}` on `G^1`, for every `r` | I.1 (4), I.4.3, II.1.1, III.1.1 | Book | GL_n only; the conclusion as a Prop, with a supplied subgroup in place of `G^1`: `HasRapidlyDecreasingCoefficientsOn` (generic, statement only); a related exponential bound for coefficients on lattice rays of actual rational points, from strict normalized Jacquet exponents and a supplied simultaneous standard basis: `rationalLatticeCoefficientDecay` |
| Lemme III.1.3 | 264 | an admissible square-integrable representation is unitary and semisimple | II.1.5, III.1.2 | Book | for irreducible representations of `GL_n` block Levis: square integrable modulo the center implies tempered, `glLeviDiscreteSeriesTempered`, and tempered implies unitarizable, `glLeviTemperedUnitarity`; generic: admissible unitarizable representations are semisimple, `admissibleUnitarySemisimplicity` (compact open subgroups cofinal); generic: an irreducible representation that is square integrable modulo a normal central subgroup `A` is unitarizable, `isUnitarizable_of_isSquareIntegrable` (`SchurOrthogonality`; a Haar measure on `G ⧸ A` invariant under inversion and the premise `hcof` that every open subgroup contains a compact open subgroup are hypotheses; the proof uses one smooth functional in place of Waldspurger's sum over generators); for not necessarily irreducible admissible representations square integrable modulo a normal central subgroup `A` (same setting and hypotheses): unitarizable, `isUnitarizable_of_isSquareIntegrableModCentralSubgroup`, and semisimple, `isSemisimpleRepresentation_of_isSquareIntegrable` (`SquareIntegrableSemisimplicity`); for irreducible representations, with a left Haar measure on `G ⧸ A` not assumed invariant under inversion (normal central `A`, compact open subgroups cofinal), unitarizable: `isUnitarizable_of_irreducible_isSquareIntegrable_leftHaar` (`LeftHaarSquareIntegrableUnitarity`) |
| III.1 (2), (3) | 265 | Schur orthogonality, formal degree `d(π) > 0` | [C], III.1.2, II.1.5 | Ext | generic (`SchurOrthogonality`), for representations of a topological group `G` on which a normal central subgroup `A` acts by one character, with a Haar measure on `G ⧸ A` invariant under inversion and the premise `hcof`: (2) for irreducible admissible inequivalent `π₁`, `π₂` whose orthogonality integrands are integrable, `orthogonalityIntegral_eq_zero_of_integrable` (the form needed for tempered `π₂` in the proof of III.7.1); that integrability, for left-invariant measures `μ` on `G` and `ν` on `G ⧸ A`, when the first representation is `π ⊗ χ'` with `π` smooth with tempered coefficients and `χ'` a unitary character with open kernel, and the second is a smooth `ω` with the conclusion of Cor. III.1.2 for `ω̌` on `ker p`, the two acting on `A` by the same character, given `TranslationWeights` and `L2Weights`, in the setting of `TraceFamilyScalar` (a surjective `p : G →* Λ` with open kernel, `Λ / p(A)` finite, the measure compatibility `hcompat` with `m ≠ 0, ∞`): `integrable_orthogonalityIntegrand_of_tempered` (`TemperedTwistIntegrability`, Worker 249), and for square-integrable ones `orthogonalityIntegral_eq_zero`; (3) for irreducible `π` square integrable modulo `A` (`IsSquareIntegrableModCentralSubgroup`): `exists_formalDegree`, `formalDegree`, `formalDegree_pos`, `formalDegree_unique`, `orthogonalityIntegral_eq_formalDegree`. The unimodularity of `G/A_G` and `hcof` for Waldspurger's `G` are not proved there; the formal degree of an actual irreducible representation, its positivity and its invariance under equivalence and under unitary twists, `representationFormalDegree`, `representationFormalDegree_pos`, `representationFormalDegree_equiv`, `representationFormalDegree_unitaryTwist` (`FormalDegreeComparisons`), its descent to classes and twist orbits, `discreteSeriesFormalDegree`, `discreteSeriesOrbitFormalDegree` (`DiscreteSeriesFormalDegree`), and its scaling with the Haar measure, `discreteSeriesFormalDegree_smul_measure` (`FormalDegreeHaarScaling`) (Worker 200), also on twist orbits, `discreteSeriesOrbitFormalDegree_smul_measure` (`DiscreteSeriesOrbitHaarScaling`); the Hermitian forms of (2), (3) for coefficient tensors, in the same setting with a unitary central character: `hermitianCoefficientPairing_eq_zero` (inequivalent irreducibles), `hermitianCoefficientPairing_eq_inner` (`(E ψ₂, E ψ₁) = d⁻¹ (ψ₂, ψ₁)` for the tensor form of a positive invariant form), `hermitianCoefficientPairing_eq_inner_of_equiv` (`HermitianSchurOrthogonality`, Worker 249) |
| Lemme III.2.1, Prop. III.2.2, Lemme III.2.3 | 265–267 | tempered representations; criteria via exponents; induction | I.2, I.3, I.4.1, I.6.1, II.1.1, II.1.2, III.1.2 | Book | for `GL_n` see `GL_n`-specific work; generic growth condition `HasTemperedGrowth` (`TemperedPairing`); on actual rational points of a connected reductive group, the exponent side of Prop. III.2.2 in Renard's normalized form (Renard VII.2.1: the normalized Jacquet exponents along every parabolic lie in the nonnegative cone of the restricted simple roots) as a definition, `RepresentedParabolic.IsNormalizedExponentTempered` (`ArbitraryParabolicTempered`), with the unitarity of the exponents for the full group, `normalizedTemperedFullGroupExponent` (`NormalizedTemperedFullGroupProof`, Worker 1590), the unitarity of the central character on a split component, `normalizedTemperedUnitarySplitCentralCharacter` (`NormalizedTemperedSplitCentralCharacter`), a logarithmic reformulation, `normalizedTemperedLogarithmicComparison` (`NormalizedTemperedLogarithmicComparison`, Worker 6, Worker 1593), and the reduction to standard parabolics from four structural Props, `normalizedTemperedStandardReduction_of_dynamic_structural_statements` (`NormalizedTemperedStandardReductionFromDynamics`); that square-integrable representations satisfy the exponent condition (Renard VII.2.1, Remark 2, without irreducibility), the Prop `SquareIntegrableNormalizedTemperedStatement` (Worker 6; statement only); exponents under induction and restriction (Renard VII.1.1), the Prop `ArbitraryParabolicExponentStatement` (Worker 6; statement only), with lemma (i) `inducedExponent_restrict` (`ArbitraryParabolicInductionComparison`, Worker 1666), lemma (ii) `normalizedJacquetExponent_restrict` (`JacquetExponentRestriction`, Workers 1670 and 1666; both given the compatibility of the two split components), the characteristic-space decompositions and finiteness `generalizedWeightSpace_decomposition`, `finite_generalizedWeights_of_spanning` (`SplitComponentDecomposition`, `SplitComponentFiniteSupport`, `SplitComponentComparison`, Worker 1666) and the finite-exponent reduction from two structural Props, `arbitraryParabolicFiniteSupport_reduction` (`ArbitraryParabolicFiniteSupportReduction`); Lemma III.2.1 for a topological group with a compact open subgroup, with tempered as `HasTemperedCoefficients Ξ σ`, `C^w_lisse(G)` replaced by `HasTemperedGrowth Ξ σ` and Lemma II.1.2 as `TranslationWeights Ξ σ`: `temperedCoefficient_iff` (union) and `exists_tempered_coefficient_add` (sum) (`AdmissibleCoefficientSpace`, Worker 249); Lemma III.2.3 for normalized induction from `P = M ⋉ U` (`U` closed and unimodular) in the setting of `InducedCoefficientXi`, for an admissible `π` with `HasTemperedCoefficients (Ξ^M) σ_M`, with `LeviData`, the Iwasawa pairs `G = P_0 K` and `M = (P_0 ∩ M)(K ∩ M)`, `δ_0` trivial on `P_0 ∩ K`, `P` closed, `m_P` continuous, `G = P K`, `G` unimodular, the modular character of `P` equal to its modulus on `U`, `σ ≥ 0` and `σ(kg) = σ(g)` for `k ∈ K`: `HasTemperedCoefficients Ξ σ` for `I_P^G π`, with `σ_M ≥ 0` and the derived bound `LeviSigmaBound` (`σ_M(m_P(q)) ≤ c(1 + σ(qk))`), `hasTemperedCoefficients_normalizedInduction_of_tempered`, and with `σ_M = σ\|_M`, `σ(gk) = σ(g)` and Lemma II.3.1 as `SigmaProductBound M U σ`, `hasTemperedCoefficients_normalizedInduction_of_sigmaProductBound` (`InducedTemperedCoefficients`, Worker 249; a derived route through Lemma II.1.6, not the exponent proof); the equivalence of the exponent condition with tempered growth: none |
| Lemmes III.3.1–III.3.3 | 267–268 | weak constant terms `π^w_P` | I.3, III.1.1, III.2.2 | Book | the decomposition `V_P = V^w_P ⊕ V^+_P` for one vector `y` of a finite-dimensional subspace stable under the centre, as the split `F = F^w + F^+` of the coefficient `m ↦ λ(J(m) y)` with polynomials in the right translation by `j(a₀)` annihilating the two parts (roots of modulus `1`, resp. of modulus `≤ θ < 1` when the non-unitary exponents satisfy `\|χ(a₀)\| < 1`), `exists_weak_positive_decomposition` (`ExponentDecomposition`, generic, Worker 249); Lemmas III.3.1–III.3.3: GL_n only (III.3.1) |
| Prop. III.4.1 | 269 | an irreducible tempered representation embeds in some `I_P^G ω`, `ω ∈ E_2(M)` | III.3.2, III.3.3 | Book | `GL_n` only: `glTemperedDiscreteSeriesSupport` (proof of `GLTemperedDiscreteSeriesSupportStatement`: an irreducible admissible tempered representation of `GL_n(F)` embeds in a representation normally induced, from the opposite of a standard block parabolic, by an irreducible representation of its Levi that is square integrable modulo the center) |
| Lemme III.5.1 | 269–270 | weak constant term `f^w_P` of `f ∈ A^w(G)` | III.3 | Book | the limit `lim_{a →_P ∞}` of III.5, for a map `H_M : A → a_M` on an abstract group and a finite set of linear forms in place of `Σ(P)`, `TendstoZeroAlongParabolic`; the uniqueness of `f^w_P` (`WeakConstantTermUniqueness`, generic, Worker 249): a function `Σ_j χ_j(a) Q_j(H_M(a))` with unitary characters `χ_j` (`exponentialPolynomial`) whose limit is `0` vanishes, `exponentialPolynomial_eq_zero_of_tendstoZeroAlongParabolic`, and two candidates agree, `eq_of_tendstoZeroAlongParabolic`, with the additivity of `H_M`, an `a₀` with `⟨α, H_M(a₀)⟩ > 0` for all `α`, and the form (1) with `Re(χ) = 0` of the differences of the candidates as hypotheses; the existence part in abstract form (generic, Worker 249): an exponential polynomial with decaying characters (`IsDecayingAlongParabolic`, the conditions `Re(χ) ∈ +ā_P^{G*}`, `Re(χ) ≠ 0` of (1)) and coordinates in the span of the roots has limit `0`, `tendstoZeroAlongParabolic_exponentialPolynomial`, and `f^w_P` exists and is unique given the equality of I.6.2 and the form (1) of `ϕ` as hypotheses, `existsUnique_tendstoZeroAlongParabolic_sub` (`WeakConstantTermExistence`); the source's existence argument needs this span condition (see "Notation and source corrections"; abstract counterexample `not_tendstoZeroAlongParabolic_fst_mul_expNegSnd`); uniqueness within a class given by explicit finiteness, invariance and growth hypotheses, `eq_of_tendstoZeroAlongParabolic_of_mem` (`FiniteFunctionExpansion`); the spaces `A^w` and the derivation of (1) from the exponents of `π_P`: none |
| III.6 | 271–272 | `C(G)`, seminorms `ν_r`, levels `C_H`, inductive-limit topology, (1), completeness, `C_c^∞(G)` dense, `G × G` acts continuously, constant term `f^{(P)}` via II.4.5 | I.6, II.1, II.1.2, II.4.5, [B] | Data, Book | generic: `C(G)`, `ν_r`, `C_H`, topology, (1), density, `G × G` continuity, completeness (`Space.completeSpace`, for a cofinal sequence of compact open subgroups), `f^{(P)}` and `C(G) → C(M)` (`constantTerm`, with II.4.5 as a hypothesis), `f^{(P),Ind}` and the diagram (`constantTermInd`, pointwise; see below) |
| Lemme III.6.1 | 271 | for `f_1, f_2 ∈ C(G)`: `∫_G f_1(h) f_2(h^{-1}g) dh` converges absolutely, `f_1 * f_2 ∈ C(G)`, and `(f_1, f_2) ↦ f_1 * f_2` is separately continuous | II.1.3–II.1.5 | Book | `Convolution` (generic; II.1.3–II.1.5 as hypotheses) |
| III.7, Prop. III.7.1, Cor. III.7.2, III.7.3 | 273–276 | `π(f)`, `θ_π(f)` continuous on `C(G)`; `E_2(G)`; orbits `O` of `Im X(G)`; polynomials on `O`; `W(G\|M)`; regular `ω`: `(I_P^G ω)^w_{P'}` semisimple | III.1.2, III.3.2, III.3.3, III.6.1 | Data, Book | first paragraph (generic, for an admissible representation with the displayed coefficient-growth hypothesis `HasTemperedCoefficients`): `π(f)` `schwartzAction`, of finite rank `schwartzAction_mem_finiteRankEnd`, `θ_π` as a continuous linear form `schwartzCharacter`, `π(f_1 * f_2) = π(f_1) π(f_2)` `schwartzAction_convolution`; second paragraph, `f φ ∈ C(G)` for `f ∈ A(ω)` and `φ ∈ C_c(G/N)`: `TranslationWeights.mul_mem_schwartzSubmodule` (generic, with an open normal subgroup `N` in place of `G^1` and the conclusion of Cor. III.1.2 as the hypothesis `HasRapidlyDecreasingCoefficientsOn`); proof of Prop. III.7.1, the operator `π[φ]` of a family with properties (1), (2) and its naturality: `IdempotentFamily.operator`, `IdempotentFamily.operator_intertwining` (generic), and the concrete family `φ_H = φ ψ_H` with the first displayed equality for `π[φ]`: `traceFamily`, `traceFamily_operator_eval` (generic, with an open normal subgroup in place of `G^1`); the Schur step of that proof (printed pp.274–275), for `ω` in place of `ω ⊗ χ` and in the setting of `SchurOrthogonality`: `ψ^{ρ̌}_H(g) = ψ^ρ_H(g^{-1})` for admissible `ρ`, `traceCoefficient_smoothContragredient`; the integral over `G ⧸ A` of `ψ_H(g) ℓ(π(g) v)` vanishes for irreducible admissible inequivalent `π`, `ω` with integrable integrands, `integral_traceOrthogonalityIntegrand_eq_zero`, and equals `d(ω)^{-1} ℓ(e_H v)` for `π = ω` irreducible and square integrable modulo `A`, `integral_traceOrthogonalityIntegrand_eq_formalDegree` (and `d(ω)^{-1} ℓ(v)` for `H`-fixed `v`, `integral_traceOrthogonalityIntegrand_eq_formalDegree_of_mem`) (`TraceOrthogonality`, generic; `d(ω ⊗ χ) = d(ω)` is `representationFormalDegree_unitaryTwist`, see III.1 (2), (3)); the computation of `π[φ]` with the twists by `χ` and the Fourier inversion on `G^1 A_G \ G`, in an abstract setting (the setting of `SchurOrthogonality` with `G` second countable and a right-invariant Haar measure `μ` on `G`) with a surjective `p : G →* Λ` with open kernel in place of `G → G/G^1` (every compact open subgroup in `ker p`), a central normal `A` in place of `A_G` with `Λ / p(A)` finite, the characters of `Λ` in place of `X(G)`, `Λ →₀ ℂ` in place of `C_c(G/G^1)`, Haar measures related by `hcompat` with a constant `m ≠ ∞` (not compared with `[G : G^1 Z_G]`), the weight hypotheses of `traceFamily` and the conclusion of Cor. III.1.2 for `ω̌` on `ker p` (`hD`), `ω` irreducible and square integrable modulo `A`, `π` irreducible admissible with tempered coefficients and the integrability as the hypothesis `hint`: `traceFamily_operator_eq_smul` (`π[φ] = P • id`, for a chosen `χ_0` with `χ_0(p(a)) c_ω(a) = c_π(a)`), `traceFamily_operator_eval_eq_zero` (`ℓ(π[φ] v) = 0` for admissible `π` with tempered coefficients and admissible `ω` whose characters on `A` differ at a point of `A ∩ ker p`), `exists_character_comp_eq` (`TraceFamilyScalar`, Worker 249); Prop. III.7.1 in that setting, with the unitary characters of `Λ` in place of `Im X(G)`, `π ∈ O` as `π ≃ ω ⊗ (χ ∘ p)` with `χ` unitary, a polynomial on `O` as `b : Λ →₀ ℂ` with `b̂` constant on the classes of `O` (`hb`): `orbitPolynomialOperator` (`π(p) = π[φ_b]`), (i) for admissible `π`, `τ` with tempered coefficients and an intertwiner `T : π → τ`, `T ∘ π(p) = τ(p) ∘ T`, `orbitPolynomialOperator_comp`, (iii) for `π` irreducible admissible with tempered coefficients, `π ≃ ω ⊗ (χ₁ ∘ p)` with `χ₁` unitary, `m ≠ 0` and `hint`, `π(p) = b̂(χ₁)`, `orbitPolynomialOperator_eq_smul_of_equiv`, (ii) for `π` irreducible admissible with tempered coefficients, on which `A` acts by a unitary character, satisfying `hint` and equivalent to no `ω ⊗ (χ ∘ p)` with `χ` unitary, `π(p) = 0`, `orbitPolynomialOperator_eq_zero`; proof of Cor. III.7.2, the Fitting decomposition of an intertwiner of an admissible representation: `isCompl_fittingRange_fittingKernel`, `bijOn_fittingRange` (generic); Cor. III.7.2 in the setting above with `m ≠ 0`, for an admissible `π` with tempered coefficients, with subquotients given by an injective `i : τ → π` and a surjective `q : τ → π'` on types in the universe of `V`: the finiteness of `Σ`, `exists_orbit_covering` (a derived counting argument through `dim V^H`), and the existence and uniqueness of `V = V₁ ⊕ V₂` with every irreducible subquotient of `V₁` equivalent to `ω` and none of `V₂`, `existsUnique_orbitIsotypic_decomposition`, under the hypothesis `hsub` (every irreducible subquotient of `π` has a unitary character of `A` and satisfies `hint`) (`OrbitPolynomialOperator`, Worker 249); the consequences of temperedness used there (`TemperedTwistIntegrability`, Worker 249): for a nonzero smooth `ρ` with tempered coefficients on which `A` acts by a character `c`, with `Ξ` positive and invariant under `A` and `σ` nonnegative and subadditive, `‖c‖ = 1`, `norm_centralCharacter_eq_one`; `hint` for a smooth `π` with tempered coefficients on which `A` acts by a unitary character, `ω` smooth with `hD` and a unitary character on `A`, `m ≠ 0, ∞`, `TranslationWeights` and `L2Weights`, given `IsUnitaryDetecting A` (every character of `G` with open kernel and absolute value `1` on `A` is unitary), `hint_of_tempered`; `hsub` for an admissible `π` with tempered coefficients, given in addition that `Ξ` is invariant under `A` and `σ` is subadditive, `hsub_of_tempered`; Prop. III.7.1 (iii) without `hint`, given `IsUnitaryDetecting A`, `orbitPolynomialOperator_eq_smul_of_equiv_of_tempered`; Prop. III.7.1 (ii) without the hypotheses on the central character of `π` and `hint`, and Cor. III.7.2 without `hsub`, given `IsUnitaryDetecting A`, `Ξ` invariant under `A` and `σ` subadditive, `orbitPolynomialOperator_eq_zero_of_tempered`, `existsUnique_orbitIsotypic_decomposition_of_tempered`; `IsUnitaryDetecting A` when `Λ / p(A)` is finite and every character of `G` with open kernel has absolute value `1` on `ker p`, `isUnitaryDetecting_of_norm_eq_one_on_ker`; on the rational points of a connected reductive group over a nonarchimedean local field, absolute value `1` on the common kernel of the rational norm characters for every character with open kernel, given `CentralNormKernelCompactness` (proved, `centralNormKernelCompactness`) and the Props `CentralDerivedNormKernelCocompactness` and `DerivedSmoothRealAnnihilation`, which the Library reduces to further structural statements but does not prove: `norm_eq_one_on_rationalCommonNormKernel_of_structure` (`RationalSmoothCharacterModulus`, Worker 200); the existence of the constant `m` of `hcompat` (`IsQuotientCompatible`), with `m ≠ 0, ∞`, for an open subgroup `N` in place of `ker p`, `G` locally compact and second countable, Haar measures `μ` on `G` and `ν` on `G ⧸ A` and `A ∩ N` compact: `exists_isQuotientCompatible` (`QuotientMeasureCompatibility`, Worker 249); the specialization to Waldspurger's `G` (`p` the projection to `G/G^1`, `A = A_G`, his `Ξ`, `σ`, `IsUnitaryDetecting A_G`) is not made; Cor. III.7.3: none (see the row Prop. IV.2.2); orbits: `DiscreteSeriesClass`, `discreteSeriesOrbit`, their quotient topology (compact, Hausdorff) `discreteSeriesOrbitHomeomorph`, `compactSpace_discreteSeriesOrbit`, `t2Space_discreteSeriesOrbit`, finiteness of the stabilizer `finite_discreteSeriesStabilizer` (generic), `finite_rationalDiscreteSeriesStabilizer` (given the open finite-index premise `hindex`, see below); the pairing of `C(G)` with functions of tempered growth, `Space.temperedPairing` (generic) |

## Chapter IV. Intertwining operators (pp.276–287)

| Item | Page | Content | Uses | Class | Lean coverage |
|---|---|---|---|---|---|
| IV.1 | 276–278 | compact picture, rational families via `B`-families, `J_{P'\|P}(π)` by integrals over `U ∩ U' \ U'` | I.5 | Data | compact picture: restriction of normalized induction to `K` and its independence of unramified twists, `normalizedInductionCompactEquiv`, `unramifiedNormalizedInductionCompactEquiv` (actual subgroup data, with `G = P K` as a hypothesis; the Library's full-parabolic normalization, see below); and, for the positive Levi-normalized induction of I.3, `unramifiedLeviInductionCompactEquiv` (one compact picture for all unramified twists; the same compact open `K` factorizes both parabolics, and unimodularity of the conjugation moduli of the radicals is a hypothesis; `CompactIntertwiningFamilies`); the integral `∫_{(U ∩ U') \ U'} f(u' g) du'` on the subspace `StandardIntertwining.domain` of the Levi-inflated induced space where it converges weakly with a representing vector: `Langlands.Plancherel.StandardIntertwining.operator`, with `operator_right_action`, `operator_uniformly_smooth`, `operator_unipotent_mul`; its Levi transformation factor, `operator_levi_mul` (`StandardIntertwiningCovariance`); naturality in the inducing representation and the representative square on the domain, `operator_map`, `operator_domainEquiv` (`StandardIntertwiningNaturality`); target Levi covariance and the target-valued intertwiner on the domain, `targetOperator`, `targetIntertwiner`, given the explicit premise `SquaredModulusCompatibility` (`δ_U δ_{U'} = δ_{U ∩ U'}^2` on `M`, not proved for reductive groups; comparisons of its intersection character in `StandardIntertwiningModulus`) (`StandardIntertwiningTarget`); the intertwiner on the whole source when the domain is the whole source, `fullSourceIntertwiner`, and for `U' = U` the total-mass multiple of the identity, `diagonalTargetIntertwiner_eq` (`StandardIntertwiningTargetLaws`, `StandardIntertwiningMeasure`) (all generic, for a locally compact nonarchimedean `G` and semidirect decompositions with a common Levi and closed radicals; the target-valued maps also use regular Haar measures and a compatible quotient measure); rational families: the algebra generated by the evaluations `χ ↦ χ(m)` on the unramified characters of a supplied norm family, `unramifiedRegularFunctions`, and polynomial and rational vector and operator families on a parameter subset, `IsPolynomialOn`, `IsPolynomialOperatorOn`, `IsRationalOperatorOn` in the namespace `UnramifiedOperatorFamily` (`UnramifiedOperatorFamilies`, generic), closed under composition (`IsRationalOperatorOn.comp`, `CompactIntertwiningComposition`) and transported along multiplicative homeomorphisms (`unramifiedRegularFunctionsEquiv`, `UnramifiedOperatorTransport`); for the actual rational norm characters of a connected reductive group, this algebra is identified with the group algebra of the valuation image and with the Laurent polynomial functions in the finite character coordinates, `rationalCanonicalUnramifiedLaurentAlgebraEquiv` (`RationalUnramifiedCoordinateAlgebra`; Waldspurger's `B` and `b_m`); the compact-picture operator of the standard integral and its rationality predicate, `standardCompactOperator`, `StandardCompactRationalOn` (`CompactIntertwiningFamilies`); the decomposition `U' = (U ∩ U')(Ū ∩ U')` used on p.279, as a homeomorphism `U(χ)(F) ∩ U(ξ)(F) × U(χ⁻¹)(F) ∩ U(ξ)(F) ≃ U(ξ)(F)` for cocharacters `χ`, `ξ` of a smooth affine group over a nonarchimedean local field, given `ξ(t) ∈ Z(χ)(F)` and `Z(χ)(F) ∩ U(ξ)(F) = 1` (hypotheses not derived from parabolic data there): `unipotentIntersectionProduct` (`UnipotentIntersectionProduct`, from the abstract `productHomeomorph` of `OpenCellIntersectionProduct`); continuation of rational operator families (derived steps for p.277), on the unramified characters of the actual rational norm characters of a connected reductive group (with a topology for which the valuation-image projection is continuous): the extension of a supplied rational family on a region containing a nonempty open set to the nonvanishing locus of its denominator, `rationalOperatorContinuation` (`RationalUnramifiedOperatorContinuation`), its equivariance, `continuedIntertwiner` (`RationalUnramifiedIntertwiningContinuation`), and on the actual normalized induction spaces (two closed semidirect parabolics with a common Levi, unimodular radical moduli, a common compact open `K` with `G = P_i K`, continuous Levi projections, the Levi identified with rational points of a reductive group), from a supplied rationality witness and the polynomial dependence of the compact-picture action on the parameter (`unramifiedCompactRepresentation_polynomial`, `CompactInductionPolynomialAction`), `continuedInductionIntertwiner` with `continuedInductionIntertwiner_rational`, `continuedInductionIntertwiner_agrees`, `continuedInductionIntertwiner_unique` (`CompactIntertwiningContinuation`), its naturality in the representative, `continuedInductionIntertwiner_natural` (`ContinuedIntertwiningNaturality`), base change of the compact operators, `compactIntertwiningOperator_baseChange` (`CompactIntertwiningBaseChange`), and translation of the parameter, `isRationalOperatorOn_translation_iff` (`UnramifiedOperatorTranslation`); the universal `B`-family construction of IV.1 (the smooth `B`-linear normalized models of the row I.5 are available, with flatness and finite projective compact-open invariants for admissible `π`, see the row I.5): none |
| Thm IV.1.1 | 278 | convergence in a cone and rationality of `J_{P'\|P}(π ⊗ χ)` | II.3.4, II.4.2, I.4.4, I.3 | Book | the conditional Prop `ConditionalParabolicIntertwiningStatement` (statement only, `ParabolicIntertwiningStatement`: for actual rational points of a connected reductive group with compatible `ParabolicRootPresentation`s sharing a Levi and the further structural premises listed there, and admissible `π` of finite length, it asserts unimodularity of the radicals, `SquaredModulusCompatibility`, a nonempty open threshold region on whose orbit saturation the domain is the whole source, rationality `StandardCompactRationalOn` there, and the representative square); parameter regions: `rootThresholdRegion`, `intertwiningRegion`, `rootThresholdRegion_nonempty_of_positivePairing` (`IntertwiningCone`), their realization by unramified characters, `canonicalUnramifiedIntertwiningRegion_nonempty_iff` (`CharacterIntertwiningCone`), the form induced from one ambient Weyl-invariant form, `weylInducedCharacterForm`, and its regions (`AmbientCharacterForm`, `AmbientCharacterFormNaturality`, `AmbientCharacterIntertwiningCone`, `SubtorusIntertwiningCone`), and the regions for actual parabolic data, `parabolicUnramifiedIntertwiningRegion`, `parabolicPointUnramifiedIntertwiningRegion` (`ParabolicIntertwiningRegion`, `ParabolicPointIntertwiningRegion`); supporting results for that statement: its elementary prerequisites (unimodularity of a supplied radical, full-domain transport and representative naturality), `parabolicIntertwiningElementaryStatement` proving `ParabolicIntertwiningElementaryStatement` (`ParabolicIntertwiningElementaryProof`, with `parabolicRadical_isUnimodular` in `ParabolicRadicalUnimodularity` and `domain_eq_top_iff_equiv` in `StandardIntertwiningFullDomainTransport`), openness of the orbit-saturated regions, `isOpen_unramifiedTwistOrbitRegion` (`ParabolicIntertwiningTopology`), and algebra for the rational continuation, `universalUnramifiedRepresentation` (`UnramifiedUniversalTwist`), `unramifiedTensorMapLift` (`UnramifiedTensorMaps`), `polynomialRangeMap` (`PolynomialIsolation`); reductions of the convergence of the actual standard integral: its scalar domain `StandardIntertwining.scalarDomain` contains the weak-integral domain, `StandardIntertwining.domain_le_scalarDomain` (`StandardIntertwiningScalarDomain`), and is the whole source when an explicit Iwasawa weight is integrable, `StandardIntertwining.scalarDomain_eq_top_of_integrable_iwasawaWeight` (`StandardIntertwiningScalarBounds`), with one growth exponent for all open-kernel character twists, `StandardIntertwining.exists_exponent_scalarDomain_eq_top_twist` (`StandardIntertwiningTwistBounds`), and continuity in the unramified parameter of the compact scalar integral under a supplied domination, `continuousAt_unramifiedCompactScalarIntegral_of_dominated` (`CompactIntertwiningParameterContinuity`); for the rational continuation, the algebra of unramified regular functions of actual rational points (see I.5) and the Prop `RationalUnramifiedLocalHypersurfaceDivisibilityStatement`, proved by `rationalUnramifiedLocalHypersurfaceDivisibility` (`RationalUnramifiedLocalDivisibilityProof`, Worker 1664), with the denominator cancellations that use it, `rationalUnramified_isRationalOperatorOn_of_weak_continuity` (`RationalUnramifiedScalarCancellation`, `RationalUnramifiedVectorCancellation`); rationality on the compact picture from analytic inputs: `StandardCompactRationalOn` from a local integrable domination, a common nonzero regular numerator and the divisibility Prop, `parabolicLevi_standardCompactRationalOn_of_dominated` (`CompactIntertwiningWeakRegularity`), such a numerator, `exists_uniform_standardCompactOperator_numerator` (`CompactIntertwiningUniformNumerator`, with `regularTranslateSpan_eq_top` in `CompactInductionGeneration`, `exists_regular_compactIdentityValue_numerator` in `CompactIntertwiningCompression`, the truncations `truncatedIntegral` in `StandardIntertwiningTruncation` and the stable-limit principle `eval_one_smul_eq_aeval_of_stableLimit` in `UnramifiedStableLimit`), its form for actual rational-point parabolics and `π` of finite length, `parabolicLevi_standardCompactRationalOn_of_dominated_of_finiteLength` (`ParabolicPointUniformNumerator`), and the conjuncts of the conclusion of `ConditionalParabolicIntertwiningStatement` from convergence on a region and local domination on its orbit saturation, `parabolicLevi_intertwiningConclusion_of_dominated` with the predicate `ParabolicLeviAnalyticInputs` (`ParabolicIntertwiningAssembly`); the convergence and the local domination, and with them `ConditionalParabolicIntertwiningStatement`, from three unproved Props: `conditionalParabolicIntertwiningStatement_of_statements` (`ParabolicCharacterDecayProof`) derives it from `RationalCoefficientModerateGrowthStatement` (Cor. I.4.4), `RelativeRootSystemStatement` and `CentralSplitTorusCharacterStatement`; the steps: the inputs Prop `ConditionalParabolicIntertwiningInputs` and `conditionalParabolicIntertwiningStatement_of_inputs` (`ParabolicIntertwiningReduction`, Worker 1615, with `compactIntegralLocallyDominatedOn_saturation` in `CompactIntegralSaturation`); the assembly from `RationalFiniteLengthModerateGrowthStatement` and the Props `ParabolicSquaredModulusInput`, `ParabolicCharacterDecayInput`, `conditionalParabolicIntertwiningStatement_of_characterDecay` (`ParabolicIntertwiningDecayAssembly`); the squared-modulus compatibility from the two structural Props, `parabolic_squaredModulusCompatibility_of_structural` (`ParabolicSquaredModulusReduction`); convergence and domination from a decay predicate, `IsLocallyUniformQuotientDecayOn`, `scalarDomain_twist_eq_top_of_quotientDecay`, `compactIntegralLocallyDominatedOn_of_quotientDecay` (`CompactIntertwiningQuotientDecay`), `ParabolicOppositeConeDecay`, `exists_region_convergence_domination_of_coneDecay` (`ParabolicIntertwiningConeReduction`), `ParabolicOppositeCharacterDecay`, `parabolicOppositeConeDecay_of_characterDecay` (`ParabolicIntertwiningCharacterDecay`), with the opposite chart of `(U ∩ U') \ U'` and integrability of negative powers of the height there, `quotientChart`, `exists_integrable_quotientChart_symm_rationalMatrixNorm` (`ParabolicOppositeQuotient`), and a common coefficient growth exponent on the Levi, `parabolicLevi_exists_coefficientGrowth` (`ParabolicLeviModerateGrowth`); the character decay itself from the two structural Props, `parabolicOppositeCharacterDecay_of_statements` (`ParabolicCharacterDecayProof`), through logarithm vectors along a split component, `exists_splitComponentLogarithm` (`SplitComponentLogarithm`), the Levi bounds of `ParabolicLeviLogarithmBounds`, the conic decay from the relative roots, `exists_parabolicRootCone_decay` (`ParabolicRootCone`), the root inclusions of `OppositeIntersectionRootInclusions` and the convex lemmas `exists_pos_rootCone_decay` (`Langlands/LinearAlgebra/RootFaceCone`), `exists_int_sign_realization` (`RootFaceReflection`); Waldspurger's gallery induction is not followed |
| IV.1 (10)–(14) | 283–284 | uniform convergence, nonvanishing, adjoint, composition, transitivity | IV.1.1 | Book | (12) as a formal identity of the integrals, for supplied ordered quotient coordinates with measure-preserving charts and absolute convergence of the product integral: `HasIntegral.comp_ordered`, `operator_eq_comp_ordered`, `fullSourceIntertwiner_comp_ordered` (`StandardIntertwiningComposition`); the coordinates and their exact measure normalization from literal ordered product homeomorphisms of the radicals, `OrderedSubgroupFactorization`, `quotientCoordinates` (`StandardIntertwiningFactorization`), and from compact-open mass identities (`StandardIntertwiningIntersectionFactorization`, `StandardIntertwiningIntersectionNormalization`, `StandardIntertwiningFirstFactorMass`, `StandardIntertwiningLocallyNormalizedComposition`, `StandardIntertwiningCompactOpenComposition`, `StandardIntertwiningFactorChoice`, `StandardIntertwiningFactorRegularity`; for second countable `G`, `comp_hasIntegral_of_secondCountable` in `StandardIntertwiningCountableComposition`) (generic); the same at the common source scale of I.1 (one compact open subgroup normalizing all intrinsic Haar measures): `comp_hasIntegral_at_sourceScale` (`StandardIntertwiningSourceComposition`, with `StandardIntertwiningSourceFactors`, `StandardIntertwiningSourceQuotients`), `comp_hasIntegral_at_sourceScale_of_covers` (`StandardIntertwiningCoveredSourceComposition`) and, for actual dynamic radicals, `comp_hasIntegral` (`StandardIntertwiningDynamicSource`); the factorizations for actual reductive radicals, the distance condition of (12), convergence and the rational identity: none; (10), (11), (13), (14): none |
| Cor. IV.1.2 | 284 | pole order at 0; for square integrable `π`, `J` regular unless `P̄` conjugate to `P` | IV.1.1 | Book | none |
| Prop. IV.2.1 | 284 | tempered: convergence for `⟨Re χ, α^∨⟩ > 0` | II.4.3 | Book | none |
| Prop. IV.2.2 | 284 | `ω` square integrable and `G`-regular: `I_P^G ω` irreducible, `J` regular and invertible | III.7.3, IV.1 | Book | a weaker consequence, stated only: for an irreducible square-integrable representation of the Levi of an actual rational parabolic of a connected reductive group (with explicit structural premises), a nonempty open set of unramified parameters at which the normalized induction is irreducible, the unproved Prop `ConditionalParabolicGenericIrreducibilityStatement` (`ParabolicGenericIrreducibilityStatement`, adapted from IV.2.2 (i) and the beginning of IV.3; the `G`-regular case and the regularity and invertibility of `J` are not stated); a finite-dimensional openness step, the Prop `FiniteMatrixIrreducibilityOpennessStatement` (`FiniteMatrixOpennessStatement`), proved by `finiteMatrixIrreducibilityOpenness` (`FiniteMatrixOpennessProof`); the scalar-endomorphism step of the proof of (i) as a criterion (`Langlands/Representation/Aubert/General/JacquetMultiplicityIrreducibility`, generic semidirect `P = M U` with a closed unimodular radical): a nonzero semisimple normalized induction whose normalized Jacquet Hom space into the inducing representation has rank at most one is irreducible, `isIrreducible_induction_of_semisimple_jacquetHom_rank_le_one` (nonzeroness of the induction is a hypothesis), and the variant `isIrreducible_induction_of_unitary_jacquetHom_rank_le_one` for a nonzero inducing representation with continuous Levi projection, compact open subgroups cofinal in `G`, and admissible unitarizable induction (semisimplicity then follows), with the same rank bound; IV.2.2 itself: none |
| IV.3 (1)–(6) | 285–287 | `j(π)`: `J_{P\|P̄} J_{P̄\|P} = j(π)`, independence of `P`, symmetries, product formula, `j ≠ 0` for square integrable | IV.1, IV.2.2, [S] (avoided for square integrable `π`) | Book | derived steps toward the scalar `j(π)`, for supplied intertwiner families (their identification with the standard integrals `J_{P\|P̄}`, `J_{P̄\|P}` is not made): the extracted scalar of a rational endomorphism family that is scalar on a nonempty open set, and its continuation, `rationalUnramifiedScalarContinuation` (`RationalUnramifiedScalarContinuation`), as an element of the function field of the unramified characters, `rationalUnramifiedOperatorScalar` (`RationalUnramifiedScalarField`), and its translation, `rationalUnramifiedOperatorScalar_translation` (`UnramifiedScalarTranslation`); on the actual normalized induction spaces, the scalar of the composite of two intertwiners at an irreducible parameter, `compactIntertwiningCompositionScalar`, `compactIntertwiningComposition_eq_extracted_scalar` (`CompactIntertwiningScalar`), and for two continued intertwiners, given irreducibility of the induced representation on a nonempty open set, a rational scalar `a/b` with `J₀₁ J₁₀ = (a(χ)/b(χ)) · id`, `continuedInductionComposite_eq_scalar`, `continuedInductionCompositeRationalScalar_spec` (`ContinuedIntertwiningScalar`), independent of the representative, `continuedInductionCompositeRationalScalar_representative_independent` (`ContinuedIntertwiningScalarNaturality`); `j(π)` and (1)–(6): none |

## Chapter V. Weak constant terms of induced coefficients (pp.287–295)

| Item | Page | Content | Uses | Class | Lean coverage |
|---|---|---|---|---|---|
| V.1 | 287–289 | `L(ω,P)`, `E_P^G`, `W(M'\|G\|M)`, `c_{P'\|P}(s,ω)` | III.7, IV | Data | the tensor model of `L(ω,P)` and its coefficient map `ℓ(π(g)v)`: `CoefficientTensor`, `coefficientTensorMap`, `range_coefficientTensorMap`, `NormalizedCoefficientTensor`, `normalizedCoefficientMap`, `normalizedInductionDualTensorEquiv`; product induction `I_P^G(A) ⊠ I_Q^H(B) ≅ I_{P×Q}^{G×H}(A ⊠ B)`: `normalizedProductInductionTensorEquiv`; `L(ω,P) = I_{P×P}^{G×G}(E ⊗ Ě)` and `E_P^G` on it: `productInducedCoefficientObject`, `productInducedCoefficientMap`, with the integral formula `productInducedCoefficientMap_integral` and image `range_productInducedCoefficientMap` (actual subgroup data with explicit hypotheses, the Library's full-parabolic normalization; in the Levi-inflated normalization of I.3: `leviProductInducedCoefficientMap`; see below); `W(M'\|G\|M)` and `c_{P'\|P}(s,ω)`: none |
| Prop. V.1.1 | 289 | weak constant terms of `E_P^G ψ` | III.3.3, III.4.1, IV.2.2, III.5.1, IV.1, IV.3 | Book | none |
| V.2, Lemme V.2.1 | 292–293 | `μ(ω) = j(ω)^{-1} ∏ γ(M_α\|M)^2`: rational, regular, `≥ 0`, product formula, Weyl invariant; the hermitian product `(v₁ ⊗ v̌₁, v₂ ⊗ v̌₂) = d(ω)^{-1} (v₁, v₂)(v̌₁, v̌₂)` on `L(ω,P)` (p.293) | IV.3, III.1 (3) | Data, Book | the hermitian product (generic, for actual subgroup data `P = M U` of a unimodular `G` with the modulus of `P` given by its action on `U`, and `ω` irreducible and square integrable modulo a normal central subgroup `C` of `M` with a Haar measure on `M ⧸ C`): `formalDegreeInducedTensorForm` on `I_P^G(E) ⊗ I_P^G(Ě)`, its product formula for every invariant positive form on `E`, `formalDegreeInducedTensorForm_inner_tmul`, and the independence of that form, `normalizedInducedDualTensorForm_independent` (`FormalDegreeInducedTensorForm`; through `InducedTensorForm`, `InvariantPositiveForm.tensorProduct` in `PositiveFormTensor` and `InvariantPositiveForm.exists_pos_rescale_eq` in `AdmissibleFormUniqueness`); the same form on the compact pictures and on `productInducedCoefficientObject`: `tensorForm`, `formalDegreeTensorForm` (`CompactInducedTensorForm`), `formalDegreeProductForm`, `formalDegreeProductForm_eq_coefficientForm` (`CompactProductInducedForm`), its integral expansion `productForm_inner_integral` (`CompactProductIntegralFormula`), the Hermitian form of the integral duality of normalized induction, `integralDualEquiv_form` (`CompactInducedDualIsometry`), and transport of the coefficient-tensor form along equivalences, `coefficientTensorInvariantForm_ofEquiv` (`CoefficientTensorFormTransport`); the induced forms integrate over the Library's quotient measures or over Haar probability on a compact open subgroup, whose comparison with Waldspurger's normalization is not made there; `μ(ω)` and Lemma V.2.1: none |
| Lemme V.2.2, Cor. V.2.3 | 293–294 | norm identity for `c_{P'\|P}(s,ω)`; regularity of `μ^G μ^{M'}(sω)^{-1} c` | V.1.1, V.2.1 | Book | none |
| V.3, Lemmes V.3.1, V.3.2 | 295 | normalized `°c_{P'\|P}(s,ω)`: regular, unitary, `E_{P'}^G(°c ψ) = E_P^G ψ`, cocycle | V.2 | Data, Book | none |

## Chapter VI. Wave packets (pp.295–313)

| Item | Page | Content | Uses | Class | Lean coverage |
|---|---|---|---|---|---|
| VI.1 | 295–296 | identifications of `L(ω,P)` along an orbit; `C^∞(O,P) = [C^∞(Im X(M)) ⊗ L_K(ω,P)]^{Stab}` | V.1 | Data | transport of coefficient tensors along equivalences, independent of the choice: `normalizedCoefficientTransport`, `normalizedCoefficientTransport_independent`; scalar smooth functions on an orbit: `IsSmoothRationalOrbitFunction`, `rationalSmoothOrbitFunctions`, `isSmoothRationalOrbitFunction_basis_iff`; transport between the spaces `L(ω,P)` of equivalent representatives, independent of the equivalence for irreducible admissible `ω`: `productInducedCoefficientTransport`; the fixed compact picture `productInducedCompactEquiv` and the action of the stabilizer on it by self-twists `unramifiedStabilizerCompactRepresentation`; the coefficient-valued `C^∞(O,P)` as coherent smooth sections over the unitary unramified twist orbit of a fixed irreducible admissible `ω`, and its identification with the stabilizer-invariant tensors: `productInducedSmoothOrbitSections`, `productInducedSmoothTensorOrbitEquiv` (with supplied torus coordinates, `G = P K` as a hypothesis, the stabilizer `unitaryClassTwistStabilizer` of `ω` in the unitary unramified characters, and the Library's full-parabolic normalization; see below); independence of the base representative, `productInducedSmoothOrbitBaseEquiv`; the comparison with the discrete-series orbit and the full unramified stabilizer, `unitaryOrbitRepresentativeDiscreteSeriesOrbit`, `productInducedFullStabilizerTensorOrbitEquiv` (given finiteness of the relevant central quotient, see below); Hermitian compatibility: the fixed compact picture preserves the product forms, `productInducedCompactIsometry` (`FixedCompactProductForm`), also after the inverse-degree normalization, `formalDegreeProductCompactIsometry` (`FormalDegreeFixedCompactForm`); unitary twists preserve the coefficient-tensor form, `productCompactTwistTensorIsometry` (`ProductCompactTwistForm`); transport between representatives preserves the normalized form, `formalDegreeProductTransport` (`CompactProductFormTransport`); positive integral pairings of smooth families, `finiteSmoothFamilyCore` (`FiniteSmoothFamilyForm`, finite families on `J → Circle`) and `productInducedSmoothFamilyCore` (`ProductInducedSmoothFamilyForm`, on the unitary parameter cover); the action of `G × G` on `C^∞(O,P)` used in the proof of VI.4.1, with an invariant positive form, `productInducedSmoothOrbitRepresentation`, `productInducedSmoothOrbitForm` (`ProductInducedOrbitFullAction`), the action of the compact open `K × K`, `productInducedSmoothOrbitCompactRepresentation`, `productInducedSmoothOrbitCompactForm` (`ProductInducedOrbitCompactAction`), and their compatibility with a change of base point, `productInducedSmoothOrbitBaseIso`, `productInducedSmoothOrbitBaseIsometry` (`ProductInducedOrbitBaseAction`), and of lattice coordinates, `productInducedSmoothOrbitRebaseIso`, `productInducedSmoothOrbitRebaseIsometry` (`ProductInducedOrbitCoordinateAction`, `ProductInducedOrbitFormCoordinates`) (Worker 200); torus coordinates in which the characters are Laurent monomials, `HasLaurentUnitaryCoordinates`, with the smooth evaluation family `unitaryUnramifiedSmoothEvaluation` and the canonical rational coordinates `rationalCanonicalUnitaryUnramifiedCharacterCoordinates_hasLaurent` (`UnitaryUnramifiedSmoothEvaluation`), and the canonical lattice exponent of such coordinates, `laurentExponent`, with `torusCharacter_laurentExponent` and its homomorphism, kernel and local constancy properties (`LaurentExponent`, Worker 249; for the canonical rational coordinates `laurentExponent_rationalCanonical`); the detection of finite smooth families by evaluation, `mem_finiteSmoothFamilies_of_common_open_stabilizer` (`FiniteSmoothCompactEvaluation`) |
| Lemmes VI.2.1–VI.2.3 | 296–301 | smoothness in `ω`; `\|E_P^G ψ_ω(g)\| ≤ C Ξ(g)`; exponential decay of the `+` part on `D_{M'}(δ)` | I.5, I.4.3, III.1.2, II.1.6, II.1.1, III.2.2 | Book | Lemma VI.2.2 for one `ω`, generic: `norm_coefficientMap_le_xi` (`InducedCoefficientXi`, Worker 249) for the coefficients `CompactInduction.coefficientMap` of normalized induction on Worker 200's product-induced coefficient space (`CompactProductInducedCoefficients`), from the analytic core `LeviData.norm_compactIntegral_le_xi` (`InducedCoefficientBound`), the integrand bound `integrand_bound_levi` (`CompactProductCoefficientBounds`) and the Haar comparison `CompactInduction.measure_eq_normalizedHaar` (`CompactCoefficientHaarComparison`); the conclusion of Cor. III.1.2 for `M`, `G = P K`, the unimodularity of `G` and `U`, the modulus of `P` and the Iwasawa pairs are hypotheses; uniformly over the unitary unramified twists of one `ω`, for the twisted sections `twistedSection` of a fixed compact section, `norm_twist_coefficientMap_le_xi`, and for smooth families on a finite torus `(S¹)^J`, `norm_family_coefficientMap_le_xi` (`InducedCoefficientTwistXi`, Worker 249, the same hypotheses); the coefficient `ω ↦ E_P^G ψ_ω` of a section `ψ ∈ C^∞(O,P)` on the discrete-series orbit, `unitaryOrbitCoefficientMap`, and at representatives, `unitaryOrbitRepresentativeCoefficientMap`, with transport, equivariance and bi-invariance (`ProductInducedOrbitCoefficients`, Worker 200); Lemma VI.2.1 (i) for such sections, smoothness in torus coordinates and continuity on the orbit, `isSmoothFiniteTorusFunction_unitaryOrbitCoefficient`, `continuous_unitaryOrbitCoefficient` (`ProductInducedOrbitCoefficientSmoothness`, Worker 200, given `HasLaurentUnitaryCoordinates` and continuous coordinates); Lemma VI.2.2 for `ψ ∈ C^∞(O,P)`, uniformly over `O` and over all representatives, `exists_norm_unitaryOrbitCoefficientMap_le_xi`, `exists_norm_unitaryOrbitRepresentativeCoefficientMap_le_xi` (`OrbitWavePacket`, Worker 249, the hypotheses of `norm_family_coefficientMap_le_xi`); Lemma VI.2.3 in abstract form (generic, Worker 249): for a group with an additive `H` (for `H_0` on `M_0`), finite sets of linear forms for `Δ_0^{M'}` and `Δ_0 − Δ_0^{M'}`, `a` with `⟨β, H(a)⟩ = 0`, resp. `> 0`, and a family `F_i` annihilated by `p_i(ρ(a))` (monic, fixed degree, roots of modulus `≤ θ < 1`), bounded by `C_1 B (1 + σ)^d` on the shifted chamber (estimate (1)) and by `C_0 B` on the bounded part of `D(δ)`: `‖F_i(g)‖ ≤ C B(g) e^{−ε‖H(g)‖}` on `D(δ)`, `exists_norm_le_exp_of_aeval_eq_zero`, with estimate (2), `norm_le_of_aeval_eq_zero`, and the replacement of `a` by a power, `rootPowerPolynomial` (`PositivePartDecay`); the split of the constant term into weak and positive parts for one vector, `exists_weak_positive_decomposition` (`ExponentDecomposition`); the bound of the weak part, `Ξ^{M'}`, `σ`, the bound on the constant term, the region data and the identification with `E^G_P ψ_ω`: hypotheses or none; Lemma VI.2.1 (ii) (regularity in `χ`): none |
| VI.3 | 301–302 | topology on `C^∞(O,P)`; measure on `O`; wave packet `f_ψ(g) = ∫_O μ(ω) (E_P^G ψ_ω)(g) dω` | VI.1 | Data | measure on `O` locally preserved by the character parametrization: `discreteSeriesOrbitMeasure` (generic), `rationalNormalizedDiscreteSeriesOrbitMeasure`; integration over `O`: `rationalDiscreteSeriesOrbitIntegral` (the last two given the open finite-index premise `hindex`, see below); the pairing of two coherent sections over the orbit with the inverse-degree form, its continuity and its integral, `unitaryOrbitProductPairing`, `continuous_unitaryOrbitProductPairing`, `integral_unitaryOrbitProductPairing_eq_parameterIntegral`, `productInducedSmoothOrbitCore` (`ProductInducedOrbitForm`), independent of the base point (`ProductInducedOrbitFormBaseChange`); the wave packet for `M = G` on actual rational points, with `μ = 1` and sections given by coefficient tensors of chosen representatives, `rationalOrbitWavePacket` (`RationalOrbitWavePacketPairing`, Worker 249); for general `P = M U` on `C^∞(O,P)`, with a weight `w : O → ℂ` in place of `μ` (V.2 is not formalized), the orbit measure `discreteSeriesOrbitMeasure` of a measure `ρ` on the unitary unramified characters and a finite stabilizer `S` of the class of the base representative, all of them, like `unitaryOrbitCoefficientMap`, with `G = P K`, the unimodularity of `G` and the modulus of `P` as hypotheses (`OrbitWavePacket`, Worker 249): the integral `f_ψ` itself, `inducedOrbitWavePacket`, for arbitrary `w` and `ρ`, and its bi-invariance under one compact open subgroup, `exists_inducedOrbitWavePacket_biInvariant`, in the same generality; the bound by `c Ξ`, `exists_norm_inducedOrbitWavePacket_le_xi`, only for a finite measure `ρ` and a bounded weight `w`, with the hypotheses of `exists_norm_unitaryOrbitCoefficientMap_le_xi` in the row Lemmes VI.2.1–VI.2.3 (Cor. III.1.2 for `M`, unimodularity of `U`, the Levi data and the Iwasawa pairs); the linear map `ψ ↦ f_ψ`, `inducedOrbitWavePacketLinear` (through `integrable_inducedOrbitWavePacket_integrand` and `inducedOrbitWavePacket_add`), only for a finite measure `ρ`, a bounded almost everywhere strongly measurable weight `w`, continuous torus coordinates `e` in which the characters are Laurent monomials (`HasLaurentUnitaryCoordinates`) and the same coefficient and Iwasawa hypotheses; the expression of `f_ψ(g)` as the inverse of the order of `S` times the integral over `ρ` of `w(ω ⊗ χ) (E_P^G ψ_{ω ⊗ χ})(g)`, `inducedOrbitWavePacket_eq_parameterIntegral`, for continuous Laurent torus coordinates and an almost everywhere strongly measurable weight, with no finiteness condition on `ρ`; the topology on `C^∞(O,P)` (`OrbitSectionTopology`, Worker 249): the levels `C^∞(O,P)^{H×H}`, `OrbitSectionLevel`, with the topology of the seminorms `q ↦ sup_z \|∂_l(ℓ ∘ R q)(z)\|` (`R` the compact restriction to the coordinate torus, `l` a list of coordinate directions, `ℓ` a linear functional on the compact picture), `orbitSectionSeminorm`, and `C^∞(O,P)` itself, `OrbitSectionSpace`, with the locally convex inductive-limit topology over the open subgroups `H ≤ K` (the convention of III.6 for `C(G)`), Hausdorff, with the criterion `OrbitSectionSpace.mkCLM` for continuous linear maps out of it; the agreement of the level topology with the source's product topology on `C^∞(Im X(M)) ⊗ L_K(ω,P)^{H×H}` (which needs `dim L_K(ω,P)^{H×H} < ∞` and commuting derivatives) is not proved |
| Prop. VI.3.1 | 302 | `f_ψ ∈ C(G)`, `ψ ↦ f_ψ` continuous | I.1 (4), I.4.3, I.5, VI.2, V.1.1, V.2.3, II.1.1 | Book | estimate (4) of the proof (p.303), in coordinates on a finite torus `(S¹)^J` with the sup norms of iterated partial derivatives in place of `ν^G(D, ·)`: `norm_torusFourierCoeff_le_rpow` (`TorusFourierDecay`, Worker 249, with `torusFourierCoeff` and `torusPartialDeriv`); the first bound of the proof, through the average over the torus of twists, in the same coordinates: `torusAverage`, `integral_mul_eq_integral_torusAverage_mul`, `norm_integral_mul_le_rpow` (`TorusFourierAveraging`, Worker 249); the bound `\|f_ψ\| ≤ c Ξ` without the factor `(1 + σ)^{-r}`, for the wave packet of the row VI.3 with a finite measure `ρ`, a bounded weight `w` and the coefficient and Iwasawa hypotheses listed there: `exists_norm_inducedOrbitWavePacket_le_xi` (`OrbitWavePacket`); the first bound of the proof with its factor, `\|f_ψ(g)\| ≤ c Ξ(g) (1 + \|n_G(g)\|)^{-r}`, for a weight `w` smooth in the torus coordinates in place of `μ ϕ`, a constant `c` depending on all the data (continuity in `ϕ` is not stated), a homomorphism `n_G : G → ℤ^L` trivial on `K` and `U` in place of `H_G`, with `χ(m) = z^{n_G(m)}` through an integer matrix as a hypothesis, a finite left-invariant `ρ` and the hypotheses of Lemma VI.2.2 listed in the row VI.3: `exists_norm_inducedOrbitWavePacket_le_xi_rpow` (`OrbitWavePacketDecay`, Worker 249, with the monomial substitution lemmas of `Langlands/HarmonicAnalysis/TorusMonomialDerivative`); the full Schwartz-seminorm estimate of the proof, for every `r` a finite set `D` of constant-coefficient differential operators on `Im X(M)` with `ν_r(f_{ϕ,ψ}) ≤ ν^M(D, ϕ)` for all `ϕ` (`ψ` fixed; derivatives on the parameter function `ϕ`, not on `f_ψ`), including the bounds of `n(ϕ)`, `n^w(ϕ)`, `n^+(ϕ)` (pp.303–305) for the weak and positive constant-term contributions, `f_ψ ∈ C(G)` and the continuity of `ψ ↦ f_ψ`: none |
| VI.3 | 305–306 | `Θ`, `C^∞(Θ)`, `κ̃`; invariant subspace `C^∞(Θ)_inv`; `κ`; projector | V.3 | Data | none |
| Lemme VI.3.2 | 306 | `κ̃` factors through the projector | V.3.1 | Book | none |
| Prop. VI.4.1 | 306–313 | constant terms `f_ψ^{(P'),Ind}`: zero for smaller non-conjugate Levis; explicit for `M' = M` | VI.2, V.1.1, V.2.3, III.1.2, II.3.4, II.4.3, IV.2.1 | Book | none |

## Chapter VII. Fourier transform and isometry (pp.313–320)

| Item | Page | Content | Uses | Class | Lean coverage |
|---|---|---|---|---|---|
| VII.1 | 313–314 | `f̂(ω,P) = d(ω) π(f̌)` in `L(ω,P)`; `θ^G_ω`; `(f_1,f_2)_X = ∫ conj(f_1) f_2` | III.7 | Data | `f̌` and `(f_1,f_2)_G` on `C(G)`: `L2` (generic); in `FourierTransform` (generic, Worker 249), for an arbitrary smooth representation `A` in place of `I_P^G ω`: the embedding (1) `A ⊗ Ã ↪ End(A)`, `coefficientTensorToEnd`, `coefficientTensorToEnd_injective`; for an admissible smooth representation `A` (`hA`) with tempered coefficients (`hT`) and an arbitrary real `d` in place of `d(ω)`, on a topological group with a compact open subgroup, with a left and right invariant measure `μ` (`OpensMeasurableSpace`, `MeasurableMul`), `L2Weights μ Ξ σ` and weights invariant under inversion (`hΞ`, `hσ`): the transform `f ↦ d π(f̌)`, `schwartzActionTensor`, `coefficientFourierTransform`; `θ^G_ω` as the trace `schwartzCharacter` of `π(f)` (`SchwartzAction`); for `π = I_P^G ω` on Worker 200's `L(ω,P)` (`productInducedCoefficientObject`) with `d = d(ω)` (`representationFormalDegree`): `inducedFourierTransform` (`InducedFourierTransform`, Worker 249), identified with `d(ω) π(f̌)` by `coefficientTensorEquiv_inducedFourierTransform`; `ψ_f[O,P]` (p.316) as a section over the unitary unramified orbit, `fourierOrbitSection`, coherent along equivalences, `fourierOrbitSection_mem_coherent`, `productInducedCoefficientTransport_inducedFourierTransform` (`InducedFourierCoherence`, Worker 249) |
| Lemme VII.1.1 | 314 | equivariance; `(E_P^G ψ, f)_G = (ψ, f̂(ω,P))`; `E_P^G(f̂(ω,P))(g) = d(ω) θ^G_ω(λ(g) f̌)` | III.7 | Book | for the abstract data of the row VII.1, with `A` admissible with tempered coefficients and the analytic hypotheses listed there (generic, `FourierTransform`, Worker 249): (i) `coefficientFourierTransform_translate` (also with translation-compatible weights `ht`); (ii) `integral_conj_coefficientTensorMap_mul_eq_inner`, for the form `d⁻¹ b(v₁, v₂)(ℓ₁, ℓ₂)` built from a positive invariant form `b` on `A`, `0 < d` and an inversion-invariant measure; (iii) `coefficientTensorMap_coefficientFourierTransform` (also with `ht`); for `L(ω,P)` with the product of V.2 (`CompactInduction.formalDegreeProductForm`): (i) `inducedFourierTransform_translate`, (ii) `integral_conj_coefficientMap_mul_eq_inner`, (iii) `coefficientMap_inducedFourierTransform`, uniqueness `inducedFourierTransform_eq_of_forall_integral`, and the tempered coefficients of `I_P^G ω` from Lemma VI.2.2, `hasTemperedCoefficients_normalizedInduction` (`InducedFourierTransform`, Worker 249; for general `Ξ` the temperedness `hT` is a hypothesis) |
| Lemme VII.1.2 | 315 | `f̂(ω,P) = f̂^{(P),Ind}(ω)`, where `f̂^{(P),Ind}(ω)(g_1,g_2) = [f^{(P),Ind}(g_1,g_2)]^(ω,M)` is the Fourier transform of VII.1 for `M`, applied pointwise to the induced constant term `f^{(P),Ind} : G × G → C(M)` of III.6 | III.6, VI.2.2, II.1.5, VII.1.1 | Book | `inducedFourierTransform_eq_constantTermInducedFourierTransform` and its pointwise form `eval_inducedFourierTransform` (`InducedConstantTermFourier`, Worker 249), for `f̂^{(P),Ind}(ω) = constantTermInducedFourierTransform` built from `Space.constantTermInd`, with the integral over `P\G` taken over `K`; hypotheses: `U` unimodular, `IsConjModulus`, `ConstantTermData`, `ConstantTermEstimate` (II.4.5), `TranslationWeights`, tempered coefficients on `M`, `mes(K) = mes(M ∩ K) = mes(U ∩ K) = 1`, `P ∩ K = (M ∩ K)(U ∩ K)` and the absolute convergence `hint`; the Bochner form of I.1 (2) used there, `integral_eq_integral_compact_levi_unipotent`; the absolute convergence for `Ξ = xi` from Lemmas VI.2.2, II.1.6, II.1.5, `integrable_coefficientPairingIntegrand` (`InducedCoefficientConvergence`, Worker 249), and the lemma for `Ξ = xi` without `hint`, `inducedFourierTransform_eq_constantTermInducedFourierTransform_xi` (`InducedConstantTermFourierXi`, Worker 249) |
| Prop. VII.1.3 | 316 | `ψ_f[O,P] ∈ C^∞(O,P)`, continuous in `f` | VII.1.2, III.6, III.1.2, II.1.5 | Book | the core for `M = G` in lattice coordinates (generic, Worker 249): with `Im X(G)` replaced by a finite torus `J → Circle` and `χ(g)` by `torusCharacter (n g)` for a supplied measurable lattice map `n` with `‖n(g)‖ ≤ C (1 + σ(g))`, and with `L2Weights μ Ξ σ`, the twisted coefficients `χ ↦ ∫ f φ χ` of `f ∈ C(G)` against a continuous `φ` with `ν_{-r}(φ) < ∞` (in place of the coefficient `⟨ω(g)v, v̌⟩`) are smooth and satisfy the estimate (2) of the proof: `twistedCoefficientFamily`, `torusPartialDerivList_twistedCoefficientFamily`, `L2Weights.lintegral_enorm_pow_mul_le` (`TwistedCoefficientSmoothness`, with `torusSynthesis`, `isSmoothFiniteTorusFunction_torusSynthesis` and `norm_torusPartialDerivList_torusSynthesis_le` in `TorusFourierSynthesis`); the same core on actual rational points of a connected reductive group, with `n` the valuation coordinates `rationalValuationCoordinates`: `isSmoothFiniteTorusFunction_rationalTwistedCoefficient`, `norm_torusPartialDerivList_rationalTwistedCoefficient_le` (`RationalTwistedCoefficientSmoothness`); the case `M = G` as tensors: `Space.twist`, `schwartzActionTensor_eq_sum`, `schwartzActionTensor_twist_mem_finiteSmoothFamilies` (`TwistedFourierFamily`, Worker 249), `twistTensorEquiv`, `twistTensorEquiv_schwartzActionTensor`, `twistTensorEquiv_coefficientFourierTransform_mem_finiteSmoothFamilies` (`TwistedFourierIdentification`, Worker 249); general `M`, first assertion: `fourierOrbitSection_mem_smooth`, `fourierOrbitSmoothSectionLinear` (`FourierOrbitSmoothness`, Worker 249): `ψ_f[O,P]` lies in Worker 200's `productInducedSmoothOrbitSections`, given torus coordinates `e`, a lattice map `n` with `χ_z(m) = torusCharacter (n m) z` and the hypotheses of Lemma VII.1.2 at every representative; for `Ξ = xi`, `fourierOrbitSmoothSectionLinearXi` (`InducedConstantTermFourierXi`); with the lattice map taken to be `laurentExponent` of Laurent coordinates, so that only the growth bound `‖n(m)‖ ≤ C (1 + σ(m))` remains a hypothesis, `fourierOrbitSection_mem_smooth_of_hasLaurent`, `fourierOrbitLaurentSmoothSectionLinear` (`FourierOrbitLaurentSmoothness`, Worker 249); the second assertion, continuity of `f ↦ ψ_f[O,P]` from `C(G)` to `C^∞(O,P)` with the topology of the row VI.3, under the same hypotheses: `fourierOrbitSectionCLM` and its Laurent form `fourierOrbitLaurentSectionCLM` (`FourierOrbitContinuity`, Worker 249, through the bound of the torus derivatives of `ψ_f[O,P]` by a seminorm of `f`, `exists_norm_torusPartialDerivList_fourierOrbitSection_le`) |
| Lemme VII.1.4 | 317 | `ψ_f` is `°c`-invariant | VII.1.1, V.3.1 | Book | none |
| Prop. VII.2.1 | 317 | `(f_ψ)^(ω',P)` in terms of `ψ` | VI.4.1, VII.1.2, III.1 (2), (3) | Book | for the Fourier inversion over `A_G` in the case `M = G` (p.318), on a finite torus in coordinates, for continuous `f` and a finite left-invariant measure (generic, Worker 249): `hasSum_torusFourierCoeff_mul_conj` (absolutely summable coefficients), `hasSum_torusFourierCoeff_mul_conj_isTrivialOn` (the partial series over the characters trivial on a finite subgroup), `sum_torusCharacter_subgroup` (`TorusFourierInversion`); the case `M = G` on actual rational points (generic over a split component `A_G`, with `μ(ω) = 1`, Worker 249): the restriction kernel `ker(Im X(G) → Im X(A_G))` in circle coordinates, `coordinates_symm_mem_restrict_ker_iff` (`RationalValuationCoordinates`, with `latticeAnnihilator`, `isTrivialOn_latticeAnnihilator_iff`, `hasSum_torusFourierCoeff_mul_conj_mem` in `Langlands/HarmonicAnalysis/TorusLatticeDuality`); the Fourier inversion on `A_G`, `integral_rationalSplitCenterInversionIntegrand`, `integral_rationalSplitCenterInversionIntegrand_eq_zero` (`RationalSplitCenterFourierInversion`), along the orbit, `integral_rationalOrbitInversionIntegrand`, `integral_rationalOrbitInversionIntegrand_eq_zero` (`RationalOrbitFourierInversion`), and with the actual central characters of the discrete-series classes (`discreteSeriesCentralCharacter`, `discreteSeriesCentralRestriction` in `DiscreteSeriesCentralCharacter`, Worker 200), `rationalOrbitCentralCharacter`, `integral_rationalOrbitCentralInversion`, `integral_rationalOrbitCentralInversion_eq_zero` (`RationalOrbitCentralInversion`); the pairing `∫_G conj(E ψ') f_ψ`, `integral_conj_mul_rationalOrbitWavePacket`, `integral_conj_mul_rationalOrbitWavePacket_eq_zero`, `integral_conj_mul_rationalOrbitWavePacket_of_mem` (`RationalOrbitWavePacketPairing`), and `(f_ψ)^(ω') = ν_A(A_G ∩ G¹) ψ_{ω'}` (`0` off `O`), `coefficientFourierTransform_rationalOrbitWavePacket`, with `rationalOrbitSectionExtension` (`RationalOrbitWavePacketFourier`); the pairing and Fourier-transform theorems for `M = G` are conditional: they assume connected reductive `G`, closed `A_G`, measures `μA` on `A_G` (left and right invariant) and `μG` on `G(F)` (also invariant for the Fourier transform) and a quotient measure `ν` on `A_G\G(F)` compatible with them whose image on `G(F)/A_G` is the measure of the discrete series (`hν`, `hνμ`), continuity in `ω ∈ O` of the coefficients `(E^G_G ψ_ω)(g)` (`hcont`, Lemma VI.2.1 (i) in the source), integrability of `a ↦ f_ψ(a g)` on `A_G` (`hintA`), for the pairing the integrability of `conj(E ψ') f_ψ` on `G(F)` (`hint`), and for the Fourier transform also weights `Ξ`, `σ` with `L2Weights`, invariant under `g ↦ g⁻¹`, an element `f` of `C(G)` for these weights equal to `f_ψ` (`hf`; this is the membership `f_ψ ∈ C(G)` of Prop. VI.3.1, which is not proved) and tempered coefficients of `ω'` (`hT`); the factor `ν_A(A_G ∩ G¹)` is kept and not compared with the source normalization `mes(A_G ∩ K) = 1` of I.1; general `M`: none |
| Prop. VII.2.2, Cor. VII.2.3 | 318–319 | orthogonality of wave packets for non-conjugate Levis; inner-product formula | VI.2.2, VII.1, VI.4.1, VII.2.1 | Book | (ii) for `M = M' = G` on actual rational points, with `μ(ω) = 1`, conditionally: `rationalOrbitSectionInner`, `integral_conj_rationalOrbitWavePacket_mul_eq_zero` (orbits `O' ≠ O`) and `integral_conj_rationalOrbitWavePacket_mul` (`(f_{ψ'}, f_ψ) = μ_A(A_G ∩ G¹) ∫_O (ψ'_ω, ψ_ω) dω` for two sections over `O` with the same base point) (`RationalOrbitWavePacketInner`, Worker 249), under the hypotheses of the `M = G` pairing theorems of the row Prop. VII.2.1 (connected reductive `G`, closed `A_G`, compatible quotient measure `hν`, `hνμ`, `hcont`, `hintA`) and the absolute convergence of the double integral over `G × O` (`hint`, from Lemma VI.2.2 in the source); the factor `μ_A(A_G ∩ G¹)` is kept and its comparison with the source normalization `mes(A_G ∩ K) = 1` is open, and sections over `O` based at different points are not treated; general `M` on Worker 200's `C^∞(O,P)` (Worker 249), for a weight `w` in place of `μ`, a finite measure on the unitary unramified characters and the hypotheses of Lemma VI.2.2 of the row VI.3 together with integrability hypotheses: formula (1) of the proof, `(f_ψ, f)_G = ∫_O conj(w(ω)) (ψ_ω, ψ_f[O,P]_ω) dω` for `f ∈ C(G)` whose `ψ_f[O,P]` is a smooth section, `pairing_inducedOrbitWavePacket_eq_integral_productPairing`, and `(f_ψ, f)_G = 0` when `f̂(ω, P) = 0` on `O`, `pairing_inducedOrbitWavePacket_eq_zero` (`InducedOrbitWavePacketPairing`); the last step of the proof of Cor. VII.2.3, `ψ_f[O,P] = 0` when `ψ_f[O,P]` is a smooth section and `(f_ψ, f)_G = 0` for every `ψ ∈ C^∞(O,P)`, for a continuous bounded weight `u > 0` and a finite character measure `ρ` that is positive on every nonempty open set (`[IsFiniteMeasure ρ]`, `[ρ.IsOpenPosMeasure]`), `fourierOrbitSection_eq_zero_of_forall_pairing_inducedOrbitWavePacket_eq_zero` (`InducedOrbitWavePacketOrthogonality`); (i) and, for general `M`, (ii): none |
| VII.2 | 319 | Hermitian product on `C^∞(Θ)_inv`, positive definite, `G × G`-invariant | VII.2.2 | Data, Book | for one orbit and without `μ(ω)`: the positive integral core of the orbit pairing, `productInducedSmoothOrbitCore` (`ProductInducedOrbitForm`); the `G × G`-invariant positive form on one `C^∞(O,P)`, without `μ(ω)`, `productInducedSmoothOrbitForm` (`ProductInducedOrbitFullAction`, Worker 200); for one orbit with a continuous bounded weight `u > 0` in place of `μ` and a finite character measure `ρ` positive on every nonempty open set (`[IsFiniteMeasure ρ]`, `[ρ.IsOpenPosMeasure]`), the positive definite summand `∫_O u(ω) (ψ'_ω, ψ_ω) dω` as an inner product core on `C^∞(O,P)`, `unitaryOrbitWeightedProductCore` (`InducedOrbitWavePacketOrthogonality`, Worker 249, with `unitaryOrbitWeightedProductPairing` in `InducedOrbitWavePacketPairing`); the product on `C^∞(Θ)_inv`: none |
| Rem. VII.2.4, Thm VII.2.5 | 320 | main targets above | VII.2.1–VII.2.3, VII.1.4 | Book | none |

## Chapter VIII. Plancherel formula (pp.320–332)

| Item | Page | Content | Uses | Class | Lean coverage |
|---|---|---|---|---|---|
| Thm VIII.1.1, VIII.1 (1)–(3) | 320 | main targets above | VII.1.1, VII.2.4, VIII.2–VIII.5 | Book | none |
| Thm VIII.1.2, Rem. VIII.1.3 | 321 | finiteness of `Θ^H_G`; finiteness of `Θ^H` by induction on semisimple rank | VIII.4.1, VIII.4.2 (proof in VIII.5) | Book | Thm VIII.1.2 from the finite dimensionality of a space containing the bi-invariant coefficients (generic), see the row VIII.5; Rem. VIII.1.3: none |
| VIII.2, Lemme VIII.2.1 | 321–322 | `°f = f − κ(ψ)`; `°C(G)` = cuspidal Schwartz functions | VII.1.2, VII.2.5, III.6, VIII.1 (2) for Levis | Data, Book | the first step of the proof of Lemma VIII.2.1 for one parabolic `P` and one orbit `𝒪` (generic, Worker 249): if `f^{(P),Ind} = 0` (`ConstantTermIndVanishes`), then `f̂(ω, P) = 0` at every representative (`inducedFourierTransform_eq_zero_of_constantTermInd_eq_zero`, by Lemma VII.1.2) and `ψ_f[𝒪, P] = 0` (`fourierOrbitSection_eq_zero_of_constantTermInd_eq_zero`) (`CuspidalWavePacketOrthogonality`, with the hypotheses of Lemma VII.1.2 at every representative); `°f`, `°𝒞(G)` and the converse direction (which uses Theorem VII.2.5): none |
| Rem. VIII.2.2, Lemme VIII.2.3 | 322–323 | symmetries of `°`; `f_1 * f_2 = f_1 * °f_2` for cuspidal `f_1` | VII.2, VIII.2.1 | Book | the vanishing in the proof of Lemma VIII.2.3 for the wave packets of one orbit of one `P` (generic, Worker 249): `(f_ψ, f)_G = 0` when `f^{(P),Ind} = 0`, `pairing_inducedOrbitWavePacket_eq_zero_of_constantTermInd_eq_zero` (`CuspidalWavePacketOrthogonality`, under the hypotheses of the wave-packet pairing with the weight `w` in place of `µ(ω)`); the convolution form `f₁ ∗ f_ψ = f_ψ ∗ f₁ = 0`, Remark VIII.2.2 and the identity `f₁ ∗ f₂ = f₁ ∗ °f₂` (which needs `κ`): none |
| Prop. VIII.3.1 | 323–326 | for `f_1 ∈ °C(G)`, `f_2 ∈ C(G)` and every `r ∈ ℝ`, the bound `≤ c δ_0(a)(1+σ(a))^{-r}` on `∫_G f_1(a g a^{-1}) f_2(g) dg` for `a ∈ Ā_0^+ ∩ G^1` (the Lean estimates are stated on an arbitrary supplied set `T`) | II.3, II.4, II.1, VIII.2.1 | Book | generic: `conjugationIntegralBound_of_split` (from the decomposition of the integral, estimate (3) `ConvolutionWeights.lintegral_conj_mul_le` and the cuspidal estimate `lintegral_cuspidal_le`); the decomposition from open-cell data: `integral_conj_mul_eq_split`, `conjugationIntegralBound_of_openCell`; inequality (2) from II.3.5: `conjugationSigmaBound_of_openCellBound` |
| Cor. VIII.3.2 | 326 | absolute convergence over `A_G\G` | VIII.3.1, I.1 (4), (5) | Book | `lintegral_lt_top_of_conjugationIntegralBound` (generic: cover, measure bound and summability as hypotheses) |
| VIII.4, Prop. VIII.4.1 | 327–330 | `p_χ`, `°C_H`; `p_χ(°C_H)` finite-dimensional | VIII.2, VIII.3.2 | Data, Book | `centralProjection`, `Space.centralProjection` (`p_χ` with absolute convergence, `χ`-covariance and bi-invariance, generic); the estimate on `G^1` in the proof of VIII.4.1, `enorm_centralProjection_le_rpow_neg`; the reproducing-kernel step of the proof, `IsReproducingKernel.finiteDimensional` (generic); the proof assembled for functions on `G` read on `A_G\G` (generic, Worker 249): the kernel `α_χ` and formula (1), `kernelAlphaChi`, `integral_conj_kernelAlphaChi_mul` (`KernelReproduction`), its quotient form and finiteness from an integrable diagonal, `integral_centralProjection_mul_conj`, `finiteDimensional_of_kernelAlphaChi` (`KernelQuotient`, with `SectionReproducingKernel`), the diagonal, `kernelAlphaChi_diag_eq`, `integrable_re_kernelAlphaChi_diag` (`KernelDiagonal`), and Proposition VIII.4.1 from Prop. VIII.3.1 and Cor. VIII.3.2, `finiteDimensional_of_conjugationIntegralBound` (`KernelFiniteness`); `°e`, `°C_H`, Lemma VIII.2.3, Prop. VIII.3.1 for the conjugates involved and the cell data of I.1 (4), (5) are hypotheses |
| Thm VIII.4.2 | 330 | `p_χ(°C(G)) = A_2(G)_χ` | III.1 (2), VII.2.5, VIII.2.2, VIII.2.3, VIII.4.1 | Book | the inclusion `p_χ(°C(G)) ⊂ A_2(G)_χ` in abstract form (generic, Worker 249): formula (2) and the reproducing identity, `integral_conj_centralProjection_mul_centralProjection`, `centralProjection_eq_inv_mul_integral` (`CentralCoefficientFormula`), and the passage from a semisimple representation with a reproducing vector to the span of the coefficient spaces of its square-integrable irreducible subrepresentations, `formCoefficient_mem_squareIntegrable`, `exists_mem_squareIntegrable_of_reproducing` (`DiscreteCoefficientSpace`); for the reverse inclusion `A₂(G)_χ ⊂ p_χ(°C(G))`, the computation for `M = G` on actual rational points (generic over a split component `A_G`, Worker 249): `(p_χ f_ψ)(g) = μ_A(A_G ∩ G¹) Σ_{ω ∈ 𝒪_χ} (E ψ_ω)(g)` with `𝒪_χ = {ω ∈ 𝒪 ; χ_ω = χ}`, and its value `μ_A(A_G ∩ G¹) (E ψ_{ω₁})(g)` for `ψ` vanishing on `𝒪_χ − {ω₁}`, `rationalOrbitCentralFiber`, `integral_central_rationalOrbitWavePacket`, `integral_central_rationalOrbitWavePacket_of_vanishing` (`RationalOrbitCentralProjection`; continuity in `ω` and integrability over `A_G` for the given `g` as hypotheses); Remark VIII.2.2, Lemma VIII.2.3, the square integrability of (2), the existence of such sections `ψ` and `f_ψ ∈ °C(G)` (Theorem VII.2.5): none |
| VIII.5 | 331–332 | proofs of VIII.1.2 and VIII.1.1 | VII.2.5, VIII.1.3, VIII.4.1, VIII.4.2 | Book | proof of VIII.1.2, abstract steps (generic, Worker 249): independence of the spaces `A(ω)` of pairwise inequivalent irreducibles, `iSupIndep_coefficientFunctionSpace`, `A(ω)^{H×H} ≠ 0`, `exists_isBiInvariant_coefficient_ne_zero`, and finiteness of a family whose bi-invariant coefficients lie in one finite-dimensional space, `finite_of_isBiInvariant_coefficient_mem` (`CoefficientIndependence`); the reduction of VIII.1.2 to the finiteness of the sets `E_2(G)^H_χ` (generic, Worker 249): `discreteSeriesCentralFixed` (`E_2(G)^H_χ`), `discreteSeriesFixedOrbits` (`Θ^H_G`), the finiteness of `Â^H_G / Im X(G)` in the form `finite_image_mk_characterAnnihilator`, and `finite_discreteSeriesFixedOrbits`, `finite_discreteSeriesFixedOrbits_of_coefficient_mem` (`DiscreteSeriesOrbitFiniteness`; an open `H ≤ G^1`, compactness of `A ∩ G^1`, the extension of the unitary characters of `A` trivial on `A ∩ G^1` to `Im X(G)` and the finite-dimensional space of VIII.4.1, VIII.4.2 are hypotheses); the extension hypothesis removed for an open `G^1` with `A ∩ G^1` compact, `finite_discreteSeriesFixedOrbits_of_finiteDimensional` (`UnramifiedCharacterExtension`), and the specialization to actual rational points with `A_G(F)` the image of a split component and `G^1` the common kernel of the rational norm characters, `rationalDiscreteSeriesFixedOrbits`, `isClosed_range_splitComponent`, `finite_rationalDiscreteSeriesFixedOrbits_of_finiteDimensional` (`RationalDiscreteSeriesOrbitFiniteness`); proof of VIII.1.1, abstract steps: `p_χ φ = 0` when `p_χ φ` lies in the span of the coefficient spaces of subrepresentations `S` with `π_S(ˇφ) = 0`, `centralProjection_eq_zero_of_schwartzAction_eq_zero` (`CentralProjectionVanishing`), and Fourier inversion on `A_G`, `eq_zero_of_forall_centralProjection_eq_zero` (`CentralFourierInversion`, with `eq_zero_of_characterSum_eq_zero` in `Langlands/HarmonicAnalysis/DiscreteFourierUniqueness`), whose hypothesis `HasFGCompactOpenQuotients A` holds for every closed central subgroup `A` of `G(F)`, `hasFGCompactOpenQuotients_rationalPoints` (`CentralQuotientGeneration`); in particular for `A_G(F)`, the image of the rational points of a split component, `hasFGCompactOpenQuotients_splitComponent` (`CentralQuotientGeneration`); the family `f ↦ (p_χ f)_{χ ∈ Â_G}` on `C(G)` and its injectivity, `Space.centralProjectionFamily`, `Space.centralProjectionFamily_injective`, and the end of the proof of VIII.1.1 in abstract form (`φ = 0` when every `p_χ φ` lies in the span of the coefficient spaces of subrepresentations `S` with `π_S(ˇφ) = 0`), `Space.eq_zero_of_forall_schwartzAction_eq_zero` (`CentralProjectionFamily`); `ω(ˇφ) = 0` (from VII.2.5) and Theorem VIII.4.2 for Waldspurger's `G`: none |

## Library coverage

The declarations below formalize parts of the article in the Library at commit
`ce52163e` (for the entries named in the header, at the commits named there). The list covers the modules of this task's two executors and other
modules found by searching the Library for the article and for the reductive
data of I.1; it is not the declaration-level reuse audit of condition 7. None
proves a numbered theorem of Chapters IV–VII as stated for Waldspurger's `G`. There are
generic or conditional versions with explicit hypotheses: for IV.1 generic formal laws of the
standard integral, and Thm IV.1.1 as a Prop derived from three unproved Props; for Lemma VI.2.2
a generic version for one `ω`; for Prop. III.7.1 and Cor. III.7.2 versions in an abstract setting for `G → G/G^1` and `A_G` (see the row III.7); for Lemma VI.2.1 (i) and Lemma VI.2.2 versions on Worker 200's `C^∞(O,P)`; for Lemma VII.1.1 a version for an admissible
smooth representation with tempered coefficients and a version for `I_P^G ω` on `L(ω,P)`; for
Lemma VII.1.2 a version with explicit analytic hypotheses; for Prop. VII.1.3 both
assertions given torus coordinates and a lattice map; for the uniqueness half of Lemma III.5.1 a
version with the form (1) of the differences as a hypothesis; for IV.2.2 a weaker open-locus
consequence as an unproved Prop; for formula (1) of the proof of Prop. VII.2.2 and the last step
of the proof of Cor. VII.2.3 versions on Worker 200's `C^∞(O,P)` with a weight in place of `μ`
(the latter for a finite character measure positive on nonempty open sets);
for Props. VII.2.1 and VII.2.2 (ii) the case `M = G` with `μ = 1`, assuming among others `f_ψ ∈ C(G)` (Prop. VI.3.1, open) for the
Fourier transform and the absolute convergence of the double integral for the inner product,
with the factor `μ_A(A_G ∩ G¹)` not compared with `mes(A_G ∩ K) = 1`; see the table; for VIII.3.1, VIII.3.2, VIII.4.1, the
inclusion of VIII.4.2 and steps of VIII.5 there are generic versions with explicit
hypotheses (see below). Most work over explicit
abstract data.
The modules `RationalCharacterValuation`, `LocalFieldUnits`,
`RationalImageCharacters`, `RationalImageRealPart`,
`RationalCharacterTopology`, `RationalNormKernelTopology` and `PointTopology`
are specializations to the actual rational points of a group scheme over an
actual nonarchimedean local field. The Library has the rational-point topology
on `G(F)` and the existence of a compact open subgroup of `G(F)`
(`Langlands.BruhatTits.rationalPoint_exists_compactOpenSubgroup`). It has
predicates for maximal split tori and minimal parabolic subgroups
(`IsMaximalSplitTorus`, `IsMinimalParabolicSubgroup`), Prop-valued product
predicates for a given subgroup `K` of the rational points
(`Langlands/BruhatTits/Iwasawa/PointProducts`), and the finite index of the
restriction of rational characters to a split component
(`IsSplitComponent.finiteIndex_range_characterRestrict`, Worker 1001: the
finite-index half of I.1's `Rat(G) ⊗ Q ≅ Rat(A_G) ⊗ Q`; the module
`CharacterRestrictionInjective` derives injectivity from the Prop
`CentralSplitTorusCharacterStatement`, taken as a hypothesis). It does not yet
construct the special maximal compact subgroup `K` of I.1, and it does not
prove `G = P K` or the Cartan decomposition (4); the existence of `K` and the
Iwasawa decomposition for Bruhat–Tits data are the Prop targets
`SpecialCompact.SpecialMaximalCompactExistence`,
`SpecialCompact.AvailableSpecialMaximalCompactExistence` (Worker 1249) and
`Iwasawa.AvailableIwasawaStatement` (Worker 1265) (statements only). It has the unproved Prop
target `JointSpecialCompactBasisExistenceStatement` (module
`Langlands/BruhatTits/SpecialCompact/JointBasisStatement`), which asks for one
apartment point whose compact subgroup has the special compact properties, the
Iwasawa products, the Cartan comparisons and a simultaneous standard basis.
The Iwasawa and Cartan results for actual rational points in
`Langlands/Representation/Aubert/General/RationalIwasawaCartan` (Worker 785)
take conjuncts of its conclusion as hypotheses. The full-center volume bound
`rationalLatticeQuotientVolume` (module
`Langlands/Representation/Aubert/General/RationalLatticeQuotientVolumeProof`)
proves the Prop `RationalLatticeQuotientVolumeStatement`. Its bound on the
measures of the images in `G(F)/Z(G(F))` of the double cosets `K a t K`, for
`a` the uniformizer image of a combination with natural coefficients of
finitely many supplied cocharacters and `t` in a finite set, has as
premises a supplied `SimultaneousStandardBasisAt`, a generic cocharacter, the
unproved Prop `StandardCocharacterStatement` (derived from unproved root-system Props by
`standardCocharacterStatement_of_relativeRootSystem_of_signs` and
`standardCocharacterStatement_of_reflections_of_signs`), local compactness and the
nonarchimedean and Hausdorff properties of the rational-point topology, and
closedness of the standard unipotent subgroups. For the lattice of `H_G` it
proves that the actual valuation image of a connected reductive group is free
of finite rank (`rationalReductiveImage_free_finite`, see below). Two
comparisons remain open: the equality of that rank with the rank of the
rational characters of `G` (equivalently, of its split component), and the
finite index of the valuation image of the split component in the actual
valuation image (the premise `hindex` described before the list of rational
modules below; Renard V.2.6). For the roots and Weyl group of I.1 it has
`relativeRoots`, `relativeWeylGroup` and `relativeWeylAction` (module
`Langlands/GroupScheme/Rational/RelativeRoots`), the normalizer and centralizer
subgroup functors of `Langlands/GroupScheme/Rational/TorusNormalizer`, and the
Prop target `RelativeWeylCoxeterStatement`, derived from three unproved structural Props by `relativeWeylCoxeterStatement_of_rootPairingWeylCoxeterStatement` (`RelativeWeylCoxeterReduction`). Representative data for the Cartan decomposition
(`RenardUniformizerSection`, `RenardRepresentativeData`, Worker 454) and the
Prop targets `RenardLatticeComparisonStatement` and
`RenardDominantComparisonStatement` are in
`Langlands/Representation/Plancherel/`. `RenardDominantComparisonStatement`
(dominant centralizer sections and finite positive covers, Renard V.3.21–V.3.23
and V.5.1(4)) is proved by `renardDominantComparison`
(`RenardDominantComparisonProof`, Worker 1292, with the helper modules
`RenardActualLattice`, `RenardDominantValuation`, `RenardDominantTransversal`,
`RenardDominantFiniteCover`, `RenardDominantSections` and
`RenardIntegralRestriction`). Its conclusions are required for every
bijectivity argument of the restriction-evaluation map of the centralizer
valuation; the existence of such an argument is the separate unproved Prop
`CentralizerValuationComparisonStatement`. `RenardLatticeComparisonStatement`
is a statement only.

### General groups

Namespace `Langlands.Plancherel`, module directory
`Langlands/Representation/Plancherel/` (Worker 200 unless stated):

- `UnramifiedCharacters`: `commonNormKernel`, `unramifiedCharacters`,
  `unitaryUnramifiedCharacters` for a supplied family of positive norm
  characters (I.1, `X(G)` and `Im X(G)`).
- `UnramifiedLogarithm`: `normLog`, `normLogarithm` (I.1, the map `H_G`
  for supplied characters).
- `UnramifiedValuation`: `characterValuation`, `characterValuationImage`,
  `normKernelValuationQuotientEquiv`: integer evaluation of a supplied family
  of characters, its actual image, and the comparison of the quotient by the
  common norm kernel with that image (I.1, `H_G` and its image; Renard V.2.3).
- `RationalCharacterValuation`: `rationalNormCharacters`,
  `rationalCharacterValuation`, `rationalCommonNormKernel`,
  `rationalNormLogarithm`, `rationalCharacterValuationImage` on
  `GroupScheme.rationalPoints G` for the actual rational characters (I.1).
- `RationalImageCharacters`, `RationalImageRealPart`: characters and unitary
  characters of the actual valuation image (with the discrete topology);
  `rationalImageUnramifiedEquiv`, their identification with the unramified
  characters, assuming continuity of the valuation projection; and the real
  and unitary parts of such characters (I.1, `X(G)`, `Im X(G)` and `Re`).
- `RationalCharacterTopology`: `rationalNormContinuousCharacter`,
  `rationalOrderContinuousCharacter`, `isClosed_rationalCommonNormKernel`,
  `compactSubgroup_le_rationalCommonNormKernel` (the actual rational norm
  characters are locally constant for the rational-point topology; their common
  kernel is closed and contains every compact subgroup). Openness of the kernel
  and the comparisons with the valuation image (`...Conditional`) assume
  `NonarchimedeanGroup` and `WeaklyLocallyCompactSpace` for the rational-point
  topology.
- `RationalNormKernelTopology`: `isOpen_rationalCommonNormKernel`,
  `rationalCommonNormOpenSubgroup`, `rationalNormKernelQuotientDiscrete`,
  `rationalNormKernelQuotientContinuousEquiv`,
  `continuous_rationalValuationImageProjection`,
  `rationalCanonicalImageUnramifiedEquiv` (the same conclusions without those
  two premises, for an affine group scheme locally of finite type: the common
  norm kernel is open, the quotient by it is discrete and homeomorphic to the
  valuation image, and the characters of that image are the unramified
  characters; I.1, `H_G` and `X(G)`). Continuity of the last equivalence for
  the compact-open topologies is not claimed.
- `RationalUnramifiedCharacterTopology`:
  `rationalCanonicalImageUnramifiedContinuousEquiv`,
  `rationalCanonicalUnitaryImageUnramifiedContinuousEquiv`,
  `compactSpace_rationalUnitaryUnramifiedCharacters` (the identification of
  the unramified characters with the characters of the valuation image is a
  homeomorphism for the compact-open topologies, and the unitary unramified
  characters form a compact group; I.1, `X(G)` and `Im X(G)`).
- `LocalFieldUnits`: `fieldNormUnits`, `fieldOrderUnits` (the normalized
  absolute value and order on `F^×`).
- `FieldUnitsTopologyStatement` with its proof `fieldUnitsTopology` in
  `FieldUnitsTopologyProof` (Worker 1218): continuity and local constancy of
  these maps.
- `NormKernelTopologyStatement`: `CommonNormKernelTopologyStatement` (the
  common kernel of continuous positive characters of a nonarchimedean, weakly
  locally compact group is open and closed and contains every compact subgroup
  and the commutator subgroup). Proof `commonNormKernelTopology` in
  `NormKernelTopologyProof` (Worker 55).
- `CentralSubgroupCoefficients`: `centralQuotientProjection`,
  `IsSquareIntegrableModCentralSubgroup` (III.1, square integrable modulo a
  prescribed central subgroup). `CentralSubgroupComparisonStatement` compares
  square integrability modulo a closed central subgroup `A` with compact
  quotient in the center with square integrability modulo the center; the proof
  `centralSubgroupSquareIntegrabilityComparison` is in
  `CentralSubgroupComparisonProof` (Worker 117).
- `DiscreteSeriesOrbits`: `IsDiscreteSeriesClass`, `DiscreteSeriesClass`,
  `unramifiedTwistStabilizer`, `discreteSeriesOrbit`,
  `discreteSeriesStabilizer`, `discreteSeriesOrbitEquiv` (III.1, III.7:
  `E_2(G)` and its `Im X(G)`-orbits).

Modules of the same directory published after commit `e9121d2f` (the author is
named where the module's Markdown names one).

Shared premise `hindex`. Many of the actual rational-point results below take
the explicit hypothesis
`hindex : (RenardCartan.splitValuationImage s).FiniteIndex`: the valuation
image of the central subgroup `s(T(F))` (in the source, the split component
`A_G`) has finite index in the actual valuation image of `G(F)`. This is a
remaining proof obligation, not a permitted permanent external structural
assumption: Renard proves it in V.2.6, and the Library has only the Prop
target `SplitComponentLatticeStatement` (module
`RenardLatticeComparisonStatement`), with no proof. `SplitComponentLatticeBridge`
(Worker 1503) proves the finite index from injectivity of the restriction of
rational characters to the split component
(`finiteIndex_splitValuationImage_of_injective`), proves the valuation-bijection
conjunct of `SplitComponentLatticeStatement` (`bijOn_C0_splitValuationImage`), and
derives that statement from either of the unproved Props
`CentralSplitTorusCharacterStatement` and `CharacterRestrictionStatement`
(`splitComponentLatticeStatement_of_centralSplitTorusCharacter`,
`splitComponentLatticeStatement_of_characterRestriction`). Entries marked
"(given `hindex`)" below hold only under this premise. It is distinct from
two results that the Library proves without it: the finite index of the
restriction of algebraic rational characters to a split component
(`IsSplitComponent.finiteIndex_range_characterRestrict`), and the
surjectivity of the restriction of unitary unramified characters,
`rationalUnitaryUnramifiedCharacterRestrict_surjective` (for a connected
reductive `G` and a split component).

- `RationalUnramifiedRestriction`, `RationalRestrictionKernel`,
  `RationalRestrictionSurjectivity` (Worker 200 for the first two):
  `rationalUnramifiedCharacterRestrict`, `rationalUnitaryUnramifiedCharacterRestrict`
  (I.1, p.239: restriction of unramified characters to `A_G`);
  `rationalUnitaryUnramifiedCharacterRestrict_surjective` (surjectivity on unitary
  characters, without `hindex`); `finite_rationalUnramifiedCharacterRestrict_ker`,
  `finite_rationalUnitaryUnramifiedCharacterRestrict_ker` (finite kernel, given `hindex`).
- `RestrictionNormalizedHaar`, `RationalCharacterHaar`: `restrictionNormalizedHaar`
  (generic, for a homomorphism with finite kernel), `rationalUnitaryUnramifiedProbabilityHaar`
  (the probability Haar measure on the unitary unramified characters of an actual group; for
  `A_G` this is the mass-one measure of p.239), `rationalUnitaryUnramifiedCharacterHaar`,
  `isLocallyMeasurePreserving_rationalUnitaryUnramifiedCharacterRestrict` (I.1, p.239: the
  measure on `Im X(G)` locally preserved by restriction; given `hindex`).
- `RationalImageLattice`, `RationalUnramifiedCharacterCoordinates` (Worker 200):
  `rationalImageBasis`, `rationalReductiveImage_free_finite`,
  `rationalCanonicalUnramifiedCharacterCoordinates`,
  `rationalCanonicalUnitaryUnramifiedCharacterCoordinates` (I.1: the valuation image of a
  connected reductive group is free of finite rank, without `hindex`; coordinates
  `X(G) ≅ (ℂ^×)^r` and `Im X(G) ≅ (S^1)^r`, where `r = rationalImageRank G` is the rank of
  the valuation image; its equality with the rank of the rational characters is not proved).
- `RationalCentralQuotient` (Worker 200): `rationalCentralQuotientEquiv`,
  `finite_rationalCentralQuotient` (finiteness of `G/(G^1 A_G)`, given `hindex`;
  Renard V.2.6).
- `TwistStabilizerComparison`, `RationalTwistStabilizer` (Worker 200):
  `unramifiedTwistStabilizerEmbedding`, `finite_unramifiedTwistStabilizer`,
  `finite_discreteSeriesStabilizer` (generic, with finiteness of the corresponding central
  quotient as a hypothesis), `finite_rationalDiscreteSeriesStabilizer` (given `hindex`)
  (III.7, p.273: the stabilizer of a discrete-series class in `X(G)` is finite and unitary).
- `DiscreteSeriesOrbitTopology`, `RationalDiscreteSeriesOrbitTopology` (Worker 200 for the
  second): `discreteSeriesOrbitMap`, `discreteSeriesOrbitHomeomorph`,
  `compactSpace_discreteSeriesOrbit`, `t2Space_discreteSeriesOrbit`,
  `discreteSeriesOrbitBaseChange`, `rationalDiscreteSeriesOrbitCoordinateMap` (III.7, VI.1:
  the quotient topology of an orbit `O`, independent of the base point); for actual rational
  points, the Hausdorff property `t2Space_rationalDiscreteSeriesOrbit` is given `hindex`.
- `FiniteCharacterQuotientMeasure`, `DiscreteSeriesOrbitMeasure`,
  `RationalDiscreteSeriesOrbitMeasure`, `RationalNormalizedOrbitMeasure` (Worker 200 for the
  last two): `IsLocallyMeasurePreserving`, `finiteCharacterQuotientMeasure`,
  `discreteSeriesOrbitMeasure` (generic, for a finite stabilizer),
  `rationalDiscreteSeriesOrbitMeasure`, `rationalNormalizedDiscreteSeriesOrbitMeasure`
  (given `hindex`) (VI.3, p.302: the measure on `O` locally preserved by the character
  parametrization, with the I.1 scale).
- `RationalOrbitIntegration` (Worker 200): `rationalDiscreteSeriesOrbitIntegral`,
  `integrable_rationalNormalizedDiscreteSeriesOrbitMeasure`,
  `norm_rationalDiscreteSeriesOrbitIntegral_le` (integration over `O`, VI.3; given `hindex`).
- `RationalOrbitSmoothFunctions`, `RationalOrbitBasisInvariance` (Worker 200):
  `finiteTorusExp`, `IsSmoothFiniteTorusFunction`, `IsSmoothRationalOrbitFunction`,
  `rationalSmoothOrbitFunctions`, `isSmoothRationalOrbitFunction_basis_iff` (VI.1: scalar
  smooth functions on `O`, tested on the unitary character torus, independent of the basis).
- `CharacterTorusDensity`, `RationalUnramifiedCharacterDensity`,
  `UnramifiedCharacterTransport` (Worker 34): `complexTorusPrincipalOpen`,
  `dense_complexTorusPrincipalOpen`, `rationalUnramifiedPrincipalOpen`,
  `dense_rationalUnramifiedPrincipalOpen`, `unramifiedCharactersHomeomorph` (density of
  principal open subsets of the character torus; internal).
- `CoefficientTensors`, `NormalizedCoefficientTensors`: `CoefficientTensor`,
  `coefficientTensorMap`, `range_coefficientTensorMap`, `coefficientTensorCongr`,
  `NormalizedCoefficientTensor`, `normalizedCoefficientMap`,
  `normalizedCoefficientTransport`, `normalizedCoefficientTransport_independent` (V.1, p.288:
  the tensor model of `L(ω,P)` and the coefficient `ℓ(π(g)v)` with image `A(π)`; VI.1: the
  transport along equivalences of inducing representations does not depend on the choice).
- `NormalizedInductionDualTensor`: `normalizedInductionIntegralDualEquiv`,
  `normalizedInductionDualTensorEquiv`, `normalizedInductionCoefficient_integrable` (I.3,
  p.243: the smooth contragredient of normalized induction by the quotient integral; V.1).
- `NormalizedProductInduction`: `normalizedProductInductionTensorEquiv` (V.1:
  `I_P^G(A) ⊠ I_Q^H(B) ≅ I_{P×Q}^{G×H}(A ⊠ B)`); see also
  `Langlands/Representation/Induction/BinaryProductTensor`.
- `RationalNormKernelSmoothDual` (Worker 6), `SplitTorusCompactKernel`,
  `SplitTorusCompactUnits`, `SplitTorusPositiveCharacter`, `SplitTorusRealPart`: smooth duals
  restricted to the norm kernel and characters of split tori (internal prerequisites; several
  cite Renard V–VI).
- `RenardSpecialCompactComparison`, `RenardSameCompactLeviComparison` (Worker 454 for the
  second): conditional comparisons of the compact quotient and of standard Levi subgroups
  with the valuation chamber (I.1 (4)); their geometric inputs are explicit Props.
- `SplitTorusNormFormula`, `SplitTorusRealPartLaws`, `SplitTorusUnitaryFactorization`,
  `SplitTorusNormalizationDiagnostic`: `smoothNormalizedParameter`,
  `normalizedRealPartFromLift`, `unitaryFactor`, `smoothUnitaryFactorization`,
  `normalizedAbsoluteValueCharacter` (the real parameter of a smooth character of an actual
  split torus and its factorization as a unitary character times a positive one; internal
  prerequisites). `RationalSmoothRealDescentStatement` (Worker 723):
  the Prop `RationalSmoothRealDescentStatement` (Renard V.3.19, statement only), with the
  factorization through the valuation image `rationalImageRealDescend` (`RationalImageRealDescent`)
  and the construction `rationalSmoothRealDescendOfStructure` from its local-point inputs
  (`RationalSmoothRealDescentConstruction`) (Worker 20).
- `RationalImageComplexExponential`, `RationalParameterTopology`,
  `RationalImaginaryParameters` (Worker 6 for the last),
  `RationalRealParameterExtension`, `RationalComplexParameterStatement`,
  `RationalComplexParameterQuotientStatement`: the complex additive parameters
  of the actual valuation image and their exponential
  `rationalImageComplexExponential` (`λ ↦ (a ↦ q^{-λ(a)})`), the stated period
  subgroup `rationalImagePeriodLattice`, a chosen lift
  `rationalImageComplexLift` with `rationalImageComplexCharacter_lift`, the
  pointwise parameter topologies with their finite-coordinate comparisons
  (`rationalImageComplexParameterContinuousCoordinates`), the imaginary
  parameters `rationalImageImaginaryParameters`, and the extension of positive
  characters of a split component to the valuation image,
  `exists_positiveImageCharacter_extension` (I.1, `X(G)`, `Re` and `Im`; the
  route of Renard V.3.20). The assertions of V.3.20 on lifts, periods, real
  parts, unitary parameters and surjectivity onto the unramified characters of
  `G(F)` are the Prop `RationalComplexParameterStatement`, and its quotient
  topology is the Prop `RationalComplexParameterQuotientStatement`; they are proved by
  `rationalComplexParameter` (`RationalComplexParameter`) and `rationalComplexParameterQuotient`
  (`RationalComplexParameterQuotient`) (Worker 6, Worker 1444). The discreteness of the periods
  and the compact imaginary quotient of Renard V.3.20 are the Prop
  `RationalImaginaryParameterQuotientStatement`, proved by `rationalImaginaryParameterQuotient`
  (`RationalImaginaryParameterQuotient`, Worker 6, Worker 1444). The map
  `ℂ ⊗ X(G) → Hom(Λ(G), ℂ)` of Renard V.3.19–V.3.20 and its exponential,
  `rationalCharacterTensorParameter`, `rationalCharacterTensorExponential`
  (`RationalCharacterTensorParameter`, Worker 6), and its bijectivity, the Prop
  `RationalCharacterTensorParameterStatement` (Worker 6), derived from the hypothesis that the
  actual valuation detects nonzero rational characters of every connected reductive group,
  `rationalCharacterTensorParameterStatement_of_detects` (`RationalCharacterTensorParameterReduction`);
  that detection unconditionally along split tori, `exists_rationalCharacterValuation_ne_zero_of_splitTorus`,
  and for connected reductive `G` under each of three unproved structural Props, for example
  `exists_rationalCharacterValuation_ne_zero_of_centralSplitTorusCharacter`
  (`RationalValuationDetection`, Workers 1521 and 1171).
- `TorusSplitNormFactorization` (Worker 1374): `splitNormExponent`,
  `exists_split_mul_commonNormKernel` (a fixed power of every point of an actual
  torus is a point of its maximal split subtorus times an element of the common
  norm kernel; internal).
- `RationalUnramifiedCoordinateAlgebra` (Worker 200),
  `UnramifiedOperatorFamilies`, `UnramifiedOperatorTransport` (Worker 200),
  `CompactIntertwiningFamilies` (Worker 200), `CompactIntertwiningComposition`,
  and the standard-integral modules `StandardIntertwiningCovariance`,
  `StandardIntertwiningNaturality`, `StandardIntertwiningMeasure`,
  `StandardIntertwiningTarget`, `StandardIntertwiningTargetLaws`,
  `StandardIntertwiningModulus`, `StandardIntertwiningComposition`,
  `StandardIntertwiningFactorization`, `StandardIntertwiningIntersectionFactorization`,
  `StandardIntertwiningIntersectionNormalization`, `StandardIntertwiningFirstFactorMass`,
  `StandardIntertwiningLocallyNormalizedComposition`,
  `StandardIntertwiningCompactOpenComposition`, `StandardIntertwiningFactorChoice`,
  `StandardIntertwiningFactorRegularity`, `StandardIntertwiningCountableComposition`:
  rational operator families and the formal laws of the standard integral; see the
  rows IV.1 and IV.1 (10)–(14).
- `IntertwiningCone`, `CharacterIntertwiningCone`, `SubtorusIntertwiningCone`
  (Worker 200), `AmbientCharacterForm`, `AmbientCharacterFormNaturality`,
  `AmbientCharacterIntertwiningCone` (Worker 200), `ParabolicIntertwiningRegion`,
  `ParabolicPointIntertwiningRegion` (Worker 200) and `ParabolicIntertwiningStatement`:
  the parameter regions of Thm IV.1.1 and its conditional statement; see the row
  Thm IV.1.1.
- `RationalAssociatedCentralCharacterSigns` (directory
  `Langlands/Representation/Aubert/General/`, namespace `Langlands.Plancherel`):
  scalar characters under associated-Levi conjugation, `scalarCharacter_eq_of_pullback_equiv`,
  `associatedLeviCenterConjugationEquiv` (internal support for a rank-one
  self-association argument).

The modules below construct the objects of V.1 and VI.1 on actual normalized induction
from the literal product parabolic. Unless stated otherwise, their data are: `G` is a locally compact
nonarchimedean group with actual subgroups `P`, `M`, `U` and a semidirect decomposition
`P = M ⋉ U` with `U` closed. Where they are used, the compact-picture results also take `P`
closed, a compact open subgroup `K`, the factorization `G = P K`, and continuity of the Levi
projection and of the positive characters `ν` defining the unramified characters, all as
explicit hypotheses.
Their normalized induction is the Library's full-parabolic normalization
`σ_A(p) = δ_U(p)^{1/2} A(r(p))`, with `δ_U` the Haar modulus of conjugation on `U` and `r` the
Levi projection. Its comparison with the Levi-inflated normalization of I.3 is
`normalizedInductionLeviEquiv` when `U` is unimodular (`LeviInflatedNormalization`, below).

- `Langlands/Representation/Induction/OpenSubgroupRestriction`, `NormalizedCompactPicture`:
  `openSubgroupInductionEquiv` (restriction of smooth induction to `K` when `G = P K`, for
  any topological group `G`, subgroup `P` and open subgroup `K`),
  `normalizedInductionCompactEquiv`, `unramifiedNormalizedInductionCompactEquiv` (the compact
  picture of normalized induction, one carrier for all unramified twists; IV.1, VI.1).
- `ProductInducedCoefficients`: `productInducedCoefficientObject` (`L(ω,P)`),
  `productInducedCoefficientMap` (`E_P^G`), `productInducedCoefficientMap_integral`,
  `productInducedCoefficientMap_action`, `range_productInducedCoefficientMap` (V.1, p.288).
  The coefficient map also assumes second countability of `G`, compactness of `P\G`,
  continuity of the Levi projection and admissibility of the inducing representation; the
  integral formula assumes `P` closed, unimodularity of `G` and the value of the modular
  character of `P` as hypotheses, for the Bruhat-density measure
  `normalizedInductionBruhatMeasure`, whose scale is not compared with Waldspurger's.
- `ProductInducedTransport`, `ProductCompactPicture`, `ProductCompactBaseChange`,
  `CompactSelfTwist`: `productInducedCoefficientTransport` (transport along an equivalence of
  inducing representations, independent of the equivalence for irreducible admissible
  ones), `productInducedCompactEquiv` (the fixed compact picture of `L(ω ⊗ χ, P)`),
  `productCompactBaseChangeEquiv` (change of the base representative),
  `unramifiedStabilizerCompactRepresentation` (the action of the stabilizer of `[ω]` in the
  unramified characters on the compact picture by self-twists) (VI.1, pp.295–296).
- `SmoothTensorFamilies`, `FiniteSmoothFamilyTransport`, `ProductInducedSmoothFamilies`,
  `ProductInducedOrbitSections`, `ProductInducedOrbitCoordinates` (Worker 200 for the first,
  second and last): `smoothFiniteTorusFunctions`,
  `finiteSmoothFamilies`, `smoothTensorInvariantFamilyEquiv`, `unitaryClassTwistStabilizer`,
  `productInducedSmoothFamilies`, `productInducedSmoothTensorFamilyEquiv`,
  `coherentProductInducedOrbitSections`, `productInducedSmoothOrbitSections`,
  `productInducedSmoothTensorOrbitEquiv`, `productInducedSmoothOrbitRebaseEquiv` (VI.1,
  p.296: for a fixed irreducible admissible `ω` and supplied coordinates
  `e : Im X(M) ≃ (S^1)^J` with `J` finite, coherent sections over every representative of the unitary
  unramified twist orbit of `ω` whose compact restrictions are finite sums of smooth scalar
  functions times fixed vectors are identified with the invariants of the unitary part of
  the stabilizer of `[ω]` in `C^∞((S^1)^J) ⊗ W`, `W` the compact picture).
- `ProductInducedOrbitBaseChange`, `ProductInducedDiscreteSeriesOrbit` (Worker 200 for the
  second): `productInducedSmoothOrbitBaseEquiv` (the smooth sections do not depend on the base
  representative), `unitaryOrbitRepresentativeDiscreteSeriesOrbit` (representatives of the
  unitary twist orbit of a square-integrable `ω` lie in its discrete-series orbit),
  `unitaryClassStabilizerEquivFull`, `finite_unitaryClassTwistStabilizer`,
  `productInducedFullStabilizerTensorOrbitEquiv` (invariants of the full unramified stabilizer
  in the tensor model; VI.1, III.7). The full-stabilizer results assume finiteness of the
  quotient of `M` by the product of the common norm kernel and a central subgroup, which is
  not proved for actual reductive groups.
- `LeviInflatedNormalization`, `RationalLeviInflatedNormalization`,
  `LeviNormalizedProductInduction`, `LeviNormalizedProductCoefficients`:
  `LeviNormalizedCovariant`, `normalizedInductionLeviEquiv` (induction with the covariance
  `f(m u x) = δ_P(m)^{1/2} σ(m) f(x)` of I.3, p.243, identified with the full-parabolic functor
  when `U` is unimodular), `standardNormalizedInductionLeviIsoOfStandardCocharacter` (the same on
  actual standard rational points, given `StandardCocharacterStatement`),
  `leviNormalizedProductInductionTensorEquiv`, `leviProductInducedCoefficientMap` (V.1 in this
  normalization).
- `StandardIntertwiningIntegral`: `StandardIntertwining.domain`, `StandardIntertwining.operator`,
  `operator_right_action`, `operator_uniformly_smooth`, `operator_unipotent_mul`,
  `compatibleMeasure_exists` (IV.1, pp.277–278: the integral of `f(u' g)` over `(U ∩ U') \ U'`
  on the subspace where it converges weakly against smooth functionals, for a compatible
  quotient measure; Theorem IV.1.1 and target Levi covariance are not proved).
- `TorusNormKernelCompactnessStatement` (Worker 723): the Prop
  `TorusNormKernelCompactnessStatement` (compactness of the norm kernel of a torus), proved by
  `torusNormKernelCompactness` (`TorusNormKernelCompactnessProof`, Worker 1505, with the helper
  modules `TorusNormKernel/FieldNormCompact`, `TorusNormKernel/NormCharacter`,
  `TorusNormKernel/SplitCoordinates`); `torusNormKernelCompactness_of_centralNormKernelCompactness`
  (`TorusNormKernelCompactnessReduction`, Worker 723) derives it from the Prop
  `BruhatTits.RationalPoints.CentralNormKernelCompactnessStatement`, which is proved by
  `BruhatTits.RationalPoints.centralNormKernelCompactness` (`CentralNormKernelCompactnessProof`,
  Worker 1045, Worker 1532, with the helper modules in
  `Langlands/BruhatTits/RationalPoints/CentralNormKernel`; for connected reductive `G`, the center
  of `G(F)` meets `G^1` in a compact set; I.1).
- `RationalNormKernelCentralCover`: `isCompact_rationalCommonNormKernel_inf_center` (`G^1 ∩ Z(G(F))`
  is compact for connected reductive `G`), `isCompact_rationalNormKernel_centralDoubleCover`
  (compact preimages of finite unions of double Cartan charts with central factors).
  `RationalNormKernelCompactOpenTransport` (Worker 485): `rationalNormKernelAmbientLevel` (the
  image of an open subgroup of the norm kernel, as an open subgroup of `G(F)`), and
  `isCompact_rationalNormKernelAmbientLevel` (the image is compact when the given open subgroup is
  compact, an explicit premise `hK`; an arbitrary open subgroup of `G^1` need not be compact).
  `RationalNormKernelResidualCover`: `exists_rationalNormKernel_residual_cover` (restriction of a
  supplied central Cartan cover to the norm kernel).
- `FormalDegreeComparisons`, `DiscreteSeriesFormalDegree`, `FormalDegreeHaarScaling` (Worker 200):
  the formal degree of an actual irreducible representation and of discrete-series classes and
  orbits, with its invariances and Haar scaling; see the row III.1 (2), (3).
- `CompactNormalizedInductionDuality`, `CompactProductInducedCoefficients`,
  `CompactProductCoefficientBounds` (Worker 200) and `CompactCoefficientHaarComparison` (Worker 200
  with Worker 249): `CompactInduction.measure`, `integralDualEquiv` (the duality of normalized
  induction with the pairing normalized by Haar probability on a compact open subgroup),
  `CompactInduction.coefficientMap`, `coefficientMap_integral`, `range_coefficientMap` (the
  coefficients of normalized induction as an integral over that subgroup, I.3 and V.1),
  `coefficientTensorMap_bound`, `integrand_bound_levi` (bounds of the proof of VI.2.2),
  `CompactInduction.measure_eq_normalizedHaar`, `coefficientMap_eq_sphericalCoefficientIntegral`;
  see the row Lemmes VI.2.1–VI.2.3.
- `RationalModerateGrowthStatement`, `CoefficientGrowthUniformizationStatement`: Cor. I.4.4 as
  Props; `CoefficientGrowthUniformizationProof`, `RationalModerateGrowthUniformization`
  (Worker 1564), `RationalMatrixNormComparisonStatement`,
  `RationalCompactLatticePolynomialBoundStatement`: its finite-length step and intermediate Props;
  `RationalCoefficientModerateGrowthAssemblyStatement`, `RationalCoefficientModerateGrowthAssemblyProof`,
  `RationalMatrixNormComparison`, `RationalCompactLatticePolynomialBoundProof`,
  `RationalUniformizerCoordinateHeightStatement`, `RationalUniformizerCoordinateHeightProof`,
  `RationalFiniteChartModerateGrowthStatement`, `RationalFiniteChartModerateGrowthProof`,
  `RationalFiniteSignedCartanCoverStatement`, `RationalFiniteSignedCartanCoverProof`: the
  coefficientwise step from two structural Props and the proofs of its intermediate Props;
  see that row.
- `CoefficientTensorForm` (Worker 200), `CompactInducedHermitianForm`, `InducedTensorForm`,
  `FormalDegreeInducedTensorForm`: invariant positive forms on coefficient tensors and on induced
  representations and their tensors, `coefficientTensorInvariantForm`,
  `CompactInduction.invariantPositiveForm`, `normalizedInducedDualTensorForm`,
  `formalDegreeInducedTensorForm` (the product on `L(ω,P)` of V.2); see the row V.2.
  `DiscreteSeriesOrbitHaarScaling`: `discreteSeriesOrbitHaarScalingEquiv`,
  `discreteSeriesOrbitFormalDegree_smul_measure`; see the row III.1 (2), (3).
- `CoefficientTensorFormTransport`, `CompactInducedTensorForm`, `CompactInducedDualIsometry`,
  `CompactProductInducedForm`, `CompactProductIntegralFormula`, `CompactProductFormTransport`,
  `FixedCompactProductForm`, `FormalDegreeFixedCompactForm`, `ProductCompactTwistForm`,
  `FiniteSmoothFamilyForm`, `ProductInducedSmoothFamilyForm`, `ProductInducedOrbitForm`,
  `ProductInducedOrbitFormBaseChange`: the form of V.2 on the compact pictures and on
  `L(ω,P)`, its compatibility with the identifications of VI.1, and positive integral
  pairings of smooth families and on orbits; see the rows V.2, VI.1, VI.3 and VII.2.
- `StandardIntertwiningScalarDomain`, `StandardIntertwiningScalarBounds`,
  `StandardIntertwiningTwistBounds`, `CompactIntertwiningParameterContinuity`: reductions of the
  convergence of the standard integral; see the row Thm IV.1.1.
- `UnramifiedNormalizedModels`, `UnramifiedNormalizedTensorModels` (Worker 1585),
  `RationalUnramifiedFunctionField` (Worker 1615), `RationalUnramifiedFactorization`,
  `RationalUnramifiedDensity`, `RationalUnramifiedLocalDivisibilityStatement`: smooth
  `B`-linear models over the algebra `B` of unramified regular functions and properties of `B`
  (the finite projectivity of compact-open invariants required of a `B`-family in I.5 is not
  proved); see the rows I.5 and Thm IV.1.1.
- `ParabolicIntertwiningElementaryStatement`, `ParabolicIntertwiningElementaryProof`,
  `ParabolicRadicalUnimodularity`, `ParabolicIntertwiningTopology`,
  `StandardIntertwiningFullDomainTransport`, `StandardIntertwiningSourceFactors`,
  `StandardIntertwiningSourceQuotients`, `StandardIntertwiningSourceComposition`,
  `StandardIntertwiningCoveredSourceComposition`, `StandardIntertwiningDynamicSource`,
  `UnramifiedTensorMaps`, `UnramifiedUniversalTwist` (Worker 1615), `PolynomialIsolation`
  (Worker 1615): supporting results for `ConditionalParabolicIntertwiningStatement` and for
  IV.1 (12); see the rows Thm IV.1.1 and IV.1 (10)–(14).
- `CompactInductionGeneration`, `CompactIntertwiningCompression`,
  `CompactIntertwiningUniformNumerator`, `ParabolicPointUniformNumerator`,
  `ParabolicIntertwiningAssembly`, `StandardIntertwiningTruncation`, `UnramifiedStableLimit`
  (Worker 1615), `CompactIntertwiningWeakRegularity`, `RationalUnramifiedScalarCancellation`,
  `RationalUnramifiedVectorCancellation`, `RationalUnramifiedLocalDivisibilityProof`
  (Worker 1664): rationality of the standard compact operator from convergence and local
  domination, for `ConditionalParabolicIntertwiningStatement`; see the row Thm IV.1.1.
  `UnramifiedNormalizedSpecialization`, `UnramifiedNormalizedNaturality` (Worker 1585),
  `UnramifiedRationalNormalizedModels`, `UnramifiedRationalNormalizedSpecialization`
  (Worker 16, with Worker 1585): specialization of the smooth `B`-linear models at a
  character and its naturality, on actual rational points; no finiteness or fiber
  isomorphism is asserted; see the rows I.5 and IV.1.

Modules of the same directory published after commit `81bddf38` (the author is named where the
module's Markdown names one):

- `DiscreteSeriesCentralCharacter` (Worker 200): `discreteSeriesCentralCharacter`,
  `discreteSeriesCentralRestriction` (the actual unitary central character of a discrete-series
  class and its restriction to a central subgroup); see the row Prop. VII.2.1.
- `ProductInducedOrbitCoefficients`, `ProductInducedOrbitCoefficientSmoothness` (Worker 200):
  `unitaryOrbitCoefficientMap` (`E_P^G ψ_ω` for `ψ ∈ C^∞(O,P)`),
  `isSmoothFiniteTorusFunction_unitaryOrbitCoefficient`, `continuous_unitaryOrbitCoefficient`
  (Lemma VI.2.1 (i)); see the row Lemmes VI.2.1–VI.2.3.
- `ProductInducedOrbitFullAction`, `ProductInducedOrbitCompactAction`,
  `ProductInducedOrbitBaseAction`, `ProductInducedOrbitCoordinateAction`,
  `ProductInducedOrbitFormCoordinates` (Worker 200): the actions of `G × G` and `K × K` on
  `C^∞(O,P)`, their invariant positive forms, and their independence of the base point and of
  the lattice coordinates; see the row VI.1.
- `UnitaryUnramifiedSmoothEvaluation`, `FiniteSmoothCompactEvaluation`:
  `HasLaurentUnitaryCoordinates`, `unitaryUnramifiedSmoothEvaluation`,
  `mem_finiteSmoothFamilies_of_common_open_stabilizer`; see the row VI.1.
- `RationalDynamicSourceHaar`, `RationalSourceGammaAmbientHaar`, `RationalSourceGammaIntegral`,
  `RationalSourceGammaGlobal`, `RationalSourceGammaConjugation`,
  `RationalSourceGammaIndex`, `RationalSourceGammaOpposite`, `RationalSourceCompactComparison`,
  `RationalSourceIwasawaIntegration`, `RationalSourceIwasawaBochner`,
  `RationalSourceOpenCellCoordinates`,
  `RationalSourceOpenCellBochner`, `SemidirectSourceGamma`, `SemidirectSourceGammaIntegral`,
  `SemidirectSourceHaarNormalization`, `SourceGammaTransport`,
  `RationalOpenCellConullStatement`, `RationalOpenCellConullProof` (Worker 200 for the
  statement), `RationalOpenCellBoundaryStatement` (Worker 135), `RationalOpenCellBoundaryProof`:
  the Haar measures normalized on one compact open subgroup, `γ`, the conullness of the open
  cell, the integration formulas (2) of I.1 and steps of the proof of Remark (3) on actual
  rational points; see the row I.1.
- `UnramifiedRationalNormalizedInducedFiniteness` (Worker 1761),
  `RationalNormalizedInducedSpecializationStatement` (Worker 1759): the Props
  `UniversalInducedCoefficientFinitenessStatement` (flatness and finite projectivity of
  compact-open invariants of the rational universal induced model) and
  `RationalNormalizedInducedSpecializationStatement` (bijectivity of its specialization at a
  character), from Renard VI.8.1–VI.8.2, both proved after commit `f36ed55e` (see below and the
  rows I.5 and IV.1).
- `CompactIntegralSaturation`, `ParabolicIntertwiningReduction` (Worker 1615),
  `CompactIntertwiningQuotientDecay`, `ParabolicOppositeQuotient`,
  `ParabolicIntertwiningConeReduction`, `ParabolicIntertwiningCharacterDecay`,
  `ParabolicIntertwiningDecayAssembly`, `ParabolicSquaredModulusReduction`,
  `ParabolicLeviModerateGrowth`, `ParabolicLeviLogarithmBounds`, `ParabolicRootCone`,
  `SplitComponentLogarithm`, `ParabolicCharacterDecayProof`: the derivation of
  `ConditionalParabolicIntertwiningStatement` from three unproved Props; see the row
  Thm IV.1.1.

Modules of the same directory published after commit `f36ed55e` (the author is named where the
module's Markdown names one):

- `RationalSourceGammaChoice`, `RationalSourceHaarConjugation`: independence of `γ` of the
  cocharacter describing the same dynamic subgroups and conjugation of the compact-normalized
  subgroup Haar measures; `RationalSourceIntegration`, `RationalSourceNormalization` (Worker
  200): modules that only import the source integration and normalization modules together; see
  the row I.1.
- `UnramifiedRationalNormalizedInducedFinitenessProof` (Workers 1754 and 1582),
  `RationalNormalizedInducedSpecializationProof` (Worker 1635),
  `RationalUniversalTensorFinitenessStatement` (Worker 1759),
  `RationalUniversalTensorFinitenessProof` (Worker 1780): proofs of the two Props of Renard
  VI.8.1–VI.8.2 listed above and of the analogous Prop for the universal twist `B ⊗ E`;
  `UnramifiedRationalCoefficientAlgebra` (Worker 1755), `UnramifiedRationalConjugateAdmissibility`,
  `UnramifiedRationalCompressionSpecialization`, `UnramifiedRationalCompactSpecialization`,
  `UnramifiedJacquetScalarExtension` (Worker 1759), `RationalParabolicCuspidality` (Worker 1780),
  `UnramifiedRationalJacquetFinitenessStatement` (Workers 1775 and 1780; the unproved Prop
  `RationalSupercuspidalJacquetFamilyFiniteStatement`, Renard VI.9.2),
  `UnramifiedCompressionCriterion` (Worker 1755), `UnramifiedRationalFamilyCompression`,
  `UnramifiedRationalDynamicCompression`, `RationalInducedGeneratorComparison`,
  `RationalInducedGeneratorCompression`, `RationalCuspidalInductionCompression` (Worker 1751):
  the universal unramified families of actual rational Levis, their Jacquet modules and compact
  compression (Renard VI.8–VI.9): one exponent for all specializations of one family
  (`UnramifiedRationalFamilyCompression`, given native finiteness and bijective specializations),
  and eventual stability for the induction of each cuspidal object
  (`RationalCuspidalInductionCompression`, given the whole inertia decomposition, finiteness of
  inertia classes at each level, the norm-kernel small-progenerator property, admissibility and
  native Jacquet finiteness of the irreducible cuspidal representatives); see the row I.5.
- `RationalUnramifiedOperatorContinuation`, `RationalUnramifiedIntertwiningContinuation`,
  `CompactInductionPolynomialAction`, `CompactIntertwiningContinuation`,
  `ContinuedIntertwiningNaturality`, `CompactIntertwiningBaseChange`,
  `UnramifiedOperatorTranslation`: continuation of rational operator families on the unramified
  characters and on the actual normalized induction spaces; see the row IV.1.
- `RationalUnramifiedScalarContinuation`, `RationalUnramifiedScalarField`,
  `UnramifiedScalarTranslation`, `CompactIntertwiningScalar`, `ContinuedIntertwiningScalar`,
  `ContinuedIntertwiningScalarNaturality`: the rational scalar of the composite of two
  intertwiner families; see the row IV.3.
- `ParabolicGenericIrreducibilityStatement`, `FiniteMatrixOpennessStatement`,
  `FiniteMatrixOpennessProof`: the unproved Prop
  `ConditionalParabolicGenericIrreducibilityStatement`, and
  `FiniteMatrixIrreducibilityOpennessStatement` with its proof
  `finiteMatrixIrreducibilityOpenness`; see the row Prop. IV.2.2.
- `RationalInertiaBlockCompression` (Worker 1751), `UnramifiedRationalJacquetSupport`: one
  compression threshold for all objects of the induced inertia block of one fixed representative
  (given its norm-kernel small-progenerator property, its admissibility and native Jacquet
  finiteness), and the support filtration of the Jacquet modules of the universal induced family;
  see the row I.5.

Namespace `Langlands.GroupScheme`, module
`Langlands/GroupScheme/Rational/PointTopology` (Worker 200):
`rationalPointsAffineHomeomorph` (the published rational-point topology agrees
with the evaluation topology on affine points) and
`rationalCharacterContinuousEval`, evaluation of an actual rational character
as a continuous homomorphism on rational points with that topology (I.1,
p.239).

Namespace `Langlands.HarishChandraSchwartz` (Worker 249), module directory
`Langlands/HarmonicAnalysis/HarishChandraSchwartz/`:

- `Basic`: `IsBiInvariant`, `weight`, `nu`, `levelSubmodule`,
  `schwartzSubmodule`, `Level`, `Space` with its inductive-limit topology
  `Space.topologicalSpace`, `Space.t2Space`, `Space.continuous_toFunLinear`
  (III.6 for arbitrary weights `Ξ`, `σ`; III.6 (1)).
- `Height`: `glNorm`, `height` (`σ = log‖τ(·)‖` for a supplied
  `τ : G →* GL_n(F)`), `height_mul_le`, `one_add_height_le`,
  `isCompact_height_le` (I.1, the norm and `σ`).
- `Spherical`: `IsIwasawaPair`, `iwasawaWeight`, `xi`, `xi_mul_mul`,
  `continuous_xi`, `integral_xi_mul_mul` (II.1 and Lemma II.1.3 from a
  supplied factorization `G = P K` and a positive character of `P`).
  Its Markdown records II.1.1, II.1.2, II.1.4, II.1.5 and the comparison of
  the integral formula with the matrix coefficient `⟨π(g)e, e⟩` as open
  proof obligations.
- `TestFunctions`: `ofSchwartzBruhat`, `denseRange_ofSchwartzBruhat` (the
  inclusion `C_c^∞(G) → C(G)` and its density, III.6, under explicit
  hypotheses on the weights).
- `Translations`: `Space.translate`, `Space.continuous_translate` (the
  continuous action of `G × G` on `C(G)`, III.6, with II.1.2 as an explicit
  hypothesis).
- `SphericalInverse`: `compactAverage`, `inducedPairing` (the functional of I.1
  and the pairing of I.3 on `I_P^G 1`, written as averages over `K`; their
  agreement with Waldspurger's quotient integrals is not proved), and `xi_inv`
  (Lemma II.1.4) when `G` is unimodular and `δ` is the modular character of a
  closed `P`. Both are explicit hypotheses.
- `Convolution`: `ConvolutionWeights`, `convolution` (an alias of
  `Hecke.convolutionIntegral`), `Space.convolution`,
  `Space.continuous_convolution_left`, `Space.continuous_convolution_right`
  (Lemma III.6.1: absolute convergence, closure of `C(G)` and separate
  continuity, with II.1.3, II.1.4 and II.1.5 as fields of `ConvolutionWeights`).
- `L2`: `check` (`f̌`), `pairing` (`(f_1, f_2)_G` of VII.1), `Space.check`,
  `Space.toL2`, `Space.inner_toL2` (VII.1, and the derived inclusion
  `C(G) ⊆ L^2(G)`).
- `SquareIntegrability`: `SquareIntegrableWeight` (the conclusion of Lemma
  II.1.5, `∫_G Ξ^2 (1+σ)^{-d} < ∞` for some `d`), `CartanSquareBound` and
  `CartanSquareBound.squareIntegrableWeight` (its proof from bounds that
  collect I.1 (4), the upper bound of I.1 (5), the lower bound of I.1 (6) and
  the upper bound of Lemma II.1.1, for countably many abstract cells covering
  `G` with an injective map `H` into a discrete subgroup of a
  finite-dimensional real normed space). Those bounds are hypotheses; they are
  not proved for an actual reductive group.
- `SphericalLevi`: `leviComponent`, `LeviData`, `LeviData.xi_eq_integral`
  (Lemma II.1.6 for `xi` and the function `Ξ^M` built in the same way on `M`,
  from a supplied Levi projection `P → M` and characters `δ_P`, `δ_0^M` with
  `δ_0 = δ_0^M δ_P` as hypotheses).
- `SphericalTranslation`: `UniformTranslationBound`,
  `xi_uniformTranslationBound` (Lemma II.1.2 for `xi` with `d = 0`),
  `xi_translationWeights`, `xi_convolutionWeights` (the hypotheses of
  `Translations` and `Convolution` for `xi`, the last one with Lemma II.1.5 as
  a hypothesis).
- `ConstantTerm`: `constantTerm` (`f^{(P)}` of III.6), `ConstantTermEstimate`
  (the estimate of Proposition II.4.5 for `P̄`, as a hypothesis),
  `ConstantTermData`, `Space.constantTerm` (the continuous linear map
  `C(G) → C(M)`).
- `ConstantTermInd`: `constantTermInd` (`f^{(P),Ind}` of III.6), its
  `G × G`-equivariance and transformation law, `IsConjModulus`,
  `isConjModulus_restrictCharacter` (the bridge to the Library's Haar modulus
  `HaarModulus.restrictCharacter`), `TransitivityData` and
  `TransitivityData.constantTermInd_constantTermInd` (the diagram of III.6,
  proved pointwise; the induced space `I_{P×P}^{G×G} C(M)` is not constructed).
- `Completeness`: `Space.completeSpace`, `Space.completeSpace_of_firstCountable`
  (`C(G)` is complete, III.6 via [B], when `G` has a sequence of compact open
  subgroups such that every compact open subgroup contains one of them; the
  second form takes `G` nonarchimedean, weakly locally compact and first
  countable).
- `ConstantTermBound`: `constantTermEstimate_of_bounds` (Proposition II.4.5: the
  Prop `ConstantTermEstimate` from Lemma II.4.4, the second inequality of II.3.1, the
  lower bound of II.1.1 for `M`, Lemma II.4.2 and the covering `M = K_M S K_M`, all as
  hypotheses), `IsConjModulus.lintegral_comp`.
- `SphericalBounds`: `xiLowerBound_of_factorization` (lower bound of Lemma II.1.1 from an
  Iwahori-type factorization), `XiUpperBound` and `CartanWeightComparison` (Props: the
  upper bound of II.1.1 on a cone and the comparison of II.3.2), `XiUpperBound.univ_of_cartan`,
  `XiUpperBound.unipotentXiBound` (Lemma II.4.4), `LevelSetMeasureBound`,
  `LevelHeightComparison`, `unipotentWeightIntegrable_of_levelSets` (Lemma II.4.2).
- `TauEstimates`: `cartanWeightComparison_of_norm` (Lemma II.3.2), `conj_height_le_of_tau`
  (Lemma II.3.3), `ModulusHeightBounds`, `modulusHeightBounds_of_tau` (Lemma II.3.4), from
  properties of `τ_P` (II.2) as hypotheses.
- `SigmaProduct`: `IsBlockDiagonal`, `IsBlockUnipotent`, `sigmaProductBound_height`
  (Lemma II.3.1 for `σ = height τ` when `τ(M)` and `τ(U)` have block form after
  conjugation).
- `LevelSetBound`: `TorusXiFormula` (formula (2) of the proof of II.4.1, as a Prop),
  `levelSetMeasureBound_of_torusXiFormula` (Lemma II.4.1).
- `LeviWeightIntegrability`: `leviXiWeight`, `LeviData.unipotentWeightIntegrable`
  (Lemma II.4.3 from Lemma II.4.2).
- `IwasawaIntegration`: `leviUnipotentShift`, `lintegral_eq_lintegral_levi_unipotent`,
  `lintegral_eq_lintegral_unipotent_levi` (I.1 (2), first formula, from `G = M U K`, the
  decomposition of `P ∩ K`, the normalizations and `IsConjModulus`; it applies
  `CompactFactorization.lintegral_restrict_lintegral_mul` of
  `Langlands/Analysis/Local/CompactFactorizationIntegral`, Worker 235). The second
  formula of (2) is in `OpenCellIntegration` and `ParabolicHaar`.
- `TemperedPairing`: `HasTemperedGrowth`, `IsTemperedSmooth`, `Space.temperedPairing`
  (the continuous functional `f ↦ ∫ f φ` on `C(G)` for `φ` of tempered growth; III.2,
  III.7).
- `ConjugationBound`: `ConjugationSigmaBound` (inequality (2) of the proof of VIII.3.1, as a
  Prop), `ConvolutionWeights.lintegral_conj_mul_le` (inequality (3)).
- `CuspidalDecay`: `cuspidalFactor`, `unipotentFactor`, `lintegral_cuspidal_le` (the
  estimate of `J(a)`), `ConjugationIntegralBound` (the conclusion of VIII.3.1, as a Prop, on a supplied set `T`;
  the source takes `T = Ā_0^+ ∩ G^1`),
  `conjugationIntegralBound_of_split` (VIII.3.1 from the decomposition of the integral and
  the two estimates).
- `CuspidalIntegrability`: `conjFun`, `lintegral_lt_top_of_conjugationIntegralBound`
  (Corollary VIII.3.2 from a cover of `A_G\G` by cells, finiteness of the conjugates of
  `f_1`, `f_2`, the measure bound of I.1 (5) and summability, as hypotheses).
- `CentralProjection`: `CentralWeights`, `IsUnitaryCharacter`, `centralProjection`,
  `Space.centralProjection` (`p_χ` of VIII.4: absolute convergence, `χ`-covariance,
  bi-invariance for central `A`), `enorm_centralProjection_le_rpow_neg` (the estimate on
  `G^1` in the proof of VIII.4.1).
- `DoubleCosetMeasure`: `doubleCosetIndex`, `measure_doubleCoset`
  (`μ(HgH) = [H : H ∩ gHg^{-1}] μ(H)`), `measure_doubleCoset_le_of_doubleCosetIndex`
  (I.1 (5) from bounds on the index), `relIndex_mul_modulus` (the identity
  `c_{U_0}(m) = δ_0(m)^{-1} c'_{U_0}(m)` of the proof of (5)).
- `OpenCellIntegration`: `openCellMap`, `openCellConstant` (`γ`), `exists_lintegral_openCellMap`,
  `lintegral_eq_openCellConstant_inv_mul` (I.1 (2), second formula, in the coordinates
  `(p, v) ↦ p v^{-1}` with a Haar measure of `P`, and `0 < γ < ∞`, by uniqueness of Haar
  measure on `P × Ū`), `openCellConstant_eq_lintegral` (`γ = ∫_Ū δ_P(m_P(ū)) dū` from the
  right translation law of the measure of `P`); the open-cell embedding, its conull image
  and the right invariance of the Haar measure of `G` are hypotheses.
- `ParabolicHaar`: `leviUnipotentCoord`, `leviUnipotentMeasure` (`dm du` on `P = M U`),
  `leviUnipotentMeasure_isMulLeftInvariant`, `leviUnipotentMeasure_isHaarMeasure` (a left
  Haar measure of `P` when `(m, u) ↦ m u` is a homeomorphism onto `P`),
  `map_mul_right_leviUnipotentMeasure` (right translation by `m_0 u_0` multiplies it by
  `δ_P(m_0)`), `lintegral_levi_unipotent_eq` (the order `u m` with `δ_P(m)^{-1}`),
  `lintegral_eq_openCell_levi_unipotent` (I.1 (2), second formula, as
  `∫_G F = μ(K) γ^{-1} ∫_M ∫_U ∫_V F(m u v^{-1})`), `openCellConstant_leviUnipotentMeasure`,
  `measure_eq_of_openCell_factor` and `openCellConstant_eq_relIndex_mul` (the index
  expression of `γ(P)` in the proof of Remark (3), from a factorized compact open subgroup
  `H`). The decomposition of `P ∩ K`, the modulus relations, the factorization of `H` and the
  open-cell data are hypotheses; Remark (3) itself is not formalized.
- `CuspidalSplit`: `integral_eq_smul_integral_openCellCoord` (the Bochner form of the
  open-cell formula), `integral_conj_mul_eq_split` (the decomposition of
  `∫_G f_1(a g a^{-1}) f_2(g) dg` into the integral over `S(a)` and `J(a)` in the proof of
  VIII.3.1, which is the decomposition hypothesis of `conjugationIntegralBound_of_split`),
  `conjugationIntegralBound_of_openCell` (VIII.3.1 from the open-cell data and the estimates
  (3) and `J(a)`, as hypotheses).
- `OpenCellLemma`: `OpenCellBound` (the conclusion of Lemma II.3.5, as a Prop),
  `mem_of_coordinate_bounds`, `mem_mul_of_dense`, `openCellBound_of_mul` (the three steps
  of II.3.5), `conjugationSigmaBound_of_openCellBound` (inequality (2) of VIII.3.1). The
  decomposition `G = K P_0`, Lemma II.3.3, the density of `Ū P` and the closedness of `Γ̄ P`
  are among its hypotheses.
- `ReproducingKernel`: `IsReproducingKernel`, `IsReproducingKernel.finiteDimensional`,
  `IsReproducingKernel.finrank_le`, `IsReproducingKernel.span_kernel_eq_top`,
  `IsReproducingKernel.kernel_eq_sum` (the functional-analytic step of the proof of
  VIII.4.1: a space of functions in `L^2` with a reproducing kernel whose diagonal is
  integrable is finite dimensional and spanned by the kernel), `eq_zero_of_covariant` and
  `centralProjection_eq_zero_of_ne_one` (the reduction to `χ` trivial on `A_G ∩ H`). The
  application to `p_χ(°C_H)` with the measure of `A_G\G` is open.
- `OpenCellPoints`: `isOpenEmbedding_openCellMap_rationalPoint` (the hypothesis `hι` of
  `OpenCellIntegration`: `(p, v) ↦ p v^{-1}` is an open embedding
  `P_G(χ)(k) × U_G(χ^{-1})(k) → G(k)` for a smooth affine group scheme `G` and a cocharacter
  `χ`), `isHomeomorph_leviUnipotentMul_rationalPoint` and
  `isHomeomorph_leviUnipotentCoord_rationalPoint` (the hypothesis `hhomeo` of
  `ParabolicHaar`: `(m, u) ↦ m u` is a homeomorphism `Z_G(χ)(k) × U_G(χ)(k) → P_G(χ)(k)`
  for `G` affine and locally of finite type), over a topological field `k` with open units
  and the published rational-point topology (I.1 (2)). This module does not contain the
  Haar-nullness of the complement of the open cell; for connected reductive `G` it is
  `rationalDynamicOpenCellConull` (`RationalOpenCellConullProof`; see the row I.1 and the
  module entry above that lists `RationalOpenCellConullProof`). The identification of Waldspurger's
  `P = M U` with `P_G(χ) = Z_G(χ) U_G(χ)` is not proved.
- `SchwartzAction`: `HasTemperedCoefficients`, `coefficientPairing`, `schwartzAction`,
  `schwartzAction_eval`, `schwartzAction_eq_of_hasIntegral`, `continuous_schwartzAction_eval`,
  `schwartzAction_mem_finiteRankEnd`, `levelAction`, `schwartzCharacter`,
  `schwartzAction_ofSchwartzBruhat` (III.7, first paragraph: the weak integral
  `π(f) v = ∫_G f(g) π(g) v dg` for `f ∈ C(G)`, its finite rank and the continuous
  character `θ_π`, for an admissible representation whose coefficients have tempered growth,
  with `L2Weights` for the weights, a left invariant measure and a compact open subgroup).
- `SchwartzActionConvolution`: `convolutionIntegrand`,
  `ConvolutionWeights.integral_convolution_mul`, `schwartzAction_convolution`
  (`π(f_1 * f_2) = π(f_1) π(f_2)`, III.7, with the weight hypotheses `ConvolutionWeights` of
  `Convolution`, second countability of `G` and an s-finite measure),
  `schwartzAction_translate_left`, `schwartzAction_translate_right` (the last with a right
  invariant measure as hypothesis).
- `CoefficientCutoff`: `IsRapidlyDecreasingOn`, `HasRapidlyDecreasingCoefficientsOn` (the
  conclusion of Cor. III.1.2 for pure coefficients on a supplied subgroup `N`, as a Prop;
  Cor. III.1.2 implies it for `N = G^1`),
  `TranslationWeights.mul_mem_levelSubmodule`, `TranslationWeights.mul_mem_schwartzSubmodule`
  (III.7, second paragraph: `f φ ∈ C(G)` for `f ∈ A(ω)` and `φ ∈ C_c(G/N)`, with an open
  normal subgroup `N` in place of `G^1` and `HasRapidlyDecreasingCoefficientsOn` as a
  hypothesis).
- `SchwartzActionFamily`: `Space.normalizedIndicator` (`ε_H` in `C(G)`),
  `schwartzAction_normalizedIndicator`, `schwartzAction_intertwining`,
  `schwartzAction_translate_conj`, `IdempotentFamily` (a family `H ↦ φ_H` in `C(G)` with
  properties (1) and (2) of the proof of Prop. III.7.1), `IdempotentFamily.operator` (`π[φ]`
  in `End_G(V)`), `IdempotentFamily.operator_intertwining` (its naturality in `π`); a Haar
  measure that is also right invariant is a hypothesis of the last two.
- `AdmissibleFitting`: `fittingRange`, `fittingKernel`, `isCompl_fittingRange_fittingKernel`,
  `bijOn_fittingRange` (proof of Cor. III.7.2: for an intertwiner `T` of an admissible
  representation, the subrepresentations `⋂_n T^n V` and `⋃_n Ker T^n` have complementary
  underlying subspaces and `T` is bijective on the first, given that every open subgroup
  contains a compact open one). Cor. III.7.2 is in `OrbitPolynomialOperator` below.
- `TraceCoefficientFamily`: `averageProjection`, `traceCoefficient` (`ψ_H(g)`, the trace of the
  compressed action of `g` on `V^H`), `traceCoefficient_conj`, `traceCoefficient_mem_range`,
  `finiteRankTrace_eq_traceCoefficient`, `integral_normalizedIndicator_mul_traceCoefficient`,
  `traceCutoff` (`φ_H = φ ψ_H` in `C(G)`), `traceFamily` (an `IdempotentFamily`),
  `traceFamily_operator_eval` (proof of Prop. III.7.1: the family `φ_H` and the first displayed
  equality for `π[φ]`; with an open normal subgroup `N` in place of `G^1` such that conjugation
  is trivial on `G/N` and every compact open subgroup lies in `N`, Cor. III.1.2 as the
  hypothesis `HasRapidlyDecreasingCoefficientsOn`, and a right invariant Haar measure).
  Prop. III.7.1 is in `OrbitPolynomialOperator` below.
- `SchurOrthogonality`: `orthogonalityIntegrand`, `orthogonalityIntegral`,
  `orthogonalityIntegral_eq_zero_of_integrable`, `orthogonalityIntegral_eq_zero` (III.1 (2)),
  `invariantForm`, `invariantPositiveForm`, `isUnitarizable_of_isSquareIntegrable` (Lemma III.1.3
  for irreducible representations), `exists_formalDegree`, `formalDegree`, `formalDegree_pos`,
  `formalDegree_unique`, `orthogonalityIntegral_eq_formalDegree` (III.1 (3)), for
  representations on which a normal central subgroup `A` acts by one character, with a Haar
  measure on `G ⧸ A` invariant under inversion and the premise `hcof` as hypotheses.
- `TraceOrthogonality`: `traceCoefficient_smoothContragredient`,
  `traceOrthogonalityIntegrand`, `integral_traceOrthogonalityIntegrand`,
  `integral_traceOrthogonalityIntegrand_eq_zero`,
  `integral_traceOrthogonalityIntegrand_eq_formalDegree`,
  `integral_traceOrthogonalityIntegrand_eq_formalDegree_of_mem` (the Schur step of the proof of
  Prop. III.7.1, printed pp.274–275, for `ω` in place of `ω ⊗ χ`; the integrability for
  tempered `π` is a hypothesis of the vanishing case).
- `TraceFamilyScalar`, `OrbitPolynomialOperator`, `TemperedTwistIntegrability`,
  `QuotientMeasureCompatibility` (Worker 249):
  the computation of `π[φ]`, Prop. III.7.1, Cor. III.7.2 and the consequences of temperedness
  used in their proofs, and the existence of the constant of the measure compatibility
  `hcompat`, in the abstract setting described in the row III.7 (a surjective `p : G →* Λ`
  with open kernel for `G → G/G^1`, a central `A` for `A_G`); see the rows III.1 (2), (3)
  and III.7 for the declarations and the hypotheses.
- `AdmissibleCoefficientSpace`, `AdmissibleCoefficientSpaceLeft` (Worker 249): Lemma I.6.1 for
  right and for left translation and Lemma III.2.1 in a generic setting; see the rows I.6 and
  III.2.
- `InducedTemperedCoefficients` (Worker 249): Lemma III.2.3 for normalized induction in the
  setting of `InducedCoefficientXi`; see the row III.2.
- `SquareIntegrableSemisimplicity`: `IsSquareIntegrableModCentralSubgroup.of_injective`,
  `IsSquareIntegrableModCentralSubgroup.smoothContragredient`, `dualInvariantForm`,
  `isUnitarizable_smoothContragredient_of_admissible`,
  `isSemisimpleRepresentation_of_isSquareIntegrable`, `isUnitarizable_of_isInternal`,
  `isUnitarizable_of_isSquareIntegrableModCentralSubgroup` (Lemma III.1.3: an admissible
  representation that is square integrable modulo a normal central subgroup `A` is unitary and
  semisimple, without irreducibility; in the setting of `SchurOrthogonality`, with a Haar
  measure on `G ⧸ A` invariant under inversion and the premise `hcof`).
- `InducedCoefficientBound`: `compactIntegral`, `LeviData.norm_compactIntegral_le_xi`,
  `LeviData.norm_compactIntegral_le_xi_uniform` (the analytic core of Lemma VI.2.2:
  `|∫_K Φ(k, k g) dk| ≤ C Ξ(g)` when `|Φ(k, x)| ≤ C δ_P(m_P(x))^{1/2} Ξ^M(m_P(x))`, via
  `LeviData.xi_eq_integral`).
- `InducedCoefficientXi`: `inducedIntegrandKernel`, `norm_inducedIntegrandKernel_le`,
  `norm_coefficientMap_le_xi` (Lemma VI.2.2 for one `ω`: the coefficients
  `CompactInduction.coefficientMap` of the normalized induced representation, on Worker 200's
  product-induced coefficient space, satisfy `|E_P^G ψ(g)| ≤ C Ξ(g)`; the conclusion of
  Cor. III.1.2 for `M` is the hypothesis `hcoeff`, and `G = P K`, unimodularity of `G` and `U`,
  the modulus of `P` and the Iwasawa pairs are hypotheses). This module treats one `ω`; the
  bound uniform over the twists of `ω` is in `InducedCoefficientTwistXi`, the bound uniform
  over the orbit `O` for sections `ψ ∈ C^∞(O,P)` in `OrbitWavePacket`, and Lemma VI.2.1 (i)
  in `ProductInducedOrbitCoefficientSmoothness` (Worker 200); see the row Lemmes
  VI.2.1–VI.2.3. Lemma VI.2.1 (ii) and Lemma VI.2.3 are open.
- `SectionReproducingKernel`: `sectionForm`, `IsSectionReproducingKernel`,
  `IsSectionReproducingKernel.finiteDimensional`, `IsSectionReproducingKernel.finrank_le`,
  `IsSectionReproducingKernel.span_kernel_eq_top`, `IsSectionReproducingKernel.kernel_apply_eq_sum`
  (the reproducing-kernel step of the proof of Prop. VIII.4.1 for functions on `G` read on
  `A_G\G` through a section `s`: a space with a reproducing kernel `K` and integrable
  `Re K(s x)(s x)` is finite dimensional and spanned by the kernel).
- `KernelReproduction`: `kernelAlpha` (`α`), `kernelAlphaChi` (`α_χ = p_χ α(·, g₂)`),
  `kernelAlphaChi_eq`, `conj_kernelAlphaChi`, `integral_conj_kernelAlphaChi_mul` (formula (1)
  of the proof of VIII.4.1 on `G`: `∫_G conj(α_χ(g', g)) φ(g') dg' = (p_χ φ)(g)`; `φ * °e = mes(H) φ`
  and the absolute convergence of the triple integral are hypotheses).
- `KernelQuotient`: `integral_integral_out_eq`, `integral_centralProjection_mul_conj` (the Weil
  formula: `∫_{A\G} (p_χ φ)(q̇) conj(K(q̇)) dν = ∫_G conj(K) φ` for `χ`-covariant `K`, with a
  compatible quotient measure `ν`), `integral_centralProjection_mul_conj_kernelAlphaChi`,
  `IsKernelAlphaChiSpace`, `isSectionReproducingKernel_kernelAlphaChi`,
  `finiteDimensional_of_kernelAlphaChi` (formula (1) on `A_G\G` and the finiteness of
  VIII.4.1 given the integrability of the diagonal).
- `KernelDiagonal`: `productSet` (`A H`), `convolution_indicator_eq` (`φ * e = mes(H) φ` for
  right `H`-invariant `φ`), `convolution_eq_of_convolution_eq_indicator`, `integral_prod_mul_eq`
  (integration over `A H` as over `A × H`), `centralCharacterExtension` (`ψ̃`),
  `kernelAlphaChi_diag_eq` (the diagonal `α_χ(g, g)` as `∫_G E(g⁻¹ x g) ψ(x) dx` for `χ` trivial
  on `A ∩ H`), `integrable_re_kernelAlphaChi_diag` (integrability of the diagonal from a finite
  lower integral of the conjugation integrals). Lemma VIII.2.3 (`°e * φ = e * φ`) is a
  hypothesis.
- `KernelFiniteness`: `out_inv_mul_mul_out`, `lintegral_conj_out_lt_top` (Corollary VIII.3.2
  for the map `h ↦ A_G h⁻¹`), `diagonalWeightOn`, `finiteDimensional_of_conjugationIntegralBound`
  (Proposition VIII.4.1 assembled: `p_χ(°C_H)` is finite dimensional, from the kernel identities,
  Prop. VIII.3.1 for the finitely many conjugates involved, the cell cover and measure bounds of
  I.1 (4), (5) and summability, all as hypotheses; the construction of `°e`, `°C_H` and
  Lemma VIII.2.3 are open).
- `DiscreteCoefficientSpace`: `subrepresentationCoefficientSpace` (`Σ_S A(S)` over the
  subrepresentations `S` satisfying a predicate), `smoothCoefficient_mem_irreducible`,
  `formCoefficient_mem_irreducible`, `isSquareIntegrable_of_irreducible_subrepresentation`,
  `formCoefficient_mem_squareIntegrable`, `exists_mem_squareIntegrable_of_reproducing` (the
  inclusion `p_χ(°C(G)) ⊂ A_2(G)_χ` of the proof of Theorem VIII.4.2 in abstract form: in a
  semisimple smooth representation, every coefficient lies in the span of the coefficient spaces
  of its irreducible subrepresentations, which are square integrable when the representation is;
  the reproducing identity and square integrability of `V = p_χ(°C(H\G))` are hypotheses).
- `CentralCoefficientFormula`: `coefficientCorrelation`, `integral_conj_centralProjection_mul`,
  `integral_conj_centralProjection_mul_centralProjection` (formula (2) of the proof of
  Theorem VIII.4.2: `(f₁, ρ(g) f₂)_{A_G\G} = p_χ(ˇφ̄₁ * φ₂)(g)`), `indicator_convolution_eq`,
  `centralProjection_eq_inv_mul_integral` (the reproducing identity
  `f(g) = mes(H)⁻¹ (p_χ °e, ρ(g) f)_{A_G\G}`); Remark VIII.2.2, Lemma VIII.2.3 and the absolute
  convergence are hypotheses.
- `CoefficientIndependence`: `coefficientFunctionSpace` (`A(π)` as a subspace of `G → ℂ`),
  `iSupIndep_coefficientFunctionSpace` (the spaces `A(ω)` of pairwise inequivalent irreducible
  smooth representations are independent), `exists_isBiInvariant_coefficient_ne_zero`
  (`A(ω)^{H×H} ≠ 0` when `ω^H ≠ 0`), `finite_of_isBiInvariant_coefficient_mem` (the proof of
  Theorem VIII.1.2 in VIII.5, abstract form: a family of such representations whose
  `H`-bi-invariant coefficients lie in one finite-dimensional space is finite; the inclusion of
  Theorem VIII.4.2 and Prop. VIII.4.1 enter as that space).
- `CentralProjectionVanishing`: `pairingAnnihilator`, `integral_conj_inner_mul`,
  `subrepresentationCoefficientSpace_le`, `integrable_centralProjection_mul_conj`,
  `centralProjection_eq_zero_of_schwartzAction_eq_zero` (the end of the proof of Theorem VIII.1.1
  in abstract form: `p_χ φ = 0` when `p_χ φ` lies in the span of the coefficient spaces of
  subrepresentations `S` with `π_S(ˇφ) = 0`; the inclusion of Theorem VIII.4.2 is that
  hypothesis).
- `CentralFourierInversion`: `HasFGCompactOpenQuotients`, `cosetValues`,
  `hasSum_integral_quotient`, `eq_zero_of_integral_inv_character_mul_eq_zero`,
  `eq_zero_of_forall_centralProjection_eq_zero` (Fourier inversion on `A_G`: `f ∈ C(G)` with
  `p_χ f = 0` for every continuous unitary character `χ` of a closed central `A` with
  `HasFGCompactOpenQuotients A` is zero), from `eq_zero_of_characterSum_eq_zero`
  (`Langlands/HarmonicAnalysis/DiscreteFourierUniqueness`, uniqueness of Fourier coefficients on
  finitely generated commutative groups).
- `CentralQuotientGeneration`: `hasFGCompactOpenQuotients_of_isCompact`,
  `isCompact_rationalNormKernelPart`, `hasFGCompactOpenQuotients_rationalPoints`,
  `hasFGCompactOpenQuotients_splitComponent` (`A / (A ∩ K)` is finitely generated for every
  closed central subgroup `A` of `G(F)`, `G` connected reductive, and every compact open `K`;
  in particular for `A_G(F)`).
- `CentralProjectionFamily`: `Space.centralProjectionFamily`, `Space.centralProjectionFamily_injective`,
  `Space.eq_zero_of_forall_schwartzAction_eq_zero` (the family `(p_χ f)_{χ ∈ Â_G}` over the
  continuous unitary characters of `A`, its injectivity on `C(G)`, and the end of the proof of
  Theorem VIII.1.1 for all `χ` at once).
- `InducedCoefficientTwistXi`: `twistedSection`, `integrand_twist_bound`,
  `norm_twist_coefficientMap_le_xi`, `norm_family_coefficientMap_le_xi` (Lemma VI.2.2 uniformly
  over the unitary unramified twists of one `ω`, for a fixed compact section and for smooth
  families on a finite torus; the hypotheses of `InducedCoefficientXi`).
- `DiscreteSeriesOrbitFiniteness`: `characterAnnihilator`, `finite_image_mk_characterAnnihilator`,
  `classActsByCharacter`, `discreteSeriesCentralFixed`, `discreteSeriesFixedOrbits`,
  `finite_discreteSeriesFixedOrbits`, `finite_discreteSeriesFixedOrbits_of_coefficient_mem` (the
  reduction of Theorem VIII.1.2 in VIII.5 to the finiteness of the `E_2(G)^H_χ`, with the
  hypotheses listed in the row VIII.5).
- `UnramifiedCharacterExtension`: `exists_circle_character_extension`, `commonNormMap`,
  `exists_unitaryUnramifiedCharacter_restrict_eq`,
  `finite_discreteSeriesFixedOrbits_of_finiteDimensional` (the extension of unitary characters
  of `A` trivial on `A ∩ G^1` to `Im X(G)`, for an open common norm kernel `G^1`).
- `RationalDiscreteSeriesOrbitFiniteness`: `rationalDiscreteSeriesFixedOrbits`,
  `isClosed_range_splitComponent`, `isCompact_splitComponent_inf_commonNormKernel`,
  `finite_rationalDiscreteSeriesFixedOrbits_of_finiteDimensional` (the reduction of VIII.5 on
  actual rational points, with `A_G(F)` the image of a split component).
- `FourierTransform`: `coefficientTensorToEnd` (for any smooth representation), and
  `schwartzActionTensor`, `coefficientFourierTransform` and Lemma VII.1.1 (i)–(iii) for an
  admissible smooth representation with tempered coefficients in place of `I_P^G ω`, under the
  analytic hypotheses listed in the row VII.1; see the rows VII.1 and Lemme VII.1.1.
- `TwistedCoefficientSmoothness`: `twistedCoefficientFamily`,
  `torusPartialDerivList_twistedCoefficientFamily`, `L2Weights.lintegral_enorm_pow_mul_le` (the
  core of Prop. VII.1.3 for `M = G` in lattice coordinates; see that row).
- `RationalValuationCoordinates`: `rationalValuationCoordinates` (lattice coordinates of the
  valuation image of `G(F)`), `rationalUnitaryUnramifiedCharacter_apply`, `rationalSplitLattice`,
  `coordinates_symm_mem_restrict_ker_iff` (the kernel of `Im X(G) → Im X(A_G)` in circle
  coordinates); `RationalTwistedCoefficientSmoothness`: `rationalTwistedCoefficient` (the core of
  Prop. VII.1.3 for `M = G` on actual rational points); see the rows Prop. VII.1.3 and
  Prop. VII.2.1.
- `RationalSplitCenterFourierInversion`, `RationalOrbitFourierInversion`,
  `RationalOrbitCentralInversion`: Fourier inversion over `A_G` for `M = G`; see the row
  Prop. VII.2.1.
- `HermitianSchurOrthogonality`: `hermitianCoefficientPairing` and the Hermitian forms of
  III.1 (2), (3) for coefficient tensors; see that row.
- `RationalOrbitWavePacketPairing`, `RationalOrbitWavePacketFourier`,
  `RationalOrbitWavePacketInner`: `rationalOrbitWavePacket` (`f_ψ` for `M = G`) and conditional
  forms of Props. VII.2.1 and VII.2.2 (ii) for `M = G`. They assume continuity of the
  coefficients in `ω ∈ O` (`hcont`), integrability on `A_G` (`hintA`) and a quotient measure
  compatible with the measures on `G(F)` and `A_G` (`hν`, `hνμ`); the pairing assumes the
  integrability of its integrand (`hint`), the Fourier transform assumes `f ∈ C(G)` with
  `⇑f = f_ψ` (`hf`, the open membership of Prop. VI.3.1) and tempered coefficients of `ω'`
  (`hT`), and the inner product assumes the absolute convergence of the double integral over
  `G × O` (`hint`). The factor `μ_A(A_G ∩ G¹)` is kept; its comparison with the normalization
  `mes(A_G ∩ K) = 1` of I.1 is open, and the inner-product formula is for two sections with
  the same base point of `O`. See those rows.
- `InducedFourierTransform`, `InducedFourierCoherence`: `inducedFourierTransform` (`f̂(ω,P)` on
  `L(ω,P)`), Lemma VII.1.1 for `L(ω,P)`, `fourierOrbitSection` (`ψ_f[O,P]`); see the rows VII.1
  and Lemme VII.1.1.
- `InducedConstantTermFourier`, `InducedCoefficientConvergence`, `InducedConstantTermFourierXi`:
  Lemma VII.1.2; see that row.
- `TwistedFourierFamily`, `TwistedFourierIdentification`, `FourierOrbitSmoothness`: the first
  assertion of Prop. VII.1.3, `fourierOrbitSmoothSectionLinear` (and
  `fourierOrbitSmoothSectionLinearXi` in `InducedConstantTermFourierXi`); see that row.
- `LaurentExponent`: `laurentExponent` (the lattice exponent of Laurent torus coordinates);
  `FourierOrbitLaurentSmoothness`: `fourierOrbitLaurentSmoothSectionLinear` (Prop. VII.1.3 with
  that exponent); see the rows VI.1 and Prop. VII.1.3.
- `OrbitWavePacket`: `exists_norm_unitaryOrbitCoefficientMap_le_xi` (Lemma VI.2.2 on
  `C^∞(O,P)`), `inducedOrbitWavePacket` (the wave packet `f_ψ` of VI.3 with a weight in place of
  `μ`, defined for any weight and character measure; its bound, linearity and parameter integral
  hold only under the finiteness, boundedness, measurability, coordinate and Iwasawa hypotheses
  listed in the row VI.3); see the rows Lemmes VI.2.1–VI.2.3, VI.3 and Prop. VI.3.1.
- `OrbitSectionTopology`: `OrbitSectionLevel`, `orbitSectionSeminorm`, `OrbitSectionSpace` (the
  topology of VI.3 on `C^∞(O,P)`); see the row VI.3.
- `OrbitWavePacketDecay`: `exists_norm_inducedOrbitWavePacket_le_xi_rpow` (the first bound of the
  proof of Prop. VI.3.1 with the factor `(1 + \|n_G\|)^{-r}`); see that row.
- `FourierOrbitContinuity`: `fourierOrbitSectionCLM`, `fourierOrbitLaurentSectionCLM` (the
  continuity assertion of Prop. VII.1.3); see that row.
- `InducedOrbitWavePacketPairing`, `InducedOrbitWavePacketOrthogonality`:
  `pairing_inducedOrbitWavePacket_eq_integral_productPairing` (formula (1) of the proof of
  Prop. VII.2.2 for general `M`), `unitaryOrbitWeightedProductCore` (one summand of the product
  of VII.2) and the last step of the proof of Cor. VII.2.3, the last two for a finite character
  measure positive on nonempty open sets; see the rows Prop. VII.2.2, Cor. VII.2.3 and VII.2.
- `WeakConstantTermUniqueness`: `TendstoZeroAlongParabolic` (the limit of III.5) and the
  uniqueness half of Lemma III.5.1, `eq_of_tendstoZeroAlongParabolic`; see that row.
- `FiniteFunctionExpansion`: I.2 for an abstract `A_M`, for functions on which a positive power of
  each element of `ker(H_M)` acts trivially (automatic for smooth functions when `ker(H_M)` is
  compact); see the rows I.2 and Lemme III.5.1.
- `WeakConstantTermExistence`: the existence in Lemma III.5.1 under a span condition, with an
  abstract counterexample; see that row and "Notation and source corrections".
- `ExponentDecomposition`: the exponents of I.3 and the weak/positive split of III.3; see the
  rows I.3, Lemmes III.3.1–III.3.3 and Lemmes VI.2.1–VI.2.3.
- `PositivePartDecay`: Lemma VI.2.3 in abstract form; see the row Lemmes VI.2.1–VI.2.3.
- `CuspidalWavePacketOrthogonality`: the vanishing for functions with vanishing constant term in
  the proofs of Lemmas VIII.2.1 and VIII.2.3; see those rows.
- `RationalOrbitCentralProjection`: the central projection of a wave packet for `M = G`; see the
  row Thm VIII.4.2.
- `RightFiniteUniqueness` (Worker 249): uniqueness in Prop. I.6.2 for right-finite functions and
  for elements of `A(M)`; see the row I.6.

Other modules of this directory, whose Markdown names no author:
`DoubleCosetIndexBoundsStatement` with its proof `doubleCosetIndexBounds`
(`DoubleCosetIndexBoundsProof`), `IwahoriContractionUpperBound`
(`doubleCosetIndex_le_unipotent_contraction`), `ContractionHaarIndex`
(`contractedOpenSubgroup_relIndex`, `contractedIntersection_relIndex`) and
`LatticeQuotientVolumeBound` (`latticeCentralQuotientVolume`): index and volume lemmas for
double cosets of compact open subgroups, used by `rationalLatticeQuotientVolume` (see the
introduction of this section; related to the upper bound of I.1 (5)). `ContractionScaling`,
`DiagonalContraction`, `OppositeUnipotentDisplacement`, `OppositeUnipotentHeight`,
`ParabolicLineHeight` and `ParabolicLineCharacter`: a route to the upper bound in II.2 (6) (see
that row); `UnipotentHeightVolume`: Haar volume of height balls in opposite unipotent groups
(see the row Lemmes II.3.1–II.3.5). Published after commit `81bddf38`: `EigenlineIwasawaBounds`,
`ParabolicDeterminantLine`, `LeviProjectionHeight` (eigenline and Levi height bounds, rows II.2 and
Thm IV.1.1), `UnipotentHeightIntegrability` (row Lemmes II.3.1–II.3.5),
`OpenCellIntersectionProduct`, `UnipotentIntersectionProduct` (row IV.1) and `LocalOpenCellGamma`,
`RestrictedOpenCellIntegration` (row I.1); `RestrictedOpenCellGamma` (Worker 200, row I.1).
Published after commit `f36ed55e`: `LeftHaarSquareIntegrableUnitarity`
(`isUnitarizable_of_irreducible_isSquareIntegrable_leftHaar`, row Lemme III.1.3).

Other generic modules: `Langlands/HarmonicAnalysis/TorusMonomialDerivative` (Worker 249):
derivatives of finite torus functions composed with monomial maps (used for Prop. VI.3.1);
`Langlands.GroupScheme.Rational.Characters` (rational
characters, I.1); `Langlands/GroupScheme/Dynamic/CentralizerReductiveProof`
(`dynamicCentralizerReductive`, row I.1); `Langlands/HarmonicAnalysis/TorusLatticeDuality`
(Worker 249): `latticeAnnihilator`, `isTrivialOn_latticeAnnihilator_iff`,
`hasSum_torusFourierCoeff_mul_conj_mem` (used for Prop. VII.2.1);
`Langlands/LinearAlgebra/RootFaceCone`, `Langlands/LinearAlgebra/RootFaceReflection` and
`Langlands/GroupScheme/Rational/OppositeIntersectionRootInclusions` (convex and root lemmas for
Thm IV.1.1); `Langlands/HarmonicAnalysis/TorusFourierDecay` (Worker 249):
`torusFourierCoeff`, `torusPartialDeriv`, `norm_torusFourierCoeff_le_rpow` (rapid decay of the
Fourier coefficients of smooth functions on a finite torus, estimate (4) of the proof of
Prop. VI.3.1 in coordinates); `Langlands/HarmonicAnalysis/TorusFourierAveraging`,
`TorusFourierSynthesis`, `TorusFourierInversion` (Worker 249): `torusAverage` (the first bound
of the proof of Prop. VI.3.1), `torusSynthesis`, `HasTorusMoments` (smoothness of synthesized
families, used for Prop. VII.1.3) and Fourier inversion on a finite torus,
`hasSum_torusFourierCoeff_mul_conj`, `hasSum_torusFourierCoeff_mul_conj_isTrivialOn` (used for
Prop. VII.2.1); `Langlands/Representation/Exponents/CentralEigencharacterExtensionStatement`
(I.3), proved by `centralEigencharacterExtension` (`CentralEigencharacterExtensionProof`).

### Parabolic induction, Jacquet modules and unitarity for general groups

These modules belong to other programs (the general Aubert involution, Jacquet modules,
geometric lemma and unitary representations). They are listed for the items of Chapters I and
III that they formalize; authors are named in their own Markdown.

- `Langlands/Representation/Aubert/General/Parabolic`: `normalizedJacquetFunctor`,
  `normalizedInductionFunctor`, `IsSemidirectDecomposition`, `closedHalfCharacter_eq_comp_projection`
  (normalized Jacquet restriction and induction on the categories of smooth complex
  representations, for a locally compact nonarchimedean `G`, `P = M ⋉ U` and closed `U`; the
  induction agrees with that of the sources when `U` is unimodular; I.3).
- `Langlands/Representation/Aubert/General/JacquetMultiplicityIrreducibility`:
  `jacquetScalarEquiv`, `isIrreducible_induction_of_semisimple_jacquetHom_rank_le_one` (a
  nonzero semisimple normalized induction whose Jacquet Hom space into the inducing
  representation has rank at most one is irreducible),
  `isIrreducible_induction_of_unitary_jacquetHom_rank_le_one` (the same for a nonzero inducing
  representation with continuous Levi projection, cofinal compact open subgroups and admissible
  unitarizable induction); see the row Prop. IV.2.2.
- `Langlands/Representation/Aubert/General/JacquetAdmissibility` and
  `Langlands/Representation/Jacquet/IwahoriContractionAdmissibility`:
  `isAdmissible_normalizedJacquetFunctor_obj_of_iwahoriContraction` (Jacquet modules of
  admissible representations are admissible, given `Jacquet.HasIwahoriContractionBasis`; I.3).
- `Langlands/Representation/Jacquet/ExactProof`: `smoothCoinvariantExactness` (exactness of
  coinvariants, I.3, for a topological group in which every finite subset lies in a compact
  open subgroup; this premise is explicit and does not follow from local compactness or the
  nonarchimedean property). `Langlands/BruhatTits/Unipotent/CompactOpenContainmentProof`:
  `dynamicUnipotentCompactOpenContainment` supplies the premise for the actual dynamic unipotent
  radicals `U_G(χ)(F)`; the identification of Waldspurger's unipotent radicals with these is not
  made here.
- `Langlands/Representation/Jacquet/StablePairingProof`, `IwahoriStablePairingAdmits`,
  `StablePairingVanishing`: `exists_isStablePairing`, `IsStablePairing.injective`,
  `IsStablePairing.flip_injective`, `admits_of_iwahoriContractions` (an abstract form of the
  pairing of I.4.1, from Casselman 2019, Thm III.6.2, for supplied contraction data).
- `Langlands/Representation/Jacquet/StablePairingAsymptotics` (Worker 249): the asymptotic
  formula of I.4.1 for stable pairings, its normalized form and the abstract Theorem I.4.1
  (`exists_nondegenerate_invariant_hasAsymptotics`); see the row Thm I.4.1.
- `Langlands/Representation/Aubert/General/IwahoriNaturalJacquetDuality`:
  `exists_naturalNormalizedJacquetDuality_of_iwahoriContractions_of_reciprocalModulus` (the
  conclusion of Cor. I.4.2 as a natural family on admissible representations, given an opposite
  Iwahori contraction basis and reciprocal Haar characters); the rational target
  `RationalNaturalJacquetDualityStatement` (`RationalJacquetDualityStatement`) is a statement only.
- `Langlands/Representation/Geometric/ClosedSubgroupStatement`, `ClosedSubgroupMackeyProof`:
  `ClosedSubgroupMackeyFiltration`, `closedSubgroupMackeyFiltration` (the support filtration
  of compact induction from `P` restricted to `Q`, along a finite ordering of `P \ G / Q`, and
  its graded pieces, for a Hausdorff, locally compact, nonarchimedean, sigma-compact `G` and
  closed subgroups `P`, `Q`; I.3, toward `F_w`).
- `Langlands/Representation/Aubert/General/GeometricK0Target`, `RationalGeometricK0Target`:
  `GeometricK0ExpansionStatement`, `RationalGeometricK0ExpansionStatement` (the geometric lemma
  in the Grothendieck group, Aubert 1995 (1.3); statements only).
- `Langlands/Representation/Aubert/General/RationalSquareIntegrabilityStatement`,
  `RationalSquareIntegrabilityReductionStatement`, `RationalSquareIntegrabilityReductionProof`,
  `RationalLatticeCoefficientDecayStatement`, `RationalLatticeCoefficientDecayProof`:
  `RationalStrictJacquetSquareIntegrabilityStatement`,
  `rationalStrictJacquetSquareIntegrabilityReduction` (Casselman's criterion, sufficiency
  direction, on actual rational points, from the unproved
  `JointSpecialCompactBasisExistenceStatement`; III.1.1), `rationalLatticeCoefficientDecay`
  (III.1.2).
- `Langlands/Representation/Aubert/General/RationalReductiveUnimodularityStatement`,
  `RationalParabolicModulusStatement`: `RationalReductiveUnimodularityStatement`,
  `RationalParabolicModulusStatement` (unimodularity of `G(F)` and the modular characters of
  standard parabolics, I.1); `rationalParabolicModulus_of_reductiveUnimodularity`
  (`RationalLeviUnimodularityReduction`) derives the second from the first and
  `DynamicCentralizerReductiveStatement`, which is proved by `dynamicCentralizerReductive`
  (`Langlands/GroupScheme/Dynamic/CentralizerReductiveProof`); `rationalReductiveUnimodularity_of_structural_inputs`
  and `rationalParabolicModulusAssembly` (`RationalReductiveUnimodularityReductionProof`, with
  `rationalTorusModularReduction` in `RationalTorusModularReductionProof`) derive the first from
  six structural Props, two of them unproved (see the row I.1).
- `Langlands/Representation/Unitary/Basic`, `AdmissibleSemisimplicityStatement`,
  `AdmissibleSemisimplicityProof`: `InvariantPositiveForm`, `IsUnitarizable`,
  `AdmissibleUnitarySemisimplicityStatement`, `admissibleUnitarySemisimplicity` (admissible
  unitarizable representations are semisimple, when compact open subgroups are cofinal; the
  last step of the proof of Lemma III.1.3). `Langlands/Representation/Unitary/PositiveFormTensor`
  (Worker 200), `AdmissibleFormUniqueness`: `InvariantPositiveForm.tensorProduct`,
  `InvariantPositiveForm.rescale`, `InvariantPositiveForm.exists_pos_rescale_eq` (an invariant
  positive form on an irreducible admissible representation is unique up to a positive scalar;
  used for V.2).
- `Langlands/Representation/Exponents/ArbitraryParabolicTempered`, `NormalizedTemperedFullGroupProof`,
  `NormalizedTemperedSplitCentralCharacter`, `NormalizedTemperedLogarithmicComparison`,
  `NormalizedTemperedStandardReduction`, `NormalizedTemperedStandardReductionFromDynamics`,
  `ArbitraryParabolicConjugation`, `ArbitraryParabolicTemperedConjugation`,
  `FullCenterFromSplitComponent`: `RepresentedParabolic.IsNormalizedExponentTempered` and its
  properties (the exponent side of Prop. III.2.2; see that row).
- `Langlands/Representation/Exponents/ArbitraryParabolicCasselmanStatement`,
  `SquareIntegrableNormalizedTemperedStatement`, `ArbitraryParabolicExponentStatement` (Worker 6;
  statements only), `ArbitraryParabolicInduction`, `ArbitraryParabolicLeviPoints` (Worker 6),
  `ArbitraryParabolicInductionComparison`, `JacquetExponentRestriction`,
  `SplitComponentComparison`, `SplitComponentDecomposition`, `SplitComponentFiniteSupport`
  (Worker 1666, with Worker 1670), `ArbitraryParabolicFiniteSupportReduction`: Renard VII.1.1,
  VII.1.2 and VII.2.1, Remark 2, for actual rational parabolics; see the rows Prop. III.1.1 and
  Lemme III.2.1.
- `Langlands/Representation/Exponents/CentralDecompositionProof` (Worker 1629):
  `centralCharacterDecomposition` (an admissible representation is center-finite, and a smooth
  representation on which the center acts finitely decomposes into generalized central-character
  spaces; Casselman 1995, Prop. 2.1.3 and 2.1.9; used for the exponents of I.3).

### `GL_n`-specific work

These modules cite the article but are stated for `GL_n` over a `p`-adic or
nonarchimedean local field. They are not general-group adapters. A
specialization of the general targets to `GL_n` may reuse them.

- `Langlands/Group/GL/Cartan*`: Cartan cells and the count `mes(KmK)` (I.1 (4), (5)).
- `Langlands/HarmonicAnalysis/HarishChandraSchwartz/SigmaProductGL` (Worker 249):
  `sigmaProductBound_glBlock` (Lemma II.3.1 for the standard block upper triangular
  parabolics `BlockShape.parabolic` of `GL_n` and the identity embedding, without
  hypotheses).
- `Langlands/HarmonicAnalysis/HarishChandraSchwartz/DoubleCosetMeasureGL` (Worker 249):
  `GLDoubleCosetIndexBound`, `glDoubleCosetIndexBound`, `exists_measure_doubleCoset_le_delta`
  (the upper bound of I.1 (5) for `GL_n(O)` and diagonal `a(λ)`, from Worker 23's
  `cartanCellCount`, for every left invariant measure).
- `Langlands/Representation/Classification/`: `SquareIntegrableExponent*`,
  `ProductLeviSquareIntegrable*` (III.1, III.1.1, III.1.2);
  `TemperedExponentStatement`, `TemperedInduction*`,
  `ProductLeviTempered*`, `InductionWeakJacquetBounds*`, `MaximalCone*`
  (III.2.2, III.2.3); `TemperedOppositeJacquetScalarLayer*` (III.3.1);
  `TemperedSupportStatement`, `TemperedSupportProof` (`glTemperedDiscreteSeriesSupport`,
  III.4.1); `LeviDiscreteSeriesTemperedProof`, `LeviTemperedUnitarity*`
  (`glLeviDiscreteSeriesTempered`, `glLeviTemperedUnitarity`, toward Lemma III.1.3);
  `TemperedDiscreteSeriesIsotypic*`, `DiscreteSeriesJacquetStatement`.
- `Langlands/Representation/Parabolic/`: `NaturalJacquetDualityStatement`,
  `NaturalJacquetDualityProof` (`standardNaturalJacquetDuality`,
  `refinedNaturalJacquetDuality`, Cor. I.4.2) and the second-adjointness modules
  `SecondAdjointness*`.
- `Langlands/Representation/Geometric/`: `GeometricLemmaStatement`, `GeometricLemmaProof`
  (`padicGeometricLemma`), `GrothendieckStatement`, `GrothendieckProof`
  (`geometricLemmaGrothendieck`) (the filtration `F_w` of I.3, Bernstein–Zelevinsky 2.12).
- `Langlands/Representation/Exponents/`: `CoefficientExtractionStatement`,
  `JacquetEigenvector*` (I.3, I.4.1), `StrictCartanCoefficientBound*`
  (I.4.3, III.1.1, III.1.2), `TemperedDualJacquetExponentBound*` (III.2.2),
  `OppositeJacquetSubquotientInheritanceStatement` (III.3.1),
  `ExtractedCoefficientL2ObstructionStatement` (III.1).

This list records which modules cite which items. It is not the
declaration-level reuse audit of condition 7, which remains open.

## Dependency chains to the main targets

- **VII.2.5** needs VII.2.1–VII.2.3 and VII.1.4. These need VI.4.1, VII.1.2,
  III.1 (2), (3) and V.3.1. VI.4.1 needs VI.2, V.1.1, V.2.3, III.1.2, II.3.4,
  II.4.3 and IV.2.1. V needs IV.1–IV.3, III.3–III.5 and III.7. The
  wave-packet side needs VI.3.1 (Schwartz membership).
- **VIII.1.2** needs VIII.4.1 and VIII.4.2. These need VIII.2, VIII.3 (with
  II.1, II.3, II.4, I.1 (4), (5)), VII.2.5 and Schur orthogonality III.1 (2).
- **VIII.1.1** needs VIII.1.2 for all Levi subgroups (Rem. VIII.1.3),
  VIII.2.1 and VIII.4.2. The final steps of VIII.5 that do not need VII.2.5 are formalized
  in abstract form (see the row VIII.5).
- **VIII.1 (3)** follows from VIII.1 (2) with VII.1.1 (iii) and VII.2.4.

The external inputs on these chains are [BZ] (I.3), [C] (I.4.1, I.4.3,
III.1.1, III.1 (2), (3)), [BD] (I.5), [H] (II.2) and [B] (III.6). Sauvageot
[S] is not needed for square-integrable `π`.
