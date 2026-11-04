# Waldspurger 2003 Plancherel formula: source map

Author: Worker 249, task `1ef6854b-f0e9-4d96-bbe5-cb8c4b52f927` (revision 1).
Lean coverage below was checked against Library commit
`cf45df0608b9136ff545b17eadf8297cd7be81fd`.

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
| [H, Thm 4.6; Ex. 8 p.115] Humphreys | II.2 (6), p.254 | orbit map of `Ū` is an isomorphism onto a closed image (purely inseparable in characteristic p) |
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
| I.1 | 238–242 | `F`, `G`, `A_0`, `M_0`, `P_0`, `Rat(G)`, `a_G`, `H_M`, roots `Σ`, `W`, special `K`; left Haar measures with `mes(H ∩ K) = 1`, the functional `∫_{H\G}` on `δ_H`-covariant functions and the integration formulas (2) (p.240); `G = P K`, Iwahori factorization, `γ(P)` depends only on `M` (proof on p.241), `c(G\|M)`, Cartan decomposition (4), `mes(KmK) ≍ δ_0(m)^{-1}` (5), the norm `‖·‖` via `τ : G → GL_n` with `τ(K) ⊆ GL_n(O)`, `σ = log‖·‖`, (6) `1 + σ(m) ≍ 1 + \|H_0(m)\|` | — | Data, Struct; `γ(P)` independence and (5) are Book | (2), first formula: `lintegral_eq_lintegral_unipotent_levi` (generic); (2), second formula, with `γ(P)` and `0 < γ(P) < ∞`: `lintegral_eq_openCellConstant_inv_mul`, `openCellConstant`, `openCellConstant_eq_lintegral` (generic, in the coordinates `(p, v) ↦ p v^{-1}`) and `lintegral_eq_openCell_levi_unipotent` (generic, in the coordinates `m u v^{-1}`); the topological hypotheses `hι` of `lintegral_eq_openCellConstant_inv_mul` and `hhomeo` of `leviUnipotentMeasure_isHaarMeasure` on rational points, for the dynamic subgroups `P_G(χ)`, `U_G(χ^{-1})`, `Z_G(χ)`, `U_G(χ)` of an affine group scheme over a topological field with open units: the open cell `isOpenEmbedding_openCellMap_rationalPoint` (smooth `G`) and the Levi coordinates `isHomeomorph_leviUnipotentCoord_rationalPoint` (`G` locally of finite type); Haar-nullness of the complement of the open cell is open; (3) open (the index expression of `γ(P)` in its proof: `openCellConstant_eq_relIndex_mul`, generic); (5): `measure_doubleCoset_le_of_doubleCosetIndex` (generic, from bounds on `[H : H ∩ mHm^{-1}]`), upper bound for `GL_n`: `exists_measure_doubleCoset_le_delta`; a related upper bound modulo the full center on actual rational points, `rationalLatticeQuotientVolume` (given a supplied simultaneous standard basis, the unproved Prop `StandardCocharacterStatement` and the topological premises listed below); restriction `Im X(G) → Im X(A_G)` surjective with finite kernel and the measures on `Im X(A_G)` and `Im X(G)` (p.239): `rationalUnitaryUnramifiedCharacterRestrict_surjective` (without `hindex`), `finite_rationalUnitaryUnramifiedCharacterRestrict_ker` and `rationalUnitaryUnramifiedCharacterHaar` (given the open finite-index premise `hindex`, Renard V.2.6); unimodularity of `G(F)` and the modular characters of standard parabolics: the unproved Props `RationalReductiveUnimodularityStatement`, `RationalParabolicModulusStatement`; see below |
| I.2 | 242–243 | finite-dimensional `ρ(A_M)`-stable spaces `V ⊂ C^∞(A_M)`: expansion `f(a) = Σ_{χ ∈ X} χ(a) P_{χ,f}(H_M(a))` with `deg P_{χ,f} ≤ d`; for minimal `X`, polynomial growth on `A_M` ⇔ `Re χ = 0` for all `χ ∈ X`; if `∏_{χ ∈ Y} (ρ(a) − χ(a))^D` kills `V`, then `X ⊂ Y` and `d ≤ D − 1`; the same for `A_M`-finite `f` | I.1 | Book (stated without proof or citation) | none for `A_M`; related: Renard App. C.III for `ℤ^d`, `Langlands.IntegerLatticeMatrixCoefficientExponentialPolynomialStatement` (statement and proof in `Langlands/Representation/MatrixCoefficient/IntegerLattice*`), not adapted to I.2 |
| I.3 | 243–244 | Jacquet functor, normalized induction `I_P^G`, filtration `F_w` of `(I_P^G V)_{P'}` | [BZ] | Data, Ext | generic, for actual subgroups with `P = M ⋉ U` and `U` closed in a locally compact nonarchimedean `G`: the normalized Jacquet functor `Langlands.Aubert.General.normalizedJacquetFunctor` and normalized induction `Langlands.Aubert.General.normalizedInductionFunctor` (full-parabolic normalization); the Levi-inflated normalization of I.3 (`LeviNormalizedCovariant`) and its comparison with that functor when `U` is unimodular, `normalizedInductionLeviEquiv` (generic) and `standardNormalizedInductionLeviIsoOfStandardCocharacter` (actual standard rational points, given `StandardCocharacterStatement`); exactness of coinvariants for a group in which every finite subset lies in a compact open subgroup (an explicit premise, not implied by the data above), `smoothCoinvariantExactness`, with that premise for the actual dynamic unipotent radicals `U_G(χ)(F)` of connected reductive groups over local fields supplied by `dynamicUnipotentCompactOpenContainment` (every compact subset of `U_G(χ)(F)` lies in a compact open subgroup); admissibility of Jacquet modules given an Iwahori contraction basis, `isAdmissible_normalizedJacquetFunctor_obj_of_iwahoriContraction`. Toward `F_w`: the Mackey support filtration of compact induction from a closed subgroup `P`, restricted to a closed subgroup `Q`, with its graded pieces (compactly induced orbit pieces), `closedSubgroupMackeyFiltration` (generic); the filtration of the Jacquet module of an induced representation and its graded pieces (Bernstein–Zelevinsky's geometric lemma) only for `GL_n`, `padicGeometricLemma` and its Grothendieck-group form `geometricLemmaGrothendieck`; the Grothendieck-group identity for general groups only as the unproved Props `GeometricK0ExpansionStatement`, `RationalGeometricK0ExpansionStatement`. The identification of the smooth contragredient of `I_P^G V` with `I_P^G V̌` by the quotient integral: `normalizedInductionIntegralDualEquiv` (actual topological subgroup data) |
| Thm I.4.1 | 245 | Casselman pairing `⟨·,·⟩_P` on `V_P × V̌_{P̄}` | [C] | Ext | an abstract form of the pairing, between the Jacquet module of `V̌` for one radical and that of `V` for the opposite radical, characterized by evaluation on stable vectors: `StablePairingData.IsStablePairing`, `exists_isStablePairing`, nondegenerate (`IsStablePairing.injective`, `IsStablePairing.flip_injective`) and invariant (`IsStablePairing.map_action`), for supplied `StablePairingData` satisfying `Admits` (generic); `Admits` follows from admissibility and opposite Iwahori contractions, `admits_of_iwahoriContractions`; for the block parabolics of `GL_n` the data are constructed (`standardPairingData_admits`, `refinedPairingData_admits`); the asymptotic formula of I.4.1: none |
| Cor. I.4.2 | 245 | `V̌_{P̄}` is the contragredient of `V_P` | I.4.1 | Book | for the block parabolics of `GL_n`: `standardNaturalJacquetDuality`, `refinedNaturalJacquetDuality` (natural families `r_P(V̌) ≅ (r_{P̄}(V))^∨` on admissible objects, proving `NaturalNormalizedJacquetDualityStatement`); generic, for closed `U`, `O` normalized by `M`, an element commuting with `M` with an opposite Iwahori contraction basis (`HasOppositeIwahoriContractionBasis`) and reciprocal Haar characters on `U` and `O`: a natural family `r_U(V̌) ≅ (r_O(V))^∨` on admissible objects, `exists_naturalNormalizedJacquetDuality_of_iwahoriContractions_of_reciprocalModulus` and `naturalNormalizedJacquetDualityOfIwahoriContractionsOfReciprocalModulus`; on actual rational points only the unproved Prop `RationalNaturalJacquetDualityStatement` |
| Prop. I.4.3 | 245 | coefficients equal Jacquet coefficients on `M_0^+` cones | [C] | Ext | the equality: none; a related strict exponential coefficient bound for `GL_n` from normalized Jacquet bounds, `glStrictCartanCoefficientBound` (proof of `GLStrictCartanCoefficientBoundStatement`) |
| Cor. I.4.4 | 245 | polynomial growth: `\|⟨π(g)v, v̌⟩\| ≤ c‖g‖^d` | I.1 (4), I.4.3 | Book | none |
| I.5 | 245–248 | `B`-families (`B` finitely generated commutative Noetherian), contragredient, Jacquet modules, induction, exponents, rationality; analogue of I.4.1 | I.4.1, [BD, 2.5, 3.1], [BD, 3.5.2] | Data, Book, Ext | none |
| Lemme I.6.1, Prop. I.6.2 | 249–250 | `C_lisse(G)`, `ρ`, `λ`; `A_ρ = A_λ = A(G)`; constant term `f_P` of `A(G)` and `f_P^{Ind}` | I.4 | Data, Book | the coefficient space `A(π)` of a smooth representation as the range of `coefficientTensorMap` (`range_coefficientTensorMap`: the span of the coefficients); Lemma I.6.1 and the constant term `f_P`: none |

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
| II.2 | 253–254 | algebraic representation `τ_P` with properties (1)–(5); (6) `1 + σ(ū) ≍ 1 + log‖τ_P(ū)e_1‖` | [H] | Book (the construction is on p.253 and (6) is proved on p.254 from (7), (8) and [H]) | none; the properties used are explicit hypotheses of `TauEstimates` and `OpenCellLemma` |
| Lemmes II.3.1–II.3.5 | 254–259 | estimates for `δ_P(m_P(ū))`, `σ` on `Ū` | II.2, I.1 | Book | generic, from properties of `τ_P` as hypotheses: II.3.1 `sigmaProductBound_height` (given the block form; for the standard block parabolics of `GL_n` without hypotheses, `sigmaProductBound_glBlock`), II.3.2 `cartanWeightComparison_of_norm`, II.3.3 `conj_height_le_of_tau`, II.3.4 `modulusHeightBounds_of_tau`, II.3.5 `openCellBound_of_mul` |
| Lemmes II.4.1–II.4.4, Prop. II.4.5 | 259–263 | integrals over `Ū`; constant term of functions bounded by `Ξ(1+σ)^{-d'}` | II.1, II.3 | Book | generic: II.4.1 `levelSetMeasureBound_of_torusXiFormula`, II.4.2 `unipotentWeightIntegrable_of_levelSets`, II.4.3 `LeviData.unipotentWeightIntegrable`, II.4.4 `XiUpperBound.unipotentXiBound`, II.4.5 `constantTermEstimate_of_bounds` (it proves the Prop `ConstantTermEstimate` of `ConstantTerm`); the inputs are listed in the modules below |

## Chapter III. Tempered representations and `C(G)` (pp.263–276)

| Item | Page | Content | Uses | Class | Lean coverage |
|---|---|---|---|---|---|
| III.1 | 263 | square integrable modulo `A_G` | I.1 | Data | `IsSquareIntegrableModCentralSubgroup` |
| Prop. III.1.1 | 263 | square integrability via exponents | [C] | Ext | `GL_n` (see Library coverage); on actual rational points of connected reductive groups, the sufficiency of strict normalized Jacquet exponents for square integrability modulo the full center: the Prop `RationalStrictJacquetSquareIntegrabilityStatement` (with `StandardCocharacterStatement` among its premises), proved from the unproved Prop `JointSpecialCompactBasisExistenceStatement` by `rationalStrictJacquetSquareIntegrabilityReduction` |
| Cor. III.1.2 | 263–264 | coefficients bounded by `c Ξ(1+σ)^{-r}` on `G^1`, for every `r` | I.1 (4), I.4.3, II.1.1, III.1.1 | Book | GL_n only; the conclusion as a Prop, with a supplied subgroup in place of `G^1`: `HasRapidlyDecreasingCoefficientsOn` (generic, statement only); a related exponential bound for coefficients on lattice rays of actual rational points, from strict normalized Jacquet exponents and a supplied simultaneous standard basis: `rationalLatticeCoefficientDecay` |
| Lemme III.1.3 | 264 | an admissible square-integrable representation is unitary and semisimple | II.1.5, III.1.2 | Book | for irreducible representations of `GL_n` block Levis: square integrable modulo the center implies tempered, `glLeviDiscreteSeriesTempered`, and tempered implies unitarizable, `glLeviTemperedUnitarity`; generic: admissible unitarizable representations are semisimple, `admissibleUnitarySemisimplicity` (compact open subgroups cofinal); the lemma for general groups: none |
| III.1 (2), (3) | 265 | Schur orthogonality, formal degree `d(π) > 0` | [C], III.1.2, II.1.5 | Ext | none |
| Lemme III.2.1, Prop. III.2.2, Lemme III.2.3 | 265–267 | tempered representations; criteria via exponents; induction | I.2, I.3, I.4.1, I.6.1, II.1.1, II.1.2, III.1.2 | Book | GL_n only; generic growth condition `HasTemperedGrowth` (`TemperedPairing`) |
| Lemmes III.3.1–III.3.3 | 267–268 | weak constant terms `π^w_P` | I.3, III.1.1, III.2.2 | Book | GL_n only (III.3.1) |
| Prop. III.4.1 | 269 | an irreducible tempered representation embeds in some `I_P^G ω`, `ω ∈ E_2(M)` | III.3.2, III.3.3 | Book | `GL_n` only: `glTemperedDiscreteSeriesSupport` (proof of `GLTemperedDiscreteSeriesSupportStatement`: an irreducible admissible tempered representation of `GL_n(F)` embeds in a representation normally induced, from the opposite of a standard block parabolic, by an irreducible representation of its Levi that is square integrable modulo the center) |
| Lemme III.5.1 | 269–270 | weak constant term `f^w_P` of `f ∈ A^w(G)` | III.3 | Book | none |
| III.6 | 271–272 | `C(G)`, seminorms `ν_r`, levels `C_H`, inductive-limit topology, (1), completeness, `C_c^∞(G)` dense, `G × G` acts continuously, constant term `f^{(P)}` via II.4.5 | I.6, II.1, II.1.2, II.4.5, [B] | Data, Book | generic: `C(G)`, `ν_r`, `C_H`, topology, (1), density, `G × G` continuity, completeness (`Space.completeSpace`, for a cofinal sequence of compact open subgroups), `f^{(P)}` and `C(G) → C(M)` (`constantTerm`, with II.4.5 as a hypothesis), `f^{(P),Ind}` and the diagram (`constantTermInd`, pointwise; see below) |
| Lemme III.6.1 | 271 | for `f_1, f_2 ∈ C(G)`: `∫_G f_1(h) f_2(h^{-1}g) dh` converges absolutely, `f_1 * f_2 ∈ C(G)`, and `(f_1, f_2) ↦ f_1 * f_2` is separately continuous | II.1.3–II.1.5 | Book | `Convolution` (generic; II.1.3–II.1.5 as hypotheses) |
| III.7, Prop. III.7.1, Cor. III.7.2, III.7.3 | 273–276 | `π(f)`, `θ_π(f)` continuous on `C(G)`; `E_2(G)`; orbits `O` of `Im X(G)`; polynomials on `O`; `W(G\|M)`; regular `ω`: `(I_P^G ω)^w_{P'}` semisimple | III.1.2, III.3.2, III.3.3, III.6.1 | Data, Book | first paragraph (generic, for an admissible representation with the displayed coefficient-growth hypothesis `HasTemperedCoefficients`): `π(f)` `schwartzAction`, of finite rank `schwartzAction_mem_finiteRankEnd`, `θ_π` as a continuous linear form `schwartzCharacter`, `π(f_1 * f_2) = π(f_1) π(f_2)` `schwartzAction_convolution`; second paragraph, `f φ ∈ C(G)` for `f ∈ A(ω)` and `φ ∈ C_c(G/N)`: `TranslationWeights.mul_mem_schwartzSubmodule` (generic, with an open normal subgroup `N` in place of `G^1` and the conclusion of Cor. III.1.2 as the hypothesis `HasRapidlyDecreasingCoefficientsOn`); proof of Prop. III.7.1, the operator `π[φ]` of a family with properties (1), (2) and its naturality: `IdempotentFamily.operator`, `IdempotentFamily.operator_intertwining` (generic), and the concrete family `φ_H = φ ψ_H` with the first displayed equality for `π[φ]`: `traceFamily`, `traceFamily_operator_eval` (generic, with an open normal subgroup in place of `G^1`); proof of Cor. III.7.2, the Fitting decomposition of an intertwiner of an admissible representation: `isCompl_fittingRange_fittingKernel`, `bijOn_fittingRange` (generic); Prop. III.7.1 and Cor. III.7.2 themselves are open; orbits: `DiscreteSeriesClass`, `discreteSeriesOrbit`, their quotient topology (compact, Hausdorff) `discreteSeriesOrbitHomeomorph`, `compactSpace_discreteSeriesOrbit`, `t2Space_discreteSeriesOrbit`, finiteness of the stabilizer `finite_discreteSeriesStabilizer` (generic), `finite_rationalDiscreteSeriesStabilizer` (given the open finite-index premise `hindex`, see below); the pairing of `C(G)` with functions of tempered growth, `Space.temperedPairing` (generic) |

## Chapter IV. Intertwining operators (pp.276–287)

| Item | Page | Content | Uses | Class | Lean coverage |
|---|---|---|---|---|---|
| IV.1 | 276–278 | compact picture, rational families via `B`-families, `J_{P'\|P}(π)` by integrals over `U ∩ U' \ U'` | I.5 | Data | compact picture: restriction of normalized induction to `K` and its independence of unramified twists, `normalizedInductionCompactEquiv`, `unramifiedNormalizedInductionCompactEquiv` (actual subgroup data, with `G = P K` as a hypothesis; the Library's full-parabolic normalization, see below); the integral `∫_{(U ∩ U') \ U'} f(u' g) du'` on the subspace of the Levi-inflated induced space where it converges weakly: `Langlands.Plancherel.StandardIntertwining.operator`, with `operator_right_action`, `operator_uniformly_smooth`, `operator_unipotent_mul` (generic; target Levi covariance not proved); rational families: none |
| Thm IV.1.1 | 278 | convergence in a cone and rationality of `J_{P'\|P}(π ⊗ χ)` | II.3.4, II.4.2, I.4.4, I.3 | Book | none |
| IV.1 (10)–(14) | 283–284 | uniform convergence, nonvanishing, adjoint, composition, transitivity | IV.1.1 | Book | none |
| Cor. IV.1.2 | 284 | pole order at 0; for square integrable `π`, `J` regular unless `P̄` conjugate to `P` | IV.1.1 | Book | none |
| Prop. IV.2.1 | 284 | tempered: convergence for `⟨Re χ, α^∨⟩ > 0` | II.4.3 | Book | none |
| Prop. IV.2.2 | 284 | `ω` square integrable and `G`-regular: `I_P^G ω` irreducible, `J` regular and invertible | III.7.3, IV.1 | Book | none |
| IV.3 (1)–(6) | 285–287 | `j(π)`: `J_{P\|P̄} J_{P̄\|P} = j(π)`, independence of `P`, symmetries, product formula, `j ≠ 0` for square integrable | IV.1, IV.2.2, [S] (avoided for square integrable `π`) | Book | none |

## Chapter V. Weak constant terms of induced coefficients (pp.287–295)

| Item | Page | Content | Uses | Class | Lean coverage |
|---|---|---|---|---|---|
| V.1 | 287–289 | `L(ω,P)`, `E_P^G`, `W(M'\|G\|M)`, `c_{P'\|P}(s,ω)` | III.7, IV | Data | the tensor model of `L(ω,P)` and its coefficient map `ℓ(π(g)v)`: `CoefficientTensor`, `coefficientTensorMap`, `range_coefficientTensorMap`, `NormalizedCoefficientTensor`, `normalizedCoefficientMap`, `normalizedInductionDualTensorEquiv`; product induction `I_P^G(A) ⊠ I_Q^H(B) ≅ I_{P×Q}^{G×H}(A ⊠ B)`: `normalizedProductInductionTensorEquiv`; `L(ω,P) = I_{P×P}^{G×G}(E ⊗ Ě)` and `E_P^G` on it: `productInducedCoefficientObject`, `productInducedCoefficientMap`, with the integral formula `productInducedCoefficientMap_integral` and image `range_productInducedCoefficientMap` (actual subgroup data with explicit hypotheses, the Library's full-parabolic normalization; in the Levi-inflated normalization of I.3: `leviProductInducedCoefficientMap`; see below); `W(M'\|G\|M)` and `c_{P'\|P}(s,ω)`: none |
| Prop. V.1.1 | 289 | weak constant terms of `E_P^G ψ` | III.3.3, III.4.1, IV.2.2, III.5.1, IV.1, IV.3 | Book | none |
| V.2, Lemme V.2.1 | 292 | `μ(ω) = j(ω)^{-1} ∏ γ(M_α\|M)^2`: rational, regular, `≥ 0`, product formula, Weyl invariant | IV.3 | Data, Book | none |
| Lemme V.2.2, Cor. V.2.3 | 293–294 | norm identity for `c_{P'\|P}(s,ω)`; regularity of `μ^G μ^{M'}(sω)^{-1} c` | V.1.1, V.2.1 | Book | none |
| V.3, Lemmes V.3.1, V.3.2 | 295 | normalized `°c_{P'\|P}(s,ω)`: regular, unitary, `E_{P'}^G(°c ψ) = E_P^G ψ`, cocycle | V.2 | Data, Book | none |

## Chapter VI. Wave packets (pp.295–313)

| Item | Page | Content | Uses | Class | Lean coverage |
|---|---|---|---|---|---|
| VI.1 | 295–296 | identifications of `L(ω,P)` along an orbit; `C^∞(O,P) = [C^∞(Im X(M)) ⊗ L_K(ω,P)]^{Stab}` | V.1 | Data | transport of coefficient tensors along equivalences, independent of the choice: `normalizedCoefficientTransport`, `normalizedCoefficientTransport_independent`; scalar smooth functions on an orbit: `IsSmoothRationalOrbitFunction`, `rationalSmoothOrbitFunctions`, `isSmoothRationalOrbitFunction_basis_iff`; transport between the spaces `L(ω,P)` of equivalent representatives, independent of the equivalence for irreducible admissible `ω`: `productInducedCoefficientTransport`; the fixed compact picture `productInducedCompactEquiv` and the action of the stabilizer on it by self-twists `unramifiedStabilizerCompactRepresentation`; the coefficient-valued `C^∞(O,P)` as coherent smooth sections over the unitary unramified twist orbit of a fixed irreducible admissible `ω`, and its identification with the stabilizer-invariant tensors: `productInducedSmoothOrbitSections`, `productInducedSmoothTensorOrbitEquiv` (with supplied torus coordinates, `G = P K` as a hypothesis, the stabilizer `unitaryClassTwistStabilizer` of `ω` in the unitary unramified characters, and the Library's full-parabolic normalization; see below); independence of the base representative, `productInducedSmoothOrbitBaseEquiv`; the comparison with the discrete-series orbit and the full unramified stabilizer, `unitaryOrbitRepresentativeDiscreteSeriesOrbit`, `productInducedFullStabilizerTensorOrbitEquiv` (given finiteness of the relevant central quotient, see below) |
| Lemmes VI.2.1–VI.2.3 | 296–301 | smoothness in `ω`; `\|E_P^G ψ_ω(g)\| ≤ C Ξ(g)`; exponential decay of the `+` part on `D_{M'}(δ)` | I.5, I.4.3, III.1.2, II.1.6, II.1.1, III.2.2 | Book | none |
| VI.3 | 301–302 | topology on `C^∞(O,P)`; measure on `O`; wave packet `f_ψ(g) = ∫_O μ(ω) (E_P^G ψ_ω)(g) dω` | VI.1 | Data | measure on `O` locally preserved by the character parametrization: `discreteSeriesOrbitMeasure` (generic), `rationalNormalizedDiscreteSeriesOrbitMeasure`; integration over `O`: `rationalDiscreteSeriesOrbitIntegral` (the last two given the open finite-index premise `hindex`, see below); the topology on `C^∞(O,P)` and the wave packet: none |
| Prop. VI.3.1 | 302 | `f_ψ ∈ C(G)`, `ψ ↦ f_ψ` continuous | I.1 (4), I.4.3, I.5, VI.2, V.1.1, V.2.3, II.1.1 | Book | none |
| VI.3 | 305–306 | `Θ`, `C^∞(Θ)`, `κ̃`; invariant subspace `C^∞(Θ)_inv`; `κ`; projector | V.3 | Data | none |
| Lemme VI.3.2 | 306 | `κ̃` factors through the projector | V.3.1 | Book | none |
| Prop. VI.4.1 | 306–313 | constant terms `f_ψ^{(P'),Ind}`: zero for smaller non-conjugate Levis; explicit for `M' = M` | VI.2, V.1.1, V.2.3, III.1.2, II.3.4, II.4.3, IV.2.1 | Book | none |

## Chapter VII. Fourier transform and isometry (pp.313–320)

| Item | Page | Content | Uses | Class | Lean coverage |
|---|---|---|---|---|---|
| VII.1 | 313–314 | `f̂(ω,P) = d(ω) π(f̌)` in `L(ω,P)`; `θ^G_ω`; `(f_1,f_2)_X = ∫ conj(f_1) f_2` | III.7 | Data | `f̌` and `(f_1,f_2)_G` on `C(G)`: `L2` (generic) |
| Lemme VII.1.1 | 314 | equivariance; `(E_P^G ψ, f)_G = (ψ, f̂(ω,P))`; `E_P^G(f̂(ω,P))(g) = d(ω) θ^G_ω(λ(g) f̌)` | III.7 | Book | none |
| Lemme VII.1.2 | 315 | `f̂(ω,P) = f̂^{(P),Ind}(ω)`, where `f̂^{(P),Ind}(ω)(g_1,g_2) = [f^{(P),Ind}(g_1,g_2)]^(ω,M)` is the Fourier transform of VII.1 for `M`, applied pointwise to the induced constant term `f^{(P),Ind} : G × G → C(M)` of III.6 | III.6, VI.2.2, II.1.5, VII.1.1 | Book | none |
| Prop. VII.1.3 | 316 | `ψ_f[O,P] ∈ C^∞(O,P)`, continuous in `f` | VII.1.2, III.6, III.1.2, II.1.5 | Book | none |
| Lemme VII.1.4 | 317 | `ψ_f` is `°c`-invariant | VII.1.1, V.3.1 | Book | none |
| Prop. VII.2.1 | 317 | `(f_ψ)^(ω',P)` in terms of `ψ` | VI.4.1, VII.1.2, III.1 (2), (3) | Book | none |
| Prop. VII.2.2, Cor. VII.2.3 | 318–319 | orthogonality of wave packets for non-conjugate Levis; inner-product formula | VI.2.2, VII.1, VI.4.1, VII.2.1 | Book | none |
| VII.2 | 319 | Hermitian product on `C^∞(Θ)_inv`, positive definite, `G × G`-invariant | VII.2.2 | Data, Book | none |
| Rem. VII.2.4, Thm VII.2.5 | 320 | main targets above | VII.2.1–VII.2.3, VII.1.4 | Book | none |

## Chapter VIII. Plancherel formula (pp.320–332)

| Item | Page | Content | Uses | Class | Lean coverage |
|---|---|---|---|---|---|
| Thm VIII.1.1, VIII.1 (1)–(3) | 320 | main targets above | VII.1.1, VII.2.4, VIII.2–VIII.5 | Book | none |
| Thm VIII.1.2, Rem. VIII.1.3 | 321 | finiteness of `Θ^H_G`; finiteness of `Θ^H` by induction on semisimple rank | VIII.4.1, VIII.4.2 (proof in VIII.5) | Book | none |
| VIII.2, Lemme VIII.2.1 | 321–322 | `°f = f − κ(ψ)`; `°C(G)` = cuspidal Schwartz functions | VII.1.2, VII.2.5, III.6, VIII.1 (2) for Levis | Data, Book | none |
| Rem. VIII.2.2, Lemme VIII.2.3 | 322–323 | symmetries of `°`; `f_1 * f_2 = f_1 * °f_2` for cuspidal `f_1` | VII.2, VIII.2.1 | Book | none |
| Prop. VIII.3.1 | 323–326 | for `f_1 ∈ °C(G)`, `f_2 ∈ C(G)` and every `r ∈ ℝ`, the bound `≤ c δ_0(a)(1+σ(a))^{-r}` on `∫_G f_1(a g a^{-1}) f_2(g) dg` for `a ∈ Ā_0^+ ∩ G^1` (the Lean estimates are stated on an arbitrary supplied set `T`) | II.3, II.4, II.1, VIII.2.1 | Book | generic: `conjugationIntegralBound_of_split` (from the decomposition of the integral, estimate (3) `ConvolutionWeights.lintegral_conj_mul_le` and the cuspidal estimate `lintegral_cuspidal_le`); the decomposition from open-cell data: `integral_conj_mul_eq_split`, `conjugationIntegralBound_of_openCell`; inequality (2) from II.3.5: `conjugationSigmaBound_of_openCellBound` |
| Cor. VIII.3.2 | 326 | absolute convergence over `A_G\G` | VIII.3.1, I.1 (4), (5) | Book | `lintegral_lt_top_of_conjugationIntegralBound` (generic: cover, measure bound and summability as hypotheses) |
| VIII.4, Prop. VIII.4.1 | 327–330 | `p_χ`, `°C_H`; `p_χ(°C_H)` finite-dimensional | VIII.2, VIII.3.2 | Data, Book | `centralProjection`, `Space.centralProjection` (`p_χ` with absolute convergence, `χ`-covariance and bi-invariance, generic); the estimate on `G^1` in the proof of VIII.4.1, `enorm_centralProjection_le_rpow_neg`; the reproducing-kernel step of the proof, `IsReproducingKernel.finiteDimensional` (generic); VIII.4.1 itself open |
| Thm VIII.4.2 | 330 | `p_χ(°C(G)) = A_2(G)_χ` | III.1 (2), VII.2.5, VIII.2.2, VIII.2.3, VIII.4.1 | Book | none |
| VIII.5 | 331–332 | proofs of VIII.1.2 and VIII.1.1 | VII.2.5, VIII.1.3, VIII.4.1, VIII.4.2 | Book | none |

## Library coverage

The declarations below formalize parts of the article in the Library at commit
`cf45df06`. The list covers the modules of this task's two executors and other
modules found by searching the Library for the article and for the reductive
data of I.1; it is not the declaration-level reuse audit of condition 7. None
proves a theorem of Chapters IV–VII; for VIII.3.1, VIII.3.2 and VIII.4 there are
generic versions with explicit hypotheses (see below). Most work over explicit
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
prove `G = P K` or the Cartan decomposition (4). It has the unproved Prop
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
unproved Prop `StandardCocharacterStatement`, local compactness and the
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
Prop target `RelativeWeylCoxeterStatement` (statement only). Representative data for the Cartan decomposition
(`RenardUniformizerSection`, `RenardRepresentativeData`, Worker 454) and the
Prop targets `RenardLatticeComparisonStatement` and
`RenardDominantComparisonStatement` are in
`Langlands/Representation/Plancherel/`; those targets are statements only.

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
`RenardLatticeComparisonStatement`), with no proof. Entries marked
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
  the Prop `RationalSmoothRealDescentStatement` (Renard V.3.19, statement only).

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
  `TorusNormKernelCompactnessStatement` (compactness of the norm kernel of a torus; statement
  only).

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
  and the published rational-point topology (I.1 (2)). The identification of Waldspurger's
  `P = M U` with `P_G(χ) = Z_G(χ) U_G(χ)` and the Haar-null complement of the open cell are
  not proved.
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
  contains a compact open one). The rest of Cor. III.7.2 is open.
- `TraceCoefficientFamily`: `averageProjection`, `traceCoefficient` (`ψ_H(g)`, the trace of the
  compressed action of `g` on `V^H`), `traceCoefficient_conj`, `traceCoefficient_mem_range`,
  `finiteRankTrace_eq_traceCoefficient`, `integral_normalizedIndicator_mul_traceCoefficient`,
  `traceCutoff` (`φ_H = φ ψ_H` in `C(G)`), `traceFamily` (an `IdempotentFamily`),
  `traceFamily_operator_eval` (proof of Prop. III.7.1: the family `φ_H` and the first displayed
  equality for `π[φ]`; with an open normal subgroup `N` in place of `G^1` such that conjugation
  is trivial on `G/N` and every compact open subgroup lies in `N`, Cor. III.1.2 as the
  hypothesis `HasRapidlyDecreasingCoefficientsOn`, and a right invariant Haar measure). The
  rest of Prop. III.7.1 is open.

Other modules of this directory, whose Markdown names no author:
`DoubleCosetIndexBoundsStatement` with its proof `doubleCosetIndexBounds`
(`DoubleCosetIndexBoundsProof`), `IwahoriContractionUpperBound`
(`doubleCosetIndex_le_unipotent_contraction`), `ContractionHaarIndex`
(`contractedOpenSubgroup_relIndex`, `contractedIntersection_relIndex`) and
`LatticeQuotientVolumeBound` (`latticeCentralQuotientVolume`): index and volume lemmas for
double cosets of compact open subgroups, used by `rationalLatticeQuotientVolume` (see the
introduction of this section; related to the upper bound of I.1 (5)).

Other generic modules: `Langlands.GroupScheme.Rational.Characters` (rational
characters, I.1); `Langlands/Representation/Exponents/CentralEigencharacterExtensionStatement`
(statement only, I.3).

### Parabolic induction, Jacquet modules and unitarity for general groups

These modules belong to other programs (the general Aubert involution, Jacquet modules,
geometric lemma and unitary representations). They are listed for the items of Chapters I and
III that they formalize; authors are named in their own Markdown.

- `Langlands/Representation/Aubert/General/Parabolic`: `normalizedJacquetFunctor`,
  `normalizedInductionFunctor`, `IsSemidirectDecomposition`, `closedHalfCharacter_eq_comp_projection`
  (normalized Jacquet restriction and induction on the categories of smooth complex
  representations, for a locally compact nonarchimedean `G`, `P = M ⋉ U` and closed `U`; the
  induction agrees with that of the sources when `U` is unimodular; I.3).
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
  standard parabolics, I.1; statements only).
- `Langlands/Representation/Unitary/Basic`, `AdmissibleSemisimplicityStatement`,
  `AdmissibleSemisimplicityProof`: `InvariantPositiveForm`, `IsUnitarizable`,
  `AdmissibleUnitarySemisimplicityStatement`, `admissibleUnitarySemisimplicity` (admissible
  unitarizable representations are semisimple, when compact open subgroups are cofinal; the
  last step of the proof of Lemma III.1.3).

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
  VIII.2.1 and VIII.4.2.
- **VIII.1 (3)** follows from VIII.1 (2) with VII.1.1 (iii) and VII.2.4.

The external inputs on these chains are [BZ] (I.3), [C] (I.4.1, I.4.3,
III.1.1, III.1 (2), (3)), [BD] (I.5), [H] (II.2) and [B] (III.6). Sauvageot
[S] is not needed for square-integrable `π`.
