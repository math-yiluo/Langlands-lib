# General Aubert adapters: source-to-declaration and dependency table

This note is the source-to-declaration and dependency table of the initial
adapter unit, task
`593ef603-6672-4424-976c-14e11e920d9c`, of the general Aubert program
`46df6a68-5db4-4428-8044-05151d6ce1f6`. It is written by Workers 23 and 1180.
It records:

* the underlying data;
* the intrinsic construction laws;
* the external structural inputs;
* the still-unproved representation-theoretic prerequisites;
* classification-dependent imports.

Each row gives the exact public declaration. The adapters are conditional on
the named hypotheses listed below, and nothing here finishes the parent theorem.
Its proof-successor publication, final coverage and proof closure belong to the
parent. The parent-side constructions and targets that import these adapters,
directly or transitively, are not tabulated here, except that §1 and §5 each
cite one of their declarations as a cross-reference. Their own Markdown names
their authors:

* the constructions `Aubert.General.Complex`, `StandardComplex`, `Initial`,
  `Terminal`, `Naturality`, `RationalParabolicDecomposition`,
  `RationalAlternatingOperator`, `SupportCategory`,
  `SupportCategoryStatements`, `SupportCategoryReductions` and
  `Aubert.GeneralLinearSpecialization`;
* the target modules `Aubert.General.ContragredientTarget`,
  `CuspidalEigenvalueTarget`, `GeometricK0Target`, `InductionTarget`,
  `InvolutivityTarget`, `JacquetTarget`, `RationalContragredientTarget`,
  `RationalCuspidalEigenvalueTarget`, `RationalInvolutivityTarget`,
  `Aubert.GeneralCorollaryTargets` and `Aubert.GeneralWeylConjugacyTarget`.

Status values: **proved** (a published theorem or definition), **hyp** (a named
hypothesis of a published declaration) and **target** (a published Prop target
awaiting a proof task). The kinds of source input follow the
[Renard Chapter V ledger](../renard/chapter-v-structural-inputs.md):

* **EXT**: an assertion that Renard imports without proof, i.e. a ledger row
  S01–S23. Only these inputs may remain as final conditional assumptions.
* **BOOK**: a deduction that the book carries out, i.e. part of a ledger row
  D01–D08. It is a retained proof obligation, never a final assumption, even
  when it consumes EXT inputs.
* **IMPL**: a comparison between two Library realizations that Renard does not
  state. It is also a retained proof obligation, never a final assumption.

Sources: Aubert 1995 (`aubert-1995-duality`); Renard 2026
(`renard-2026-representations-groupes-reductifs-padiques`), with printed page
= PDF page − 6; BZ77 (`bernstein-zelevinsky-1977-induced-i`); Conrad 2011
(`conrad-2011-weil-grothendieck-adelic-points`); Conrad–Gabber–Prasad 2015
(`conrad-gabber-prasad-2015-pseudo-reductive`).

Library modules are named below without the prefix `Langlands.`. The status
of each row is the state of Library commit `57844290`.

## 1. Underlying data

Modules: [`Aubert.General.Parabolic`](../../Langlands/Representation/Aubert/General/Parabolic.md) (P),
[`Aubert.General.AlternatingOperator`](../../Langlands/Representation/Aubert/General/AlternatingOperator.md)
(A), [`Aubert.General.DynamicParabolic`](../../Langlands/Representation/Aubert/General/DynamicParabolic.md)
(D), [`Aubert.General.Conjugation`](../../Langlands/Representation/Aubert/General/Conjugation.md)
(C) and [`Aubert.General.StandardFamily`](../../Langlands/Representation/Aubert/General/StandardFamily.md)
(S), all under `Langlands.Representation.` and in namespace
`Langlands.Aubert.General`.

| Source object | Declaration | Module | Status |
| --- | --- | --- | --- |
| `G(F)` with its topology (Renard V.2.1; Conrad Prop. 2.1) | `PointTopology.RationalPoint F G.X` (identity-test points `Over.mk (𝟙 _) ⟶ G.X`) with the non-instance topology `PointTopology.rationalPointTopology F G.X` (module `AlgebraicGeometry.PointTopology.RationalPoints`, task `886bf565`); the same topology is `RationalPointFamily.pointTopology` | external | data published; for `[IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]`, Hausdorffness, local compactness, the topological-group property and local profiniteness are proved (C1); `NonarchimedeanGroup` and the closedness of subgroups stay hyp (C1) |
| Parabolic `P = M ⋉ N` (V.3.1) | `IsSemidirectDecomposition P M U`, `IsSemidirectDecomposition.projection` | P | proved (predicate and projection) |
| Dynamic `P(χ), Z(χ), U(χ)` | `dynamic_parabolic_le_normalizer`, `dynamic_isSemidirectDecomposition`, `dynamic_projection_eq_limitHom` | D | proved |
| Standard `P_I, L_I, U_I`, `I ⊆ S` (V.3.8, V.4.2) | families `P M U : Finset ι → Subgroup G` with `h : ∀ I, IsSemidirectDecomposition ..` | A, S | hyp in A. The actual family is published: `Aubert.General.RationalPointFamily.parabolic/levi/unipotent i ν I` for `I : Finset (SimpleRoot i ν)`, which are `standardParabolicPoints/standardLeviPoints/standardUnipotentPoints i ν (rootSet i ν I)` of `GroupScheme.Rational.StandardParabolic` (task `8ace819d`). For `hG : IsConnectedReductive G`, `[IsAffineHom G.X.hom]`, a maximal split torus `i` and a generic `ν`, its decomposition `h` is proved **conditional on** the public target `GroupScheme.StandardCocharacterStatement` (A2), taken as the hypothesis `hstd`: `RationalPointFamily.isSemidirectDecomposition` (S), via `RationalPointFamily.exists_standardCocharacter_eq` (S) and `dynamic_isSemidirectDecomposition`. The parent-side `RationalPointFamily.isSemidirectDecomposition_of_standardCocharacterStatement` (module `Aubert.General.RationalParabolicDecomposition`) proves the same decomposition, also conditional on `StandardCocharacterStatement` |
| `δ_P^{±1/2}` (BZ77 §1.7–1.8; Renard VI.1.2) | `HaarModulus.closedHalfCharacter`, `closedInverseHalfCharacter`, `inductionCharacter` | published, P | proved |
| Smooth categories and exact K0 (Aubert p. 2180) | `SmoothRep`, `SmoothRep.FiniteLengthGrothendieckGroup` | published | proved |

## 2. Constructions and their intrinsic laws

| Source | Declaration | Laws proved | Module |
| --- | --- | --- | --- |
| `r^G_P` (Renard (VI.1.2.2); BZ77 §1.8(b) `r_{U,1}`) | `normalizedJacquetFunctor`, `jacquetFunctor` | `_obj_representation`, `_obj_apply`, `_map_mk`; agrees with BZ77 and Renard for every decomposition | P |
| `i^G_P` (Renard (VI.1.2.1), (VI.1.2.3); BZ77 §1.8(a) `I_{U,1}`) | `inflationFunctor`, `normalizedInductionFunctor`, `inducingRepresentation` | `_obj_representation`, `_covariant`, `_obj_apply`, `_map_eval`; agrees with BZ77 `I_{U,1}` and Renard only under `IsUnimodularModulus U hU` (e.g. from `isUnimodularModulus_of_isLimitOfCompactSubgroups`) | P |
| `i ∘ r` | `inductionJacquetFunctor` | `inductionJacquetTermIso` (`_hom_eval`, `_inv_eval`, `_natural`) to `SubgroupTransition.term`, under `IsUnimodularModulus` | P |
| Normalization comparison | `closedHalfCharacter_levi`, `closedHalfCharacter_unipotent`, `closedHalfCharacter_eq_comp_projection`, `inducingRepresentation_jacquet_eq` | proved, the last three under `IsUnimodularModulus` | P |
| Levi-in-Levi (Renard VI.1.4) | `leviNormalizedInductionFunctor`, `leviNormalizedJacquetFunctor`, `subgroupOfContinuousEquiv` | definitions | P |
| Conjugation `σ ↦ ᵍσ` | `conjugationEquiv`, `conjugationFunctor`, `conjugationK0` | `_obj_apply`, `conjugationK0_ofRepresentation`; unconditional | P, A |
| Compatibility of `i`, `r` with conjugation (Renard VI.2.1 "par conjugaison"; BZ77 §1.7–1.8): `δ_{gUg⁻¹}(gpg⁻¹) = δ_U(p)`, `r_{P'} ≅ c_g ∘ r_P`, `i_P ≅ i_{P'} ∘ c_g`, with the K0 corollaries | `mulEquivHaarChar_trans_symm`, `closedNormalizerCharacter_conj`, `closedRestrictCharacter_conj`, `closedHalfCharacter_conj`, `closedInverseHalfCharacter_conj`, `projection_conj`, `coinvariantsTranslate` (`_mk`, `Equiv`), `conj_inv_iff`, `jacquetConjugationIsoApp`, `jacquetConjugationIso` (`jacquetFunctor h hU ⋙ conjugationFunctor g hMM' ≅ jacquetFunctor h' hU'`), `jacquetConjugationIso_hom_mk`, `coindTranslate`, `inducingRepresentation_conj`, `inductionConjugationIsoApp`, `inductionConjugationIso` (`normalizedInductionFunctor h hU ≅ conjugationFunctor g hMM' ⋙ normalizedInductionFunctor h' hU'`), `inductionConjugationIso_hom_eval`, `inductionK0_comp_conjugationK0`, `conjugationK0_comp_jacquetK0` | proved from both decompositions `h`, `h'`, closedness of `U`, `U'` and the conjugation hypotheses `x ∈ N' ↔ g⁻¹xg ∈ N` for `N = P, M, U`; no unimodularity; the K0 identities take the finite-length and exactness hypotheses of `inductionK0`/`jacquetK0` for both decompositions | C |
| Exactness of `r` and `i` (Renard VI.1.2 Proposition) | `jacquetFunctor_map_isShortExact`, `jacquetFunctor_preservesShortExact`, `normalizedInductionFunctor_map_isShortExact`, `normalizedInductionFunctor_preservesShortExact` | proved for every short exact sequence, under the structural inputs of §3 | A |
| Compact-open cofinality | `compactOpenCofinal_of_nonarchimedean` | `[LocallyCompactSpace H] [NonarchimedeanGroup H] → CompactOpenCofinal H` | A |
| Smooth contragredient (Renard III.1.6) | published `SmoothRep.contragredientFunctor`; `contragredientK0` | `contragredientK0_ofRepresentation` | published, A |
| K0 maps of `i`, `r` | `inductionK0`, `jacquetK0` | `_ofRepresentation`, `inductionK0_comp_jacquetK0` | A |
| `D_G` (Aubert Déf. 1.5, p. 2181) | `alternatingTerm`, `alternatingOperator` | `alternatingOperator_apply`, `alternatingOperator_ofRepresentation` (class formula), `alternatingOperator_of_isEmpty` (empty root set) | A |
| `D_{L_J}` | `leviIndex`, `leviAlternatingOperator` | `card_leviIndex`, `leviAlternatingOperator_eq` | A |
| `i_I`, `r_I` and `D_G` for the actual standard family `P_I(k) = L_I(k) ⋉ U_I(k)`, `I ⊆ S` | `RationalPointFamily.standardInductionFunctor`, `standardJacquetFunctor`, `standardAlternatingOperator` | `standardAlternatingOperator_eq` (by `rfl`, the instance of `alternatingOperator` for the standard family, so its class formula and empty-root-set laws apply); conditional on `hstd : StandardCocharacterStatement`, with the topology of `G(k)` as instance arguments (`[TopologicalSpace] [LocallyCompactSpace] [NonarchimedeanGroup]`, to be bound to `rationalPointTopology`), closed `U_I(k)` and, for the operator, `[Fintype (SimpleRoot i ν)]` and `hfl : ∀ I, ParabolicFiniteLength ..` | S |

## 3. Named hypotheses of the adapters and what discharges them

| Hypothesis (exact Lean form) | Used by | Status | Discharge |
| --- | --- | --- | --- |
| `[LocallyCompactSpace G] [NonarchimedeanGroup G]`, `[T2Space G]` | all functors; induction exactness | EXT (C1, ledger S04); `T2Space` and `LocallyCompactSpace` proved | Renard V.2.1 (row C1 below), for `PointTopology.rationalPointTopology`. For `[IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]`, `T2Space` and `LocallyCompactSpace` are proved on `RationalPoint F G.X` (`PointTopology.rationalPoint_t2Space` with `BruhatTits.localField_t2Space`, and `PointTopology.rationalPoint_locallyCompactSpace`). `NonarchimedeanGroup` is not published; it is one step from the published `BruhatTits.rationalPoint_isLocallyProfinite` by van Dantzig (`Topology.LocallyProfiniteProof.vanDantzig`) (C1) |
| `hU : IsClosed (U : Set G)`, `hP : IsClosed (P : Set G)` | all functors; induction exactness | EXT (C1, S04) | C1 (F-points of closed subgroups are closed). The scheme-level closedness of `P(χ)`, `U(χ)` and the closed-embedding property are published; the point-level bridge is not (C1) |
| `hproj : Continuous h.projection` | `normalizedInductionFunctor_preservesShortExact` | EXT (C1, S04, applied to A1) | By `dynamic_projection_eq_limitHom` (D) the projection is `Dynamic.limitHom χ T`, which mathematically is the map on points of the limit morphism `P(χ) → Z(χ)` (CGP Lemma 2.1.5). Its continuity therefore follows from the continuity of point maps of morphisms in C1, and with continuous multiplication it gives the homeomorphism `M(F) × N(F) → P(F)`. Continuity of the point maps of morphisms on `RationalPoint F G.X` is not published (routed to Worker 105) |
| `hcof : CompactOpenCofinal G` | induction exactness, `contragredientK0` | proved from C1 | `compactOpenCofinal_of_nonarchimedean` (A) from `[LocallyCompactSpace] [NonarchimedeanGroup]` |
| `hUc : Jacquet.Localization.IsLimitOfCompactSubgroups U` | `jacquetFunctor_preservesShortExact`, `isUnimodularModulus_of_isLimitOfCompactSubgroups` | EXT (K4, S22) | Renard V.5.2(iii), p. 123 ([24] §2.1). For `U(χ)(F)` it is implied by the public target `BruhatTits.DynamicUnipotentCompactOpenContainmentStatement` (Worker 6, task `15df7cd7`: every compact subset of `U(χ)(F)` lies in a compact open subgroup), on the same pinned topology; the one-step bridge is not published. Two published prerequisites of its proof are `BruhatTits.rationalPointCompactOpenSubgroup` and `Langlands.compactOpenContainment_of_contractingFamily` (`Topology.CompactOpen.Contraction`); the target itself is open |
| `IsUnimodularModulus U hU` | term comparison | proved from `hUc` | the published theorem `isUnimodularModulus_of_isLimitOfCompactSubgroups` (P) |
| `ParabolicFiniteLength h hU` | `inductionK0`, `jacquetK0`, `alternatingOperator` | target (finite-length conjuncts); exactness conjuncts proved | `ParabolicFiniteLength.of_preservesFiniteLength` from the targets of §5 and the rows above |
| `ContragredientPreservesFiniteLength H` | `contragredientK0` | target | §5 |

## 4. External structural inputs and retained in-book obligations (Renard Chapter V)

Renard calls Chapter V "un catalogue de résultats, pas tous démontrés ici"
(p. 103). V.3 refers to Borel–Tits 1965 [7] and Springer [42]. V.5 refers to
Bruhat–Tits 1972 [14] and Deligne [24]. Each row names an input that the
adapters or the targets need on the actual objects, its row in the
[Chapter V ledger](../renard/chapter-v-structural-inputs.md), and the owner's
answer. The Kind column uses the legend above. Only EXT rows may remain as
final assumptions. BOOK and IMPL rows are retained proof obligations even when
they consume EXT rows, and a row consumed by a deduction is named in that
deduction's row. Several inputs are now public Prop targets of their owners,
but none of them is proved in general yet. The adapters therefore keep each one
as a named hypothesis or a family parameter (§3). A hypothesis whose source row
is BOOK or IMPL must eventually be proved rather than assumed.

| Id | Renard locator | Ledger | Needed input | Kind | Owner and answer | Status |
| --- | --- | --- | --- | --- | --- | --- |
| C1 | V.2.1 p. 104 | S04 | `G(F)` is a Hausdorff, locally compact, totally disconnected topological group, with topology independent of the embedding; `F`-points of closed `F`-subgroups are closed. The unimodularity announced in V.2.1 is not part of C1; it is proved in V.5.4 (K5, D07) | EXT | Conrad point-topology task `886bf565` (Workers 105, 208). The carrier and topology are published (`AlgebraicGeometry.PointTopology.RationalPoints`). `rationalPointTopology` is by definition the transport, along `rationalPointHomeomorph`, of the evaluation topology on `RingPoint F G.X F`. For that topology, Conrad Prop. 2.1 is proved in `AlgebraicGeometry.PointTopology.AffineGroupProofs` (`affineGroupPointProperties_proof`): `T2Space`, `LocallyCompactSpace` (affine, locally of finite type, Hausdorff locally compact topological value ring), `IsTopologicalGroup`, and closed embeddings for closed immersions (also `isClosedEmbedding_affineSchemePointMap`). The dynamic subgroups are closed subgroup schemes of a corepresented affine group (`GroupScheme.Corepresented.isClosedSubgroup_parabolicHom`, `_centralizerHom`, `_unipotentHom` in `GroupScheme.Dynamic.Representability`). The transfer to the identity-test carrier `RationalPoint F G.X`, for `[IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]`, is published. In `AlgebraicGeometry.PointTopology.RationalPointGroups`, `rationalPointGroupEquiv` shows that the two group laws agree, and the module proves `rationalPoint_isTopologicalGroup`, `rationalPoint_t2Space` and `rationalPoint_locallyCompactSpace`. In `BruhatTits.Unipotent.RationalPointCompactOpen`, `localField_t2Space`, `rationalPoint_totallyDisconnectedSpace` and `rationalPoint_isLocallyProfinite` are proved over a nonarchimedean local field, together with a compact open subgroup (`rationalPoint_exists_compactOpenSubgroup`, `rationalPointCompactOpenSubgroup`). Not published: `NonarchimedeanGroup` as a declaration (one step from local profiniteness by `Topology.LocallyProfiniteProof.vanDantzig`), the closedness of `P(χ)(F)` and `U(χ)(F)` in `G(F)`, and the `P = M × N` homeomorphism, which is routed to Worker 105 | open (hyp; Hausdorff, locally compact, topological group and locally profinite are proved) |
| A1 | V.3.1 p. 110 | S06 | `P = M ⋉ N` on `F`-points | EXT | Published `Dynamic.parabolic/centralizer/unipotent` and the complement theorem, used by `dynamic_isSemidirectDecomposition` (D). The rational-point factorization is also published in `GroupScheme.Rational.PointDecomposition` (`GroupScheme.RationalPoint.parabolic/levi/unipotent χ`, `unipotent_normal`, `levi_inf_unipotent`, `limitHom`, `semidirectEquiv`). Identifying an arbitrary `F`-parabolic with a dynamic one stays with `2b5e4a00` (Worker 1107) | proved for dynamic subgroups |
| A2 | V.3.8 p. 111, V.3.9 p. 112; V.4.2 p. 118 | S10, S15 | Standard parabolics `P_Θ = M_Θ N_Θ`, `Θ ⊆ Δ` ([7], 5.12–5.18), monotone, `P_∅` minimal, `P_Δ = G`, each with a unique Levi containing `A_∅`; every parabolic is conjugate to a standard one (V.3.9) | EXT | Child `8ace819d` of `2b5e4a00`. Published data: `GroupScheme.Rational.StandardParabolic` (`standardParabolic/standardLevi/standardUnipotent i ν J`, their points, `standardRelativeWeylGroup`) and the Finset-indexed `Aubert.General.RationalPointFamily` (§1). Public targets (statements only): `GroupScheme.StandardCocharacterStatement` (standard subgroups are dynamic subgroups of a standard cocharacter), `StandardParabolicEndpointsStatement`, `StandardParabolicOrderStatement`, `StandardParabolicClassificationStatement`. For GL, `GeneralLinearStandardParabolicStatement` is proved by `GroupScheme.generalLinearStandardParabolic` (`GroupScheme.Rational.GeneralLinearStandardParabolicProof`). For dynamic rational parabolics, the conjugacy of V.3.9 (with uniqueness of the standard index) is the second clause of `StandardParabolicClassificationStatement`; B3b and K3 consume it | open in general (public targets; family parameter in A, and the family's decomposition is proved in S conditional on `StandardCocharacterStatement`); proved for GL |
| A3 | V.3.10–V.3.11 p. 112 | S11 | Levi-in-Levi: `M_Θ ∩ P_Θ'` is standard in `M_Θ`, and `N_Θ' = (M_Θ ∩ N_Θ') N_Θ` | EXT | Public target `GroupScheme.StandardLeviIntersectionStatement` (task `8ace819d`): for `J ⊆ K`, `L_K ∩ U_J` is a normal complement of `L_J` in `L_K ∩ P_J` on every test object, and `U_J(F) = (L_K(F) ∩ U_J(F)) U_K(F)` | open (public target) |
| B1 | (V.3.5.1) p. 110; V.3.7 p. 111 | S08, S09 | `W_G = N_G(A_∅)(F)/Z_G(A_∅)(F)` acts faithfully on characters and is the Weyl group of the reduced relative root system `Σ_∅` ([7], 5.3 and cor. 5.8) | EXT | `6edfb074` (Worker 176): `GroupScheme.relativeWeylGroup` (`GroupScheme.Rational.RelativeRoots`) public; `standardRelativeWeylGroup` (A2) and `RationalPointFamily.Weyl/LeviWeyl` public. The identification with a Coxeter group on the actual simple roots enters through the public target `Aubert.General.RationalPointFamily.RationalRootSignCoxeterStatement` (`Aubert.General.RationalRootSignTarget`; see B2) | open (public target) |
| B1b | V.4.3 p. 119 | D06 | The embedding `W_M ↪ W_G` (V.4.3.1), the lift-independent action `w·M`, the sets `W(L, M)` (V.4.3.2) and `W(M, M)/W_M ≃ W(A)` (V.4.3.3), which the book deduces from `M_∅ ⊂ M` and conjugacy of maximal split tori | BOOK | `6edfb074`: public target `GroupScheme.StandardLeviConjugationStatement` (transport of `L_J` by a normalizing point, and independence of the lift). Its second clause, the lift independence, is proved by `GroupScheme.standardLevi_comap_innerIso_inv_eq_of_relativeWeyl_eq` (`GroupScheme.Rational.StandardLeviLiftIndependence`), without the reductivity, maximal-splitness, genericity or simple-root-subset hypotheses; the transport clause is open. `RationalPointFamily.LeviWeyl` and `pointStandardWeyl` (`Aubert.General.RationalLeviWeylComparison`) are public; their comparison with the scheme-side Levi Weyl groups is conditional on the IMPL row B1c | open (public target, lift-independence clause proved; retained proof obligation) |
| B1c | none (Renard V.4.1, V.4.3 use only the point-image quotient) | none | (i) The scheme normalizer and centralizer points equal the abstract normalizer and full centralizer of the torus point image, so that `GroupScheme.relativeWeylGroup i ≃* RationalPointFamily.Weyl i`. (ii) The compatibility of reflection conjugacy with equality of positive simple-root images | IMPL | (i) is the public target `Aubert.General.RationalPointFamily.RationalWeylComparisonStatement` (`Aubert.General.RationalWeylComparisonTarget`); `weylEquiv` is proved conditional on both equalities. (ii) is the `PositiveSimpleReflectionComparison` clause of `RationalRootSignCoxeterStatement`, which its Markdown calls an internal formulation | open (public targets; retained proof obligation) |
| B2 | V.4.1 p. 118 | S13 | `(G, P_∅, N_G(A_∅), S_∅)` is a Tits system ([7]), with the Bruhat decomposition `G = ⊔ P_∅ w P_∅`; the Coxeter structure of `(W_G, S_∅)` is part of this imported Tits-system theory (and of the root-system identification S09) | EXT | `GroupScheme.RationalBruhatStatement` and the first clause of `GroupScheme.StandardParabolicPointsStatement` (standard Bruhat pieces of `P_J(F)`, Borel–Tits 5.17 according to its Markdown) are public as statements only; there is no Tits system. The Coxeter realization of the point-image Weyl quotient on the actual simple roots is the Coxeter-system part of `RationalRootSignCoxeterStatement` | open (public targets) |
| B3 | V.4.5 Lemma p. 119 | S16 | For semistandard `P = MN`, `Q = LU` with standard Levis, the `Q`-orbits on `P\G` correspond to `W_M\W_G/W_L` ([7], 5.15–5.20) | EXT | Last clause of `GroupScheme.StandardParabolicPointsStatement`: `W_J\W/W_K ≃ P_J(F)\G(F)/P_K(F)` through normalizer points, for standard `P_J`, `P_K` (public target, `8ace819d`) | open (public target) |
| B3b | V.4.5 Corollary p. 120 | D06 | For arbitrary parabolics `P`, `Q`, the set of `Q`-orbits on `P\G` is finite | BOOK | Renard deduces it from B3, the finiteness of `W_G` (B1) and the conjugacy of every parabolic to a standard one (V.3.9, in A2). It is not stated as a Library target (item 7 of Worker 176's requests) and is a retained proof obligation of the reductive-group program | open (retained proof obligation) |
| B4 | V.4.6–V.4.7 pp. 120–121 | D06, consuming S17–S18 | Minimal representatives `W^{L,M}`; `P ∩ w·Q = (P ∩ w·L)(P ∩ w·U)` | BOOK | The deduction consumes two EXT inputs. The first is S17, the root–length facts of [43], including `ℓ(w s_γ) > ℓ(w)` iff `wγ > 0`; this is the `RootLengthComparison` clause of `RationalRootSignCoxeterStatement`. The second is S18, the Coxeter minimal-representative result ([9], IV §1, Ex. 3). `RationalPointFamily.rootSet_associatedSubset` proves a conditional consequence for associated subsets. The intersection decomposition is not yet routed (parent obligation) | open (retained proof obligation) |
| K1 | V.5.1 (1)–(3), (5) p. 122 | S19 | Good maximal compact `K_0`: `G = K_0 P_∅`, Weyl representatives in `K_0`, `K_0 ∩ P = (K_0 ∩ M)(K_0 ∩ N)` | EXT | `f33d727f` (Worker 118) | open |
| K2 | V.5.1 (4) p. 122 | S19 | Cartan decomposition `G = ⊔ K_0 a K_0` | EXT | `f33d727f` | open |
| K3 | V.5.1 Corollary p. 123 | D07 | Every parabolic is `K_0`-conjugate to a standard one; `G(F)/P(F)` is compact | BOOK | Renard's corollary consumes the Iwasawa decomposition `G = K_0 P_∅` (K1) and the conjugacy of every parabolic to a standard one (V.3.9, in A2): a conjugating element `g = k p` with `k ∈ K_0`, `p ∈ P_∅` gives `K_0`-conjugacy, and `G/P` is then the continuous image of the compact `K_0`. It is not an additional permitted assumption. Owner `f33d727f` (D07). Compactness of `G(F)/P(χ)(F)` (both coset conventions, pinned topology) is the public target `BruhatTits.DynamicParabolicQuotientCompactStatement`, which is a retained proof obligation. Its improper case is proved: when `P(χ)` is the whole group, both quotients are compact for every point topology (`GroupScheme.Dynamic.compact_quotients_of_parabolic_eq_top`, and `compact_quotients_trivialCocharacter` for the trivial cocharacter, in `GroupScheme.Dynamic.ImproperParabolic`) | open (public target for compactness, improper case proved; retained proof obligation) |
| K4 | V.5.2 p. 123 | S20–S23 | A basis of compact open `K ⊲ K_0` with Iwahori decompositions for all standard `P`, and the contraction properties (iii)–(iv) | EXT | `f33d727f`. The S22 piece is the public target `BruhatTits.DynamicUnipotentCompactOpenContainmentStatement` (Worker 6, task `15df7cd7`), which implies `hUc` (§3). Its published proof prerequisites are `BruhatTits.rationalPointCompactOpenSubgroup` (a compact open subgroup of `G(F)`) and `Langlands.compactOpenContainment_of_contractingFamily` (a continuous contraction family transports a compact open subgroup to one containing a given compact set) | open (hyp; the target is unproved) |
| K5 | V.5.4 pp. 126–127 | D07 | `G(F)` unimodular; `δ_{P\G} = δ_P^{-1}`; root formula for `δ_P` | BOOK | `f33d727f` (D07); Worker 118 notes an orientation caveat on `HaarModulus.normalizerCharacter` (see the ledger's section on modulus orientation) | open (retained proof obligation) |

## 5. Representation-theoretic prerequisites (Prop targets)

Module [`Aubert.General.PrerequisiteStatements`](../../Langlands/Representation/Aubert/General/PrerequisiteStatements.md)
(Worker 1180), namespace `Langlands.Aubert.General`. Each target is a closed `Prop`. It quantifies over a
nonarchimedean local field `F` (`[Field F] [ValuativeRel F] [TopologicalSpace F]
[IsNonarchimedeanLocalField F]`), a group scheme `G` over `Spec F` with
`IsConnectedReductive G`, and, where relevant, a cocharacter `χ`. `G(F)` is
`RationalPoint F G.X` with `letI := rationalPointTopology F G.X`. The subgroups
are the dynamic subgroups at `T = Over.mk (𝟙 (Spec (CommRingCat.of F)))`. The
only hypotheses are properties of that pinned topology that a functor or the
contragredient needs in order to typecheck (`[IsTopologicalGroup]`, or
`[LocallyCompactSpace] [NonarchimedeanGroup]` and `hU`).

| Renard | Declaration | Lean content | Status |
| --- | --- | --- | --- |
| VI.6.3 p. 178 (with VI.2.2 p. 140) | `RationalPointsFiniteLengthAdmissibleStatement` | finite length ⇒ `IsAdmissible` for `G(F)` | target |
| VI.6.3 for the Levi | `DynamicLeviFiniteLengthAdmissibleStatement` | the same for `Z(χ)(F)` | target |
| derived: VI.6.3, I.4.1 p. 23, I.5.1 Cor p. 26, III.1.6–III.1.7 pp. 61–62 | `RationalPointsContragredientFiniteLengthStatement` | `ContragredientPreservesFiniteLength (RationalPoint F G.X)` | target |
| the same for the Levi | `DynamicLeviContragredientFiniteLengthStatement` | `ContragredientPreservesFiniteLength Z(χ)(F)` | target |
| VI.6.2 p. 178 | `DynamicInductionFiniteLengthStatement` | `PreservesFiniteLength (normalizedInductionFunctor (dynamic_isSemidirectDecomposition χ T) hU)` | target |
| VI.6.4 p. 179 | `DynamicJacquetFiniteLengthStatement` | `PreservesFiniteLength (jacquetFunctor (dynamic_isSemidirectDecomposition χ T) hU)` | target |
| — | `rational_parabolicFiniteLength` | the two functor targets, with C1 and K4 inputs (`T2`, closed `P(χ)(F)`, continuous projection, `hUc`) and cofinality from `compactOpenCofinal_of_nonarchimedean`, give `ParabolicFiniteLength (dynamic_isSemidirectDecomposition χ T) hU` | proved (conditional) |

The Levi targets use `Z(χ)(F) ⊂ G(F)` with the subspace topology, which is its
own point topology by Renard V.2.1. To apply the `G`-level targets to Levi-in-Levi
data, one needs `Z_G(χ)` as a connected reductive group scheme in the Library.
That is structural (A3; `2b5e4a00`, `8ace819d`).

Results that are not stated as targets, with their existing owners:

| Renard | Reason | Existing Library owners |
| --- | --- | --- |
| Transitivity VI.1.4 p. 137 | needs the standard decompositions and Levi-in-Levi inputs (A2–A3), which are only public targets | `Induction.StructuralStatement` (transitivity and exactness clauses, unnormalized); `Induction.CompactInductionTransitivityStatement` |
| Geometric lemma VI.5.1 p. 161 | needs the double-coset input B3 (EXT) and the deductions B3b and B4 (BOOK), which are open | `Geometric.ClosedSubgroupMackeyFiltration`; `PadicGeometricLemmaTheorem` (GL only); `Geometric.General.*` (task `a2a442fc`, BZ 5.1 data); the parent-side K0 form, Aubert identity (1.3), is the target `Aubert.General.GeometricK0ExpansionStatement` (module `Aubert.General.GeometricK0Target`) |
| Second adjointness VI.9.6 p. 201 | needs opposite-parabolic and K4 inputs | only GL-specific work |
| Conjugation compatibility | an intrinsic law of the generic layer (§2), not a representation-theoretic prerequisite | `conjugationFunctor`, `conjugationK0`; the compatibility isomorphisms `jacquetConjugationIso`, `inductionConjugationIso` and the K0 identities `inductionK0_comp_conjugationK0`, `conjugationK0_comp_jacquetK0` of `Aubert.General.Conjugation` (§2) |

## 6. Classification-dependent imports and helper proofs

No declaration of the modules P, A, D, C, S or `PrerequisiteStatements` uses a
Langlands classification theorem. Their transitive Library import closure (367
`Langlands` modules, 334 without S, counting `import` lines) contains GL modules
under `Representation/Classification/`, because published generic
infrastructure lives there. C, S and `PrerequisiteStatements` add no such module.
The only helper used is
`FiniteLengthAssembly.finiteLength_comp_surjective_iff`
(`Classification.FiniteLengthProof`), through the published
`SmoothRep.pullbackFunctor_preservesFiniteLength` used by `conjugationK0`. It is
a generic statement that module length is invariant under a surjective
change of group. The contragredient category module `Category.Contragredient`
imports `Classification.SupercuspidalContragredientAux`; `contragredientK0` uses
only `contragredientIso` and `smoothContragredientShortExact` from it and its
dependencies.
