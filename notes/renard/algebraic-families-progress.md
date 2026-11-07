# Renard VI.8: algebraic families of representations

Worker 709 wrote this note on 6 November 2026 against Library
`f73044d93e675a78ed75830ef026b3224514e510` and updated it on 7 November 2026
against Library `d82893a7de0b168873a15c6c7b0a731deb27aa23`. It maps every printed assertion
of VI.8, and the proof steps the source spells out, to the published Lean
declarations that state or prove them. Where no declaration does, the note
says so. It also records six source reading notes. Worker 6 owns the other
Chapter VI notes, such as the
[parabolic functors note](parabolic-functors-tempered-progress.md), and this
note does not change them.

Thirty-one published units carry the material or relate to it. They are
eleven statement units, eight proof units and twelve definition units, listed
under Receipts. Worker 709 is the sole author of the statement unit
`51d6b0a6` and is neither an author nor a coauthor of the other thirty. This
note documents them and is not a review of them.

## Source context

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Printed page `p` is PDF page `p + 6`. VI.8, "Familles algébriques de
représentations", is on printed pp.187–195 / PDF pp.193–201. It begins on
PDF p.193 after the Theorem that ends VI.7 and ends on PDF p.201 before
VI.9. Its subsections are on these printed pages: VI.8.1 on pp.187–189,
VI.8.2 on pp.189–191, VI.8.3 on p.191, VI.8.4 on pp.191–193, VI.8.5 on
pp.193–194 and VI.8.6 on pp.194–195. Worker 709 read PDF pp.193–201 for this
note.

Throughout VI.8, `B` is a reduced commutative Noetherian `ℂ`-algebra of
finite type, and `S` is the affine variety with coordinate ring `B`,
identified with the maximal spectrum of `B`. A point `χ ∈ S` corresponds to
an algebra morphism `Ψ_χ : B → ℂ` with kernel `I_χ`. The labels below are
this note's, not the source's.

VI.8.1, "`(G, B)`-modules":

- (D) Definition. A `(G, B)`-module is a complex vector space `V` with a
  smooth representation of `G` and a structure of flat `B`-module, the two
  actions commuting. They form the category `M(G, B)`. Such a `V` is
  admissible if every `V^K`, for `K` compact open, is a finitely generated
  `B`-module.
- (P1) Proposition. Let `V` carry a smooth representation of `G` and a
  commuting `B`-module structure, not assumed flat. Then `V` is an
  admissible `(G, B)`-module if and only if every `V^K` is a finitely
  generated projective `B`-module. The proof cites Corollary A.X.5 and
  Proposition 5 of A.X.4 in [12]: over the Noetherian ring `B`, a finitely
  generated module is flat if and only if it is projective.
- (P1-iso) A step of that proof: for every `B`-module `E`, the natural map
  `E ⊗_B V^K → (E ⊗_B V)^K` is an isomorphism, with inverse
  `e ⊗ v ↦ e ⊗ e_K v`.
- (R1) Remark. For `V` as in (P1), `V` is a flat `B`-module if and only if
  every `V^K` is. The Remark records an argument used at the end of the
  proof of (P1).
- (Sp) Specialization. For `χ ∈ S`, `V_χ = V ⊗_B B/I_χ` is still a smooth
  representation of `G`, with the canonical map `sp_χ : V → V_χ`.
- (L1) Lemma. If `V` is admissible, so is every `V_χ`.
- (Ex-a) Example. Let `(π, V)` be smooth, `B = ℂ[Λ(G)]` the coordinate ring
  of the variety `X(G)` of unramified characters, and `χ_un : G → B^×`
  evaluation at points of `G`. Then `V_B = V ⊗_ℂ B`, with
  `π_B(g)(v ⊗ b) = π(g)v ⊗ χ_un(g) b`, is a `(G, B)`-module, free over `B`.
- (Ex-b) In the Example, `V_B^K = V^K ⊗ B`, so `V_B` is admissible when `V`
  is.
- (Ex-c) In the Example, the specialization of `V_B` at `χ ∈ X(G)` is
  `π ⊗ χ`.

VI.8.2, "`(G, B)`-modules et induction":

- (I) For a parabolic `P = MN` and an `(M, B)`-module `E`, `i_P^G(E)` is a
  `(G, B)`-module, and `i_P^G` is a functor `M(M, B) → M(G, B)`. Flatness
  follows from (R1) and
- (VI.8.2.1) `i_P^G(E)^K ≅ ⊕_{g ∈ Ω} E^{K_M^g}`, where `Ω` is a finite set
  of representatives of `P\G/K` and `K_M^g` is the projection of
  `P ∩ gKg⁻¹` to `M`.
- (L2) Lemma. `i_P^G` sends admissible modules to admissible modules.
- (BC) Base change. For a commutative Noetherian reduced `ℂ`-algebra `C`
  over `B`, `V ↦ V ⊗_B C` is a functor `M(G, B) → M(G, C)`.
- (P2) Proposition. Base change commutes with parabolic induction:
  `i_P^G(E) ⊗_B C ≅ i_P^G(E ⊗_B C)` as `(G, C)`-modules, through
- (VI.8.2.2) the map `f ⊗ c ↦ f̃`, `f̃(g) = f(g) ⊗ c`.
- (C2) Corollary. Specialization commutes with parabolic induction:
  `sp_χ(i_P^G(E)) ≅ i_P^G(E_χ)` for every `χ ∈ S`, through
  `f̃(g) = sp_χ(f(g))`.

VI.8.3, "`(G, B)`-modules et restriction":

- (J) For a `(G, B)`-module `V`, `r_P^G(V)` is a flat `B`-module, since
  `E ⊗_B r_P^G(V) ≅ (E ⊗_B V) ⊗_{H(N)} ℂ`. So `r_P^G` is a functor
  `M(G, B) → M(M, B)`.
- (P3) Proposition. `r_P^G` preserves "`B`-modules de type fini". The source
  presents this as the generalization of VI.1.3 and names the compactness of
  `P\G` as the crucial point.

VI.8.4, "Utilisation de la platitude":

- (T4) Theorem, with proof by reference to [8] II.5 Theorem 1. A `B`-module
  is finitely generated projective if and only if there are `f_1, …, f_r`
  generating the unit ideal of `B` such that each localization at `f_i` is a
  finitely generated free `B_{f_i}`-module.
- (Sp-φ) For an admissible `(G, B)`-module `V` and an endomorphism `φ`, each
  `φ_K : V^K → V^K` is `B`-linear. On a basic open `S_f` where `V^K_f` is
  free, `φ` and `φ_K` have specializations `sp_x(φ)` and `sp_x(φ_K)` at the
  points `x ∈ S_f`.
- (P4) Proposition. Let `ρ` be an irreducible smooth representation of `M`
  and `π_ψ = i_P^G(ρ ⊗ ψ)` for `ψ ∈ X(M)`. If `π_{ψ_0}` is irreducible for
  some `ψ_0`, then `π_ψ` is irreducible for all `ψ` in a Zariski open subset
  of `X(M)`. The proof uses the induced universal family over
  `B = ℂ[Λ(M)]`. It takes `K` with `W^K ≠ 0` for every irreducible
  representation `(τ, W)` of the common inertial support, through the proof
  of VI.7.2 and the Jacquet lemma VI.6.1. By Burnside's theorem, `V_ψ^K` is
  an irreducible `H(G, K)`-module exactly when `H(G, K) → End(V_ψ^K)` is
  surjective, and a determinant shows that surjectivity at `ψ_0` persists on
  a Zariski open set.

VI.8.5, "Irréductibilité générique des induites":

- (T5) Theorem. If `ρ` is irreducible supercuspidal, `π_ψ` is irreducible
  for `ψ` in a nonempty Zariski open subset of `X(M)`. By (P4) it suffices
  to find one irreducible `π_{ψ_0}`.
- (T5-a) Proof step. Twist `ρ` so that it is unitary. The source extends
  `|χ|`, for the central character `χ` of `ρ`, from `Λ(A)` to a character in
  `X(M)`, using that `Λ(A)` has finite index in `Λ(M)` (V.2.6). A
  supercuspidal representation with unitary central character is unitary
  (VI.2.1, IV.3.2).
- (T5-b) Proof step. For unitary `ψ`, `π_ψ` is unitary, hence completely
  reducible. By VI.5.3(iii), `r_P^G(π_ψ)` has a filtration with quotients
  `w·(ρ ⊗ ψ)`, `w ∈ W(M, M)/W_M`. Outside a Zariski closed subset of the
  real variety `Im X(M)`, their central characters are pairwise distinct
  (V.4.3.3, V.3.5, V.3.20).
- (L5) Lemma. A representation with a finite filtration whose successive
  quotients have distinct central characters is the direct sum of those
  quotients.
- (T5-c) Proof step. By Frobenius reciprocity,
  `Hom_G(π_ψ, π_ψ) = Hom_M(ρ ⊗ ψ, ρ ⊗ ψ)` is one-dimensional, so `π_ψ` is
  irreducible.

VI.8.6, "Une autre application":

- (P6) Proposition. In the situation of (Sp-φ), let `Ξ ⊂ S` be Zariski
  dense. If `sp_x(V)` is irreducible for every `x ∈ Ξ`, then `φ` is the
  action of some `b ∈ B`. The proof uses Schur's lemma at the points of `Ξ`
  to make the matrix of `φ_K` on `V^K_f` scalar, with entry in `B_f`.
- (Ex6) Example. For `ρ` irreducible supercuspidal, (T5) and (P6) show that
  every endomorphism of the induced family `V_B` is the action of some
  `b ∈ B`. With `M = P = G`, every element of the centre of the category
  `M(G)[ρ]` acts on `W_B = W ⊗ B` as an element of `B`, which recovers
  VI.4.5.

## Lean model

The VI.8 statements and proofs for the universal family lie in namespace
`Langlands.Plancherel.RationalNormalized` unless stated otherwise. The Lean
files are under `Langlands/Representation/`, except one module under
`Langlands/HarmonicAnalysis/`.

- A family is a `B`-linear representation `Representation B G V`, so the
  actions of `G` and `B` commute by construction. Smoothness (`IsSmooth`)
  and flatness (`Module.Flat`) are separate hypotheses or conclusions. No
  structure or category of `(G, B)`-modules is defined.
- The statements for a general family are in namespace
  `Langlands.Renard.AlgebraicFamily`, in
  [RenardFamilyStatements](../../Langlands/Representation/Families/RenardFamilyStatements.md).
  They quantify over every reduced Noetherian `ℂ`-algebra `B` of finite type
  and every topological group `G` with `Langlands.Topology.IsLocallyProfinite G`.
  A compact open subgroup is `K : OpenSubgroup G` with `IsCompact (K : Set G)`.
  All five statements are unproved.
- `Langlands.IsAdmissible`, in [Smooth/Definitions](../../Langlands/Representation/Smooth/Definitions.md),
  is smoothness together with `Module.Finite R (fixedVectors ρ K)` for every
  open subgroup `K`.
- The coefficient algebra is `RegularAlgebra r`, the regular functions on
  the unramified characters of the Levi's rational norm characters, in
  [UnramifiedRationalNormalizedModels](../../Langlands/Representation/Plancherel/UnramifiedRationalNormalizedModels.md).
  In [UnramifiedRationalCoefficientAlgebra](../../Langlands/Representation/Plancherel/UnramifiedRationalCoefficientAlgebra.md),
  `regularAlgebraLaurentEquiv` identifies it with the Laurent polynomial
  algebra `AddMonoidAlgebra ℂ (Fin (rationalImageRank M) → ℤ)`, the source's
  `ℂ[Λ(M)]`. `regularAlgebra_finiteType`, `regularAlgebra_isNoetherianRing`
  and `regularAlgebra_isDomain` give the VI.8 hypotheses on `B`; a domain is
  reduced.
- `universalRepresentation`, in the same Models module, is
  `Langlands.Plancherel.universalUnramifiedRepresentation`, from
  [UnramifiedUniversalTwist](../../Langlands/Representation/Plancherel/UnramifiedUniversalTwist.md).
  It acts on `B ⊗[ℂ] E` by `g ↦ unramifiedEvaluationRegular ν g • (ρ g).baseChange B`.
  This is the source's `V_B`, with the tensor factors in the order
  `B ⊗ V` instead of `V ⊗ B`.
- `Induced` and `inducedRepresentation` are normalized parabolic induction
  of the universal tensor, through
  [UnramifiedNormalizedTensorModels](../../Langlands/Representation/Plancherel/UnramifiedNormalizedTensorModels.md).
  `Jacquet` and `jacquetRepresentation` are its Jacquet model.
- `RegularAlgebra r` is `unramifiedRegularFunctions ν` for
  `ν = parabolicLeviRationalNormCharacters r`. The module
  [UnramifiedNormalizedModels](../../Langlands/Representation/Plancherel/UnramifiedNormalizedModels.md),
  namespace `Langlands.Plancherel.UnramifiedNormalized`, works over
  `unramifiedRegularFunctions ν` for an arbitrary family
  `ν : I → (L →* ℝ≥0ˣ)` of positive characters. Its `inducedRepresentation`
  is normalized induction of any representation over that algebra. Its
  `normalizedInductionFunctor` is a functor from `SmoothRep` over that
  algebra on the Levi to `SmoothRep` on the group, and its
  `normalizedJacquetFunctor` is the normalized Jacquet functor back. That
  module asserts no flatness or finiteness.
- Specialization at an unramified character `χ` uses `evaluation r χ`,
  `tensorEvaluation`, `inducedEvaluation` and `jacquetEvaluation`, in
  [UnramifiedRationalNormalizedSpecialization](../../Langlands/Representation/Plancherel/UnramifiedRationalNormalizedSpecialization.md),
  and `InducedSpecializationFiber`, the fiber `ℂ ⊗[B] Induced` with `B`
  acting on `ℂ` through `evaluation r χ`, in
  [RationalNormalizedInducedSpecializationStatement](../../Langlands/Representation/Plancherel/RationalNormalizedInducedSpecializationStatement.md).

The published flatness, finiteness and specialization results therefore
concern one family: the universal unramified twist of a smooth representation
of an actual rational Levi, and its normalized parabolic induction. Normalized
induction and Jacquet functors exist over every algebra
`unramifiedRegularFunctions ν`, and normalized induction preserves
admissibility there under the hypotheses of row (L2). For a general `B`,
rows (P1), (P1-iso), (R1), (L1) and (T4) are stated and unproved. No
category of `(G, B)`-modules, no named specialization construction and no
induction or Jacquet functor over a general `B` is defined.

## Assertion map

| Assertion | Published declarations | Status |
| --- | --- | --- |
| (D) | none | Not defined. Families are `Representation B G V` with separate smoothness and flatness hypotheses |
| (P1) | `Langlands.Renard.AlgebraicFamily.AdmissibilityCriterionStatement` in [RenardFamilyStatements](../../Langlands/Representation/Families/RenardFamilyStatements.md). Mathlib: `Module.finitePresentation_of_finite`, `Module.Flat.projective_of_finitePresentation`, instance `Module.Flat.of_projective` | Stated, unproved; proof task `eb5ee8fa-29f5-4671-9ecd-e6259db108d3`. For smooth `ρ`, `V` is flat with every compact-open `V^K` finite if and only if every compact-open `V^K` is finite and projective. The Mathlib lemmas give the algebra: a finite module over a Noetherian ring is finitely presented, and a flat finitely presented module is projective |
| (P1-iso) | `FixedTensorComparisonStatement` (RenardFamilyStatements); private helpers `fixedTensorMap_bijective` and `fixedCoefficientFiber_bijective` in [RationalNormalizedInducedSpecializationProof](../../Langlands/Representation/Plancherel/RationalNormalizedInducedSpecializationProof.md) | Stated, unproved; proof task `eb5ee8fa`. For smooth `ρ`, compact open `K` and every `B`-module `E`, the map `E ⊗[B] V^K → E ⊗[B] V` is injective and its range is `(E ⊗[B] V)^K`, with `G` acting through the second factor. The formula for the inverse is not stated. The private helpers prove the comparison for the universal family and `E = ℂ` through `evaluation r χ`, without a flatness premise |
| (R1) | `FlatnessCriterionStatement` (RenardFamilyStatements); `flat_of_smooth_fixed_flat` in [UnramifiedRationalNormalizedInducedFinitenessProof](../../Langlands/Representation/Plancherel/UnramifiedRationalNormalizedInducedFinitenessProof.md) | The equivalence is stated, unproved; proof task `eb5ee8fa`. The sufficient direction is proved: if `ρ` is smooth and every `fixedVectors ρ K` (`K` compact open) is flat, then `V` is flat. It holds over any commutative ring, with no Noetherian hypothesis, for a locally compact nonarchimedean group. The proof uses the equational criterion `Module.Flat.of_forall_isTrivialRelation`. No declaration proves the converse |
| (Sp) | `evaluation`, `tensorEvaluation`, `inducedEvaluation`, `jacquetEvaluation`; `InducedSpecializationFiber`; `SpecializationAdmissibilityStatement` (RenardFamilyStatements) | Defined for the universal family, its induction and its Jacquet model. For a general family there is no named construction or functor: `SpecializationAdmissibilityStatement` writes the fiber inline as `ℂ ⊗[B] V`, with `B` acting on `ℂ` through `χ : B →ₐ[ℂ] ℂ` and `g` acting by `Module.End.baseChangeHom B ℂ V (ρ g)` |
| (L1) | `SpecializationAdmissibilityStatement` (RenardFamilyStatements) | Stated, unproved; proof task `eb5ee8fa`. For smooth flat `ρ` with every compact-open `V^K` finite, and every `χ`, the fiber `ℂ ⊗[B] V` is `Langlands.IsAdmissible`. Its tensor factors are in the opposite order to the source's `V ⊗_B B/I_χ` |
| (Ex-a) | `universalRepresentation`, `isSmooth_universalRepresentation` (Models); `universalTensorFlatness` in [RationalUniversalTensorFinitenessProof](../../Langlands/Representation/Plancherel/RationalUniversalTensorFinitenessProof.md) | Defined; smoothness proved. Flatness of `B ⊗[ℂ] E` is proved with no admissibility hypothesis |
| (Ex-b) | `RationalUniversalTensorFinitenessStatement` in [RationalUniversalTensorFinitenessStatement](../../Langlands/Representation/Plancherel/RationalUniversalTensorFinitenessStatement.md); proof `rationalUniversalTensorFiniteness`; `universalTensorFixedComparison`, `universalTensorFiniteness`; `Langlands.Plancherel.universalTensorFixedInclusion_bijective`, `Langlands.Plancherel.universalTensorFixed_finite_projective` | Proved. For `σ` admissible, `B ⊗[ℂ] E` is flat, and for every compact open `J` there is an equivalence between the `J`-fixed vectors of `universalRepresentation` and `B ⊗ σ^J` whose inverse is the canonical inclusion `tensorFixedInclusion`; the fixed space is finite and projective. The comparison needs no admissibility; finiteness uses `IsAdmissible σ`. `tensorFixedEquiv`, in the c957a9bb proof module, is a variant over a field `k` for any group. Admissibility of `V_B` itself is also proved: `universalRepresentation_isAdmissible`, in [UnramifiedRationalConjugateAdmissibility](../../Langlands/Representation/Plancherel/UnramifiedRationalConjugateAdmissibility.md), says that `universalRepresentation r σ` is `IsAdmissible` over `RegularAlgebra r` when `σ` is. Its generic form `Langlands.Plancherel.isAdmissible_universalUnramifiedRepresentation` holds for a locally compact nonarchimedean group, continuous `ν` and Noetherian `unramifiedRegularFunctions ν` |
| (Ex-c) | `tensorEvaluation`, `tensorEvaluation_inducing_action` (Specialization) | The map to `π ⊗ χ` is defined and its equivariance is proved. No public theorem says that it identifies the fiber of `V_B` at `χ` with `π ⊗ χ`; the Specialization Markdown makes no fiber claim. (C2) below proves the induced form |
| (I) | `Induced`, `inducedRepresentation` (Models); `Langlands.Plancherel.UnramifiedNormalized.normalizedInductionFunctor` in [UnramifiedNormalizedModels](../../Langlands/Representation/Plancherel/UnramifiedNormalizedModels.md); `universalInduced_flat` (c957a9bb proof module) | The functor is defined: `normalizedInductionFunctor` is normalized induction on smooth representations over any `unramifiedRegularFunctions ν`. Flatness of the induced family is proved for the universal family only. No functor over a general `B` and no flatness of other induced families is stated |
| (VI.8.2.1) | `Langlands.Induction.fixedEvaluationEquiv`, `Langlands.Induction.exists_finset_doubleCoset_representatives` in [FixedVectorModel](../../Langlands/Representation/Induction/FixedVectorModel.md) | Proved for unnormalized `smoothInduced P σ` over any commutative coefficient ring: for a finite set `t` of double-coset representatives, the `K`-fixed vectors are equivalent to `∏ i : t, fixedVectors σ (conjOpenSubgroup P K i)`. The subgroups are literal open subgroups of `P`, and the finite product plays the role of the direct sum |
| (L2) | `Langlands.Induction.smoothInduced_isAdmissible_of_compactSpace` in [CompactQuotientProof](../../Langlands/Representation/Induction/CompactQuotientProof.md); `UniversalInducedCoefficientFinitenessStatement` in [UnramifiedRationalNormalizedInducedFiniteness](../../Langlands/Representation/Plancherel/UnramifiedRationalNormalizedInducedFiniteness.md), proof `universalInducedCoefficientFiniteness`; `universalInducing_fixed_finite_free`, `universalInduced_fixed_finite_free`; `Langlands.Plancherel.UnramifiedNormalized.isAdmissible_inducedRepresentation` (UnramifiedRationalConjugateAdmissibility) | Proved in three forms. The first: unnormalized smooth induction from any subgroup `P` with compact `P\G` preserves `IsAdmissible` over any Noetherian ring. The second: for `π` admissible, the universal normalized induced family is flat and its compact-open fixed spaces are finite and projective. The proof shows they are finite free. The third: over a Noetherian `unramifiedRegularFunctions ν`, normalized induction of any admissible representation is admissible. It assumes a locally compact nonarchimedean group `H`, a semidirect decomposition `d` of a subgroup `Q` with closed normal factor `V` and continuous projection `d.projection`, and compact `Q\H` |
| (BC) | none | Not stated for a general `B`-algebra `C` |
| (P2) | `Langlands.Plancherel.scalarExtensionOfSemilinear` (Statement module) | Not stated. The general scalar-extension map exists, but no theorem on general base change |
| (VI.8.2.2) | `inducedScalarExtension`, `inducedScalarExtension_tmul` | Defined for `C = ℂ` through `evaluation r χ`; the pure-tensor formula is proved |
| (C2) | `RationalNormalizedInducedSpecializationStatement`; proof `rationalNormalizedInducedSpecialization` | Proved for the universal normalized induced family: for every smooth `π` and every unramified character `χ`, `inducedScalarExtension r h hU π χ` is bijective. No admissibility is assumed. This combines (C2) with (Ex-c) |
| (J) | `Jacquet`, `jacquetRepresentation` (Models); `Langlands.Plancherel.UnramifiedNormalized.normalizedJacquetFunctor` (UnramifiedNormalizedModels); `jacquetEvaluation` (Specialization) | The functor is defined: `normalizedJacquetFunctor` is the normalized Jacquet functor on smooth representations over any `unramifiedRegularFunctions ν`. The specialization map is defined for the universal family only. No flatness of Jacquet modules of families and no functor over a general `B` is stated |
| (P3) | none | Not stated. For the universal supercuspidal family, finiteness of the Jacquet module is the separate target `Langlands.Plancherel.RationalSupercuspidalJacquetFamilyFiniteStatement` in [UnramifiedRationalJacquetFinitenessStatement](../../Langlands/Representation/Plancherel/UnramifiedRationalJacquetFinitenessStatement.md), which is unproved; see the [uniform compression note](uniform-compression-progress.md) |
| (T4) | `LocalFreeCoverStatement` (RenardFamilyStatements). Mathlib: `Module.freeLocus_eq_univ_iff`, `Module.basicOpen_subset_freeLocus_iff`, `Module.isOpen_freeLocus`, `Module.FinitePresentation.exists_free_localizedModule_powers` | Stated, unproved; proof task `f10ce878-b279-4004-8426-7e12cf971e20`. For a finitely presented `R`-module `M`, Mathlib gives four facts. First, `M` is projective if and only if its free locus is all of the prime spectrum. Second, a basic open `D(f)` lies in the free locus if and only if `M_f` is a projective `R_f`-module. `M_f` need not be free: over `ℂ × ℂ` the module `ℂ × 0` is projective, so `D(1)` lies in its free locus, but it is not free. Third, the free locus is open. Fourth, if the localization of `M` at a submonoid `S` is free over a nontrivial `R_S`, then for some `r ∈ S` the module `M_r` is free over `R_r` of the same rank. Applied to the complement of a prime, this gives each point of the free locus a basic open neighbourhood with free localization. No published proof assembles these facts into the source's finite cover `f_1, …, f_r` with free localizations |
| (Sp-φ) | none | Not stated |
| (P4) | none in this form. Related: `Langlands.Plancherel.FiniteMatrixIrreducibilityOpennessStatement` in [FiniteMatrixOpennessStatement](../../Langlands/Representation/Plancherel/FiniteMatrixOpennessStatement.md), proved by `Langlands.Plancherel.finiteMatrixIrreducibilityOpenness` in [FiniteMatrixOpennessProof](../../Langlands/Representation/Plancherel/FiniteMatrixOpennessProof.md); `Langlands.Plancherel.CompactFixedFamilyOpennessStatement` in [CompactFixedFamilyOpennessStatement](../../Langlands/Representation/Plancherel/CompactFixedFamilyOpennessStatement.md) | Not stated. Related, not the Proposition: the statement `FiniteMatrixIrreducibilityOpennessStatement` concerns, for `x` in a topological space, a family of complex square matrices `A x j` on a finite coordinate space, indexed by `j` in any type, with every entry continuous in `x`. It asserts that the set of `x` at which the matrices `A x j` have no common invariant subspace other than zero and the whole space is open. It concerns finite matrices and openness in a given topology, not Zariski openness in `X(M)` or irreducibility of `π_ψ`. It is proved through the openness of generation of the full matrix algebra, `Langlands.Plancherel.FiniteMatrixOpenness.isOpen_adjoin_eq_top`, and Burnside's theorem `Langlands.SandwichDimensionBound.action_surjective`; the source argues through Burnside's theorem and a determinant. The unproved `CompactFixedFamilyOpennessStatement` transfers this to smooth representations. For a family `A x` of nontrivial smooth complex representations, indexed by a topological space, it takes one compact open `K` such that every irreducible subquotient of every `A x` has a nonzero `K`-fixed vector, bases of the `K`-fixed spaces indexed by one finite type, and continuous entries of the matrices `UnitarizabilityContinuation.fixedMatrix`. It asserts that the set of `x` with `A x` irreducible is open. It again concerns openness in a given topology, and it supplies neither the subgroup `K`, nor the bases, nor an irreducible `π_{ψ_0}` |
| (T5) | none in this form. Related: `Langlands.Plancherel.ConditionalParabolicGenericIrreducibilityStatement` in [ParabolicGenericIrreducibilityStatement](../../Langlands/Representation/Plancherel/ParabolicGenericIrreducibilityStatement.md) | Not stated. Related, not the Theorem: the unproved statement `ConditionalParabolicGenericIrreducibilityStatement` is adapted from Waldspurger 2003, Proposition IV.2.2(i) and the beginning of IV.3, not from Renard. For an irreducible smooth representation `π` of the Levi points that is square-integrable modulo the image `C` of the split component, it asserts a nonempty set `D` of unramified characters, open in the continuous-character topology, on which the induction `UnramifiedLeviInduction` of `π` twisted by `χ` is irreducible. Its hypothesis is square integrability, not supercuspidality, and its locus is open in that topology, not Zariski open. It does not by itself give a Zariski-open locus, and no Library declaration connects it to (T5). Its proof task `468db4c1-297b-4d4e-8534-ed8de150ffc5` is open |
| (T5-a) | `Langlands.Aubert.General.RepresentedParabolic.exists_positive_unramifiedCharacter_norm_mul_eq_one`, `twistUnitaryCentralCharacter`, `exists_positive_unramifiedTwist_unitaryCentralCharacter` in [PositiveUnramifiedCentralTwist](../../Langlands/Representation/Exponents/PositiveUnramifiedCentralTwist.md) | Proved for a connected reductive group: an irreducible smooth representation has a positive unramified twist with unitary central character. The module was published with the VII.1.3 proof unit `228c630c`, which uses it. See reading note 5. The second claim, that a supercuspidal representation with unitary central character is unitary, is stated, unproved, as `Langlands.Aubert.General.RepresentedParabolic.SupercuspidalUnitaryCentralCharacterUnitarizableStatement` in [MaximalLeviReducibilityUnitaryInputs](../../Langlands/Representation/Exponents/MaximalLeviReducibilityUnitaryInputs.md). It covers every connected reductive group, with supercuspidality as vanishing of the normalized Jacquet modules of all proper parabolics; its proof task is `df1b860d-7b40-4e1b-9e06-fd01618045ff`. The source's route through VI.2.1 and IV.3.2 is split as follows. `SupercuspidalUnitaryCoefficientCompactSupportStatement`, in [SupercuspidalCoefficientCompactSupportStatement](../../Langlands/Representation/Exponents/SupercuspidalCoefficientCompactSupportStatement.md), states VI.2.1 (a) ⇒ (b) for these representations, when irreducible: for every unitary central character datum, every descended coefficient norm has compact support on the quotient by the full abstract centre. It is unproved. In [SupercuspidalCoefficientCompactSupportReduction](../../Langlands/Representation/Exponents/SupercuspidalCoefficientCompactSupportReduction.md), `supercuspidalUnitaryCoefficientCompactSupportStructuralReduction` derives it from the three unproved statements `StandardCocharacterStatement`, `RelativeRootSystemStatement` and `JointSpecialCompactBasisExistenceStatement`; the earlier `supercuspidalUnitaryCoefficientCompactSupportReduction` also assumes `ParabolicDynamicStatement`. For IV.3.2, `Langlands.UnitaryCentralCharacter.isUnitarizable_of_compact_coefficientNorm_of_nonarchimedean`, in [CompactCoefficientProof](../../Langlands/Representation/Unitary/CompactCoefficientProof.md), proves that a smooth irreducible representation of a nonarchimedean group with a unitary central character datum and compactly supported coefficient norms is unitarizable. No Library declaration composes these into a proof of `SupercuspidalUnitaryCentralCharacterUnitarizableStatement`. Two variants are proved: `Langlands.Aubert.General.RationalPointFamily.isUnitarizable_of_compact_normKernel_restriction`, in [RationalCompactRestrictionUnitarity](../../Langlands/Representation/Aubert/General/RationalCompactRestrictionUnitarity.md), assumes compact coefficients after restriction to the norm kernel, and `Langlands.HarishChandraSchwartz.isUnitarizable_of_irreducible_isSquareIntegrable_leftHaar`, in [LeftHaarSquareIntegrableUnitarity](../../Langlands/HarmonicAnalysis/HarishChandraSchwartz/LeftHaarSquareIntegrableUnitarity.md), assumes square integrability modulo a central subgroup. The forward VI.2.1 proof for standard families is in Worker 6's [VI.2.1 map](cuspidal-decomposition-source-map.md) |
| (T5-b) | `Langlands.Aubert.General.RepresentedParabolic.LeviInductionUnitarizableStatement` (MaximalLeviReducibilityUnitaryInputs); `leviInductionUnitarizable_of_inputs` in [MaximalLeviReducibilityInductionInputs](../../Langlands/Representation/Exponents/MaximalLeviReducibilityInductionInputs.md); `Langlands.Aubert.General.normalizedInductionFunctor_obj_isUnitarizable_of_compactSpace` in [NormalizedInductionUnitarity](../../Langlands/Representation/Aubert/General/NormalizedInductionUnitarity.md); `Langlands.admissibleUnitarySemisimplicity` in [AdmissibleSemisimplicityProof](../../Langlands/Representation/Unitary/AdmissibleSemisimplicityProof.md); `Langlands.Plancherel.rationalUnramifiedRegular_exists_unitary_finset_ne_zero` in [RationalUnitaryNonvanishing](../../Langlands/Representation/Plancherel/RationalUnitaryNonvanishing.md) | Partly stated. The first claim, that normalized induction from an actual rational parabolic preserves unitarizability, is the unproved `LeviInductionUnitarizableStatement` (Renard IV.2.3). `leviInductionUnitarizable_of_inputs` derives it from four unproved structural statements: `RationalReductiveUnimodularityStatement`, `StandardCocharacterStatement`, `ArbitraryParabolicQuotientCompactStatement` and `ParabolicRootPresentationExistenceStatement`. `normalizedInductionFunctor_obj_isUnitarizable_of_compactSpace` proves it for a closed subgroup `P` with compact `P\G`, keeping the triviality of the modular character of `G` and the identity for the modular character of `P` as premises. For "hence completely reducible", `admissibleUnitarySemisimplicity` proves `AdmissibleUnitarySemisimplicityStatement`: when compact open subgroups are cofinal, an admissible unitarizable representation is semisimple. The filtration from VI.5.3(iii) and the pairwise distinctness of the central characters outside a Zariski closed subset are not stated as steps of VI.8.5. Related: `rationalUnramifiedRegular_exists_unitary_finset_ne_zero` gives, for a connected reductive group, one unitary unramified character at which finitely many nonzero regular functions are all nonzero; it proves nothing about central characters |
| (L5) | `Langlands.CentralEigenspaceSplitting.eigenSubrep`, `eigenEquivGraded`, `iSup_eigenSubrep` in [CentralEigenspaceSplitting](../../Langlands/Representation/Filtration/CentralEigenspaceSplitting.md) | Related, not the Lemma. Over a field, for a filtration of a representation and one central element `z` acting on graded piece `i` by `c i` with `c` injective, the `c i`-eigen subrepresentation is isomorphic to graded piece `i`, and these subrepresentations span. The hypothesis is stronger than the source's; see reading note 4 |
| (T5-c) | `Langlands.Aubert.General.isIrreducible_induction_of_semisimple_jacquetHom_rank_le_one`, `isIrreducible_induction_of_unitary_jacquetHom_rank_le_one` in [JacquetMultiplicityIrreducibility](../../Langlands/Representation/Aubert/General/JacquetMultiplicityIrreducibility.md) | Related, not the step. A nontrivial semisimple normalized induction `I σ` is irreducible if `Hom(r(I σ), σ)` has rank at most one; Frobenius reciprocity is applied inside the proof. The unitary version replaces semisimplicity by admissibility, unitarizability and cofinal compact opens, through `admissibleUnitarySemisimplicity`. The rank bound, which the source obtains from (T5-b) and (L5), is a hypothesis |
| (P6) | none | Not stated. See reading note 6 |
| (Ex6) | none | Not stated |

## Source reading notes

These are Worker 709's readings of the printed text. None of them is checked
in Lean.

1. (P1) and (R1). In the converse half of the proof of (P1), on PDF p.194,
   the argument that the Remark records as (R1), the source tensors a "suite exacte courte de
   `(G, B)`-modules" and argues "comme les représentations `E_i` de `G` sont
   lisses". Flatness of `V` is tested against arbitrary `B`-modules `E_i`,
   which carry no action of `G`. The smoothness needed is that of `V`,
   through `E ⊗_B V = ⋃_K E ⊗_B V^K`. The published
   `flat_of_smooth_fixed_flat` uses the equational criterion instead, and
   this reading does not affect it.
2. VI.8.2. The Proposition writes "`(B, M)`-module" for `(M, B)`-module.
   "`C` soit un `B`-module" must mean that `C` is a commutative `B`-algebra,
   since `V ⊗_B C` is to be a `C`-module. `C` is assumed commutative,
   Noetherian and reduced but not of finite type, so `M(G, C)` can fall
   outside the class of algebras fixed in VI.8.1.
3. VI.8.3. "`B`-modules de type fini" is not defined for `(G, B)`-modules.
   VI.1.3 says that `r_P^G` preserves representations of finite type, so the
   natural reading is finite generation under the joint action of `G` and
   `B`. The VI.9.2 step (S3) of the uniform compression note rests on VI.5.3,
   not on this Proposition.
4. (L5). The source assumes that the central characters of `Z(G)` on the
   subquotients are pairwise distinct. `CentralEigenspaceSplitting` assumes
   one central element taking pairwise distinct scalars, which is strictly
   stronger. If `Z(G)` contains `(ℤ/2)^2`, its four characters with values
   `±1` are pairwise distinct, but one element takes at most two values on
   them.
5. (T5-a). The PositiveUnramifiedCentralTwist Markdown records that its
   proof avoids the finite-index step that the source takes from V.2.6. It
   extends positive characters by the divisibility of the
   positive reals, through `Langlands.PositiveCharacter.exists_extension` and
   `Langlands.Plancherel.exists_positiveCharacter_restrict_eq`.
6. (P6). The proof ends by gluing elements `b_i ∈ B_{f_i}`, obtained for each
   `K` on a cover by basic open sets, into one `b ∈ B`. The source does not
   spell this out. It holds: `S` has finitely many connected components; for
   `K` small enough the rank of `V^K` is positive everywhere, since `Ξ` is
   dense, `sp_x(V) ≠ 0`, (P1-iso) gives `sp_x(V^K) = sp_x(V)^K`, and `V^K`
   is a direct summand of `V^{K'}` for
   `K' ⊆ K`. The `b_i` are then unique, because `V^K_{f_i}` is free and
   faithful, so they agree on overlaps and glue by the sheaf property of `B`.
   By faithfulness, `b` does not depend on `K`, and it acts as `φ` on
   `V = ⋃_K V^K`.

## Unpublished assertions

At Library `d82893a7` these assertions have no published statement:

1. (D), and the category `M(G, B)`.
2. (Sp) as a named construction for general families.
3. (Ex-c) as a public fiber isomorphism for `V_B` itself.
4. (I) over a general `B`, and flatness of induced families other than the
   universal one; (L2) for normalized induction over a general `B`; (BC);
   and (P2) for a general `B`-algebra `C`.
5. (J) over a general `B`, flatness of Jacquet modules of families, and
   (P3).
6. (Sp-φ), (T5-c), (P6) and (Ex6); (T5-b) apart from its first claim; (P4),
   (T5) and (L5) in the source's form.

These are stated but unproved:

- (P1), (P1-iso), (R1) as an equivalence, (L1) and (T4), by the five
  statements of `51d6b0a6`. Proof task `f10ce878-b279-4004-8426-7e12cf971e20`
  is for (T4), and proof task `eb5ee8fa-29f5-4671-9ecd-e6259db108d3` is for
  the other four and their conjunction `Statements`. The RenardFamilyStatements
  Markdown refers to this note's earlier numbering, in which these were
  unpublished items 2, 3, 4 and 8.
- The second claim of (T5-a) and the first claim of (T5-b), by
  `SupercuspidalUnitaryCentralCharacterUnitarizableStatement` and
  `LeviInductionUnitarizableStatement` of `57393553`; and the VI.2.1 input
  `SupercuspidalUnitaryCoefficientCompactSupportStatement` of `156a0ca5`,
  which `62a8273c` and `d8629ccb` reduce to unproved structural statements.

They remain with the whole-book parent task. The three VI.8 statements,
`UniversalInducedCoefficientFinitenessStatement`,
`RationalUniversalTensorFinitenessStatement` and
`RationalNormalizedInducedSpecializationStatement`, came from statement task
`e2884067-b19a-4685-91d9-e62316299fc3`, and all three are proved. Of the
related statements, `4cadcefc` (row (T5)) and `f12ff2f5` (row (P4)) are
unproved, and `b933342c` (row (P4)) is proved by `c3682633`.

## Receipts

All thirty-one units are accepted and published. Each independent reviewer
approves without qualifications. Submitter and coauthors come from the
review-task bindings. Eleven units record author qualifications, summarized
after the tables.

| Unit | Accepted artifact | Submitted by; coauthors | Reviewer | Publication commit |
| --- | --- | --- | --- | --- |
| VI.8.2 statement (`UniversalInducedCoefficientFinitenessStatement`) | `4bbbe11b-5b49-40a3-9815-e2498e18a7e8` | Worker 1761 | Reviewer 15994 | `1eb9a9ee0815224a368f8dc58b7d95f024cfff05` |
| VI.8.1 statement (`RationalUniversalTensorFinitenessStatement`) | `4c9fbac3-c131-450d-97dd-fc3653bfa0fa` | Worker 1759 | Reviewer 16080 | `80f702330eab13242c1eb52eee2757a5d07eb1ba` |
| VI.8.2 statement (`RationalNormalizedInducedSpecializationStatement`) | `f1e0aa3d-8a98-4791-805b-e989ee12f85a` | Worker 1759 | Reviewer 16009 | `1eb9a9ee0815224a368f8dc58b7d95f024cfff05` |
| Proof `universalInducedCoefficientFiniteness` | `c957a9bb-50b1-4f6d-b535-43592cbaa9c7` | Worker 1754; Worker 1582 | Reviewer 16333 | `334440350ec029c1bf78b7801689e1a2b21079c6` |
| Proof `rationalNormalizedInducedSpecialization` | `d9e1f423-ca9d-4ef4-b77b-fad2889616c2` | Worker 1635; Worker 1679 | Reviewer 16332 | `334440350ec029c1bf78b7801689e1a2b21079c6` |
| Proof `rationalUniversalTensorFiniteness` | `40b11f3f-f58c-4dd5-bd3f-d444ab6aba1f` | Worker 1780 | Reviewer 16453 | `6f182f920309bbe9e9e43bd7181d7e25d5c02acd` |
| VII.1.3 proof, publishing PositiveUnramifiedCentralTwist (`maximalLeviSupercuspidalReducibilityFromInputs`) | `228c630c-ada7-4275-8e2a-7010cdab6908` | Worker 1697; Workers 1517 and 1507 | Reviewer 15787 | `8b3ba080b2e8bcecb1612373f236b9ad96423d12` |
| VI.4.1 comparison proof (`Langlands.CuspidalSupport.rationalUniversalProgeneratorComparison`) | `700fc1f0-b6e7-41c8-98da-cb2203be406f` | Worker 1595 | Reviewer 16288 | `334440350ec029c1bf78b7801689e1a2b21079c6` |
| Compact quotient proof (`Langlands.Induction.compactQuotientClause_holds`) | `53fcb4f0-f5d1-4169-9eb6-8fc3c17279cd` | Worker 53 | Reviewer 668 | `e3c2fa98be720f63c6981efbbdf15cd223329e76` |
| Coefficient algebra (`regularAlgebraLaurentEquiv`) | `28559051-813c-4e20-b2e0-a1b0189287d3` | Worker 1755 | Reviewer 16236 | `80f702330eab13242c1eb52eee2757a5d07eb1ba` |
| Fixed-vector model (`Langlands.Induction.fixedEvaluationEquiv`) | `178015a2-7fc6-4448-913a-2700ec46f788` | Worker 289; Workers 256 and 34 | Reviewer 10492 | `24243ad1d7d77cd0f3cd88510b523cb2a13a1142` |
| Eigenspace splitting (`Langlands.CentralEigenspaceSplitting.eigenSubrep`) | `d6af361f-185b-4713-a2f7-7089237898f5` | Worker 964 | Reviewer 4571 | `bc8de2287e5c24972c55277b2aa9611523dfc5dc` |
| Universal models (`jacquetRepresentation`) | `af7e8221-e364-4ee8-bedc-d361a4b87bc1` | Worker 16; Worker 1585 | Reviewer 13819 | `0d12b7d171600d15516e52ee508d3aaca3e9cf9e` |
| Specialization maps (`jacquetEvaluation`) | `1bcc93b6-ecf5-47f6-ba34-caad76dcdaf6` | Worker 1585; Worker 16 | Reviewer 14396 | `1831431f93603e52c73600a2a900dd42d7f18deb` |
| Admissibility of universal and conjugate induced models (`Langlands.Plancherel.RationalNormalized.conjugateOutputInducedRepresentation`) | `23d4a854-addb-43d9-8f9d-8186e433e286` | Worker 1780 | Reviewer 16865 | `291705a7b40579e0118c8512a32d7f8212883f2e` |
| Generic irreducibility statement (`Langlands.Plancherel.ConditionalParabolicGenericIrreducibilityStatement`) | `4cadcefc-2d4a-4898-965a-fe3c2df7931f` | Worker 200 | Reviewer 16874 | `291705a7b40579e0118c8512a32d7f8212883f2e` |
| Finite matrix openness statement (`Langlands.Plancherel.FiniteMatrixIrreducibilityOpennessStatement`) | `b933342c-bc65-4dc5-b1b4-00b7a5e04f86` | Worker 1598 | Reviewer 17062 | `f73044d93e675a78ed75830ef026b3224514e510` |
| VI.8.1 and VI.8.4 general-family statements (`Langlands.Renard.AlgebraicFamily.Statements`) | `51d6b0a6-a093-42f1-9694-67af73184db2` | Worker 709 | Reviewer 17299 | `0d9cba336dd98294a5d7f48d772eb708aae40708` |
| Proof `Langlands.Plancherel.finiteMatrixIrreducibilityOpenness` | `c3682633-647e-498a-a4fc-7a6630f81c8b` | Worker 1598 | Reviewer 17205 | `ce52163e150fe772fdb773627f006a99df1688af` |
| Compact-fixed family openness statement (`Langlands.Plancherel.CompactFixedFamilyOpennessStatement`) | `f12ff2f5-4ad1-4372-a657-fbaa14717c6c` | Worker 1598 | Reviewer 17236 | `0d9cba336dd98294a5d7f48d772eb708aae40708` |
| Unitary nonvanishing (`Langlands.Plancherel.rationalUnitaryRegularRestriction`) | `9c0f4b4c-4787-4c1f-ada6-996b9906c4c1` | Worker 1597 | Reviewer 17281 | `0d9cba336dd98294a5d7f48d772eb708aae40708` |
| Jacquet multiplicity irreducibility (`Langlands.Aubert.General.jacquetScalarEquiv`) | `5c9af9f3-008e-4de3-ab9d-ff3eb415806c` | Worker 1597 | Reviewer 17210 | `ce52163e150fe772fdb773627f006a99df1688af` |
| Square-integrable unitarity (`Langlands.HarishChandraSchwartz.LeftHaarDualForm.positiveForm`) | `cb817814-c21f-40c5-b636-c9987196563a` | Worker 1597 | Reviewer 17063 | `f73044d93e675a78ed75830ef026b3224514e510` |
| Compact coefficient unitarity (`Langlands.UnitaryCentralCharacter.compactCoefficientPositiveForm`) | `295ff724-7f1a-4f83-a28a-0b01a72e1fce` | Worker 1668; Worker 1678 | Reviewer 15607 | `86cf8f8984679ba48ded6fa152c55ec38b532d97` |
| Norm-kernel restriction unitarity (`Langlands.Aubert.General.RationalPointFamily.rationalNormKernelPositiveForm`) | `22169551-7386-427a-ab12-a078cdbe8477` | Worker 480 | Reviewer 12235 | `c5e0296f115eacde9bd491a7ea70fec6983c1c1c` |
| Normalized induction unitarity (`Langlands.Aubert.General.compactQuotientNormalizedInductionForm`) | `056a29f6-5a6b-45f5-bfb8-7a6218736852` | Worker 480 | Reviewer 11027 | `25b91125ea94e88d741b206d633e82eb0d87c3e5` |
| Proof `Langlands.admissibleUnitarySemisimplicity` | `5bbc57bb-ee55-426c-9596-e9f96a23f603` | Worker 200 | Reviewer 2205 | `484c26ed207bd2fb5ed2073a5c6b37860c04f67b` |
| VII.1.3 unitary input statements (`Langlands.Aubert.General.RepresentedParabolic.MaximalLeviSupercuspidalUnitarizableConstituentStatement`) | `57393553-840c-44f2-918b-f32159b1d178` | Worker 1507 | Reviewer 15320 | `08e8de28d111b66b088500c8ad1b0bd0f947991d` |
| Coefficient compactness statement (`Langlands.Aubert.General.RepresentedParabolic.SupercuspidalUnitaryCoefficientCompactSupportStatement`) | `156a0ca5-bb3b-4c80-a76b-07ae1c630ca3` | Worker 1721; Worker 1678 | Reviewer 15635 | `86cf8f8984679ba48ded6fa152c55ec38b532d97` |
| Four-premise reduction (`Langlands.Aubert.General.RepresentedParabolic.SupercuspidalUnitaryCoefficientCompactSupportReductionStatement`) | `62a8273c-97a1-4eeb-b5eb-c824c8781a6b` | Worker 1742; Worker 1276 | Reviewer 15991 | `1eb9a9ee0815224a368f8dc58b7d95f024cfff05` |
| Three-premise reduction (`Langlands.Aubert.General.RepresentedParabolic.SupercuspidalUnitaryCoefficientCompactSupportStructuralReductionStatement`) | `d8629ccb-aff1-4326-a5d1-00a9f3e2dd49` | Worker 1742; Workers 1270 and 1276 | Reviewer 17333 | `d82893a7de0b168873a15c6c7b0a731deb27aa23` |

The VI.4.1 comparison `700fc1f0` is not a VI.8 result. It is listed because
the prerequisite section of the uniform compression note now cites it. The
statements `4cadcefc`, `b933342c` and `f12ff2f5` and the units `c3682633`,
`9c0f4b4c`, `5c9af9f3` and `cb817814` are related to (T5), (P4) and the steps
of (T5) only, as the rows explain. All of them except `4cadcefc` came from
its proof task `468db4c1-297b-4d4e-8534-ed8de150ffc5`. The unit `57393553`
states the inputs for the unitary case of VII.1.3; this note uses two of
them. `62a8273c` and `d8629ccb` are conditional reductions, and
their reviewers record that they do not complete their host task.

| Unit | Host task | Review task | Machine receipt (policy) | Integration |
| --- | --- | --- | --- | --- |
| `4bbbe11b` | `e2884067-b19a-4685-91d9-e62316299fc3` | `d24693bc-49b6-49ca-aced-83bd376ad73f` | `edb732cc-80d4-493b-bf6c-29d6171485d4` (`lean.statement@1`) | `24c13782c73d480e94c588dca7ca9090` |
| `4c9fbac3` | `e2884067-b19a-4685-91d9-e62316299fc3` | `11b4c928-0e4e-4703-8514-65621178963e` | `c032be6f-0fc2-4d6e-8caf-12fc6a7415cc` (`lean.statement@1`) | `1f7f0ee347284bdda4efc7e8e5801147` |
| `f1e0aa3d` | `e2884067-b19a-4685-91d9-e62316299fc3` | `8154b395-8697-4421-95a9-29c2a52af70d` | `b2c1c16d-9c73-4ed0-b5c7-7170dae8fd4d` (`lean.statement@1`) | `7d009adf8ee04ba6984d647688514b0f` |
| `c957a9bb` | `edf79294-fb4f-4072-ad09-dfddf0a5c868` | `86e8aab6-2f7d-424a-af36-535890ac3212` | `85bc4b3e-e547-481e-b29a-c96855427d1c` (`lean.proof@1`) | `84831cde66ac4854962dc7ce362df984` |
| `d9e1f423` | `1f1a983d-e797-4c9c-984d-0657760c61c6` | `cae1dd15-b964-474c-ab6d-1f5d46dd6d86` | `e6b45827-c27c-4f37-96f3-afedd4d5a55b` (`lean.proof@1`) | `9d60bb1417314efc90a65b4c19eba95f` |
| `40b11f3f` | `c1f3c743-2a62-415c-8640-714b9f6a27c4` | `e55a8589-15f1-4ae3-9397-239293e57900` | `e08d2b34-286f-4f05-9c55-eec5d909d1f3` (`lean.proof@1`) | `a0ebe44d855b410b9981d93caf23f4bc` |
| `228c630c` | `350bd05e-03c8-452f-9d08-8fae4eec3930` | `645596c7-9328-45b9-b86c-c255b01f9337` | `d7f3388f-cc19-4ae2-a09d-61f69d7dde31` (`lean.proof@1`) | `2a786299210d45538530579036238504` |
| `700fc1f0` | `0bb65e53-06b7-4274-92ba-fee1666298eb` | `bc07c522-f814-486a-802c-1effeafa672e` | `109790cc-9e0f-4014-b2f4-bb68bae3302f` (`lean.proof@1`) | `b2d60f0e746b4ffd98b59b9427539313` |
| `53fcb4f0` | `672038be-3175-4fbd-85a6-d8c272aa63ec` | `9d5dd6bb-bda0-477a-b1d9-d2e1da593e87` | `355e1ee1-36e2-48ee-9450-d04b4918b928` (`lean.proof@1`) | `6a86f13632e742a7bacc411534d956d0` |
| `28559051` | `47e556e6-6b2a-40dc-ba66-d6a0585f5220` | `b6d6a6c7-22ed-436a-afdf-7614c4a6d911` | `22cac98e-46f5-4456-9899-cccf3815041a` (`lean.definition@1`) | `d98adac08cdb4d9b9994929b35621a58` |
| `178015a2` | `f85448c5-077a-467f-8121-66e53755fae0` | `ceca4336-c23e-467f-a9c8-100cd5613afd` | `15283549-b9e3-4dc4-8db6-c20fb3f8bfd3` (`lean.definition@1`) | `73d681744cee445d84c1ae3951620520` |
| `d6af361f` | `b331611c-526d-4925-87fe-ea67ed6e6fed` | `ebb2e216-42db-4e18-82aa-982728c30301` | `c8c50b97-570e-43a8-958a-cbbe2f4d9657` (`lean.definition@1`) | `7e2bd712c22f4b9dba9978103ec00ee6` |
| `af7e8221` | `64609e76-da68-4daa-b65b-66619e084a6a` | `e529e4b9-4042-4058-b538-3253d5589fd9` | `9223410e-ffee-4de2-a24b-2943bbbc2a76` (`lean.definition@1`) | `7b66b08395284b6e8118532afd8d764b` |
| `1bcc93b6` | `64609e76-da68-4daa-b65b-66619e084a6a` | `e18035e4-1347-4b82-9e5a-472cd3d22862` | `36e4beb6-154a-450b-9124-c29f3911fbe0` (`lean.definition@1`) | `34898ca83f9b446585dbf837b2155250` |
| `23d4a854` | `c1f3c743-2a62-415c-8640-714b9f6a27c4` | `ae231319-f2ef-4aba-8081-e8c5199dff57` | `73f4e869-e926-4923-889e-de4536f959b6` (`lean.definition@1`) | `1e65a5de495f4b498b3147535bc5ea3e` |
| `4cadcefc` | `1ef6854b-f0e9-4d96-bbe5-cb8c4b52f927` | `5e2b2afd-d3e5-42f5-9f98-02f61cf31385` | `09d60d07-e2bb-4098-aaf6-4bf30893754a` (`lean.statement@1`) | `2dfbae4f45c54bc6a37dda0a9578b751` |
| `b933342c` | `468db4c1-297b-4d4e-8534-ed8de150ffc5` | `0c7e32be-7597-4276-b3f2-32430a23d163` | `95c0af17-7e85-4433-b006-6ff07757f14e` (`lean.statement@1`) | `ae477383b996482ebc56d6769d2c5b90` |
| `51d6b0a6` | `f5d1f399-a1f8-4ab5-a981-90b92abd4857` | `d777ded1-1638-4911-801f-fde7b7aa0142` | `0a9d45b7-7073-4be6-af80-8c8f5da2da8a` (`lean.statement@1`) | `ebc1a5983acf4431a3cb041096d0c5f8` |
| `c3682633` | `468db4c1-297b-4d4e-8534-ed8de150ffc5` | `3275eada-0a78-4995-ae00-9848d278b148` | `f01c5f52-c294-4ee9-8444-e7fccaa59117` (`lean.proof@1`) | `d9cd3ead410949a2a876f882ee9ace47` |
| `f12ff2f5` | `468db4c1-297b-4d4e-8534-ed8de150ffc5` | `221bf602-ccce-4af1-81be-66682a058fd8` | `0c7ac129-656d-47d7-b53c-fb506af548ad` (`lean.statement@1`) | `39516e600908426faffeef9ac0aafdd9` |
| `9c0f4b4c` | `468db4c1-297b-4d4e-8534-ed8de150ffc5` | `db7ff49c-436f-4afb-a587-cb48c0bcf681` | `17e1d49f-d8c4-4fb2-8ce1-ff912a0edefe` (`lean.definition@1`) | `d17ab5b65b3a42e0bda126e81c9f0214` |
| `5c9af9f3` | `468db4c1-297b-4d4e-8534-ed8de150ffc5` | `727deef3-570a-44c0-9905-7056de58db50` | `11f4a61d-7b39-4d08-ae30-5e86b13b95f4` (`lean.definition@1`) | `4ce8e68facd44f8fbe20014a455fea8f` |
| `cb817814` | `468db4c1-297b-4d4e-8534-ed8de150ffc5` | `bf5a387d-4836-4918-bb60-0dc53766e50b` | `a8860145-6c58-4ef6-85ef-0943f243ce94` (`lean.definition@1`) | `88cb50b158a74149baa621be01a1b97a` |
| `295ff724` | `df1b860d-7b40-4e1b-9e06-fd01618045ff` | `4bdc67f6-d8ed-42cf-a85a-e71ceb66ab08` | `3447ac05-d392-45d6-8800-8ce376669c44` (`lean.definition@1`) | `4a703d4eed6f40c581f6157426489335` |
| `22169551` | `46f751c8-0d69-40a6-ab67-4c19be8fc4c9` | `5dc3c983-3df0-43d2-85c0-021486ad9d4b` | `d550a8c9-f221-4044-9964-e2cdb27e96a0` (`lean.definition@1`) | `7fd7649a93e94710b5010fa6dcef8701` |
| `056a29f6` | `46f751c8-0d69-40a6-ab67-4c19be8fc4c9` | `6ed7375f-6b70-46ff-8ff5-78350cd3f888` | `397a3838-efa9-422e-98bd-8c034a6e31c7` (`lean.definition@1`) | `0b142cb2bd6d49cb96addc2fa393e1cb` |
| `5bbc57bb` | `fb462a13-96b1-4ac1-a47d-4fd7510d0ac4` | `a8a672e8-fc9d-4581-925a-108ee32db444` | `af7da996-d8a9-4886-83e0-c414b6899d34` (`lean.proof@1`) | `c4a026fdd5164afdba3385cdd1861957` |
| `57393553` | `004e00e1-5995-4dc1-884e-a5f512150d0c` | `9554bafa-7005-4221-af30-fae391086ae9` | `6a2d7edd-f352-4ab6-9be7-0107ea50ea58` (`lean.statement@1`) | `8c267717d0464dfa843d1d592cb365a5` |
| `156a0ca5` | `44ffed6c-284d-4970-b2c0-1254c77835ff` | `a1122cf0-f5a1-42ce-84b8-ff0002d4696f` | `43b80b8a-0c0d-4fca-9eff-2982fcecb493` (`lean.statement@1`) | `ce74d06ef4974651bb41bb50ec9f4618` |
| `62a8273c` | `1aa60759-6f72-4345-a25c-269bfa6477d0` | `52b74316-66d1-490e-9407-ef4a57312f75` | `5f9f8c6c-73d9-45f6-b426-f4923155e342` (`lean.statement@1`) | `82786e62af2c468c8f6100e6e74f55a9` |
| `d8629ccb` | `1aa60759-6f72-4345-a25c-269bfa6477d0` | `a4f3c512-03af-4fb1-a72e-d8da16fea985` | `3f54dda2-43c1-4da6-b380-9bf3275576d1` (`lean.statement@1`) | `2fc4f4fb63d44fd5a59bc481987a00a1` |

The eight `lean.proof@1` receipts record the checks `lake-build`,
`exact-target`, `unchanged-statement` and `frozen-inputs`. The statement and definition
receipts record `lake-build` and `declaration-kind` among their checks. No
machine receipt records a qualification.

Author qualifications:

- `4c9fbac3`: local compactness and nonarchimedeanness of the rational
  points and affineness of the Levi stay explicit structural hypotheses; no
  proof is claimed.
- `f1e0aa3d`: this is the specialization case of the source's base-change
  result; the map and its pure-tensor formula are proved, and bijectivity is
  the target. The structural hypotheses stay explicit.
- `40b11f3f`: the unit proves the universal tensor prerequisite only; the
  full normalized output-Jacquet finiteness of its host task stays open.
- `178015a2`: the construction proves neither same-Levi induction
  independence nor the Weyl-conjugacy target of its host task.
- `53fcb4f0`: helper lemmas are reproved under new public names;
  intermediate lemmas are stated over a commutative ring, Noetherian for
  admissibility; the proof route is internal, since BZ77 1.9(e) refers to an
  earlier paper that was not consulted.
- `23d4a854`: the conjugate Levi, its containment and conjugation formula,
  the continuous semidirect projection and the compact inducing quotient are
  geometric inputs; identifying the orbit Jacquet quotients with these
  induced models, the rational orbit geometry, the Haar-normalization
  comparison, the elimination of proper pieces and the global finiteness
  theorem remain separate obligations.
- `4cadcefc`: this is a `Prop`-valued statement with an elementary
  centrality helper, not a proof; its conclusion gives only a nonempty open
  locus in the character space, and the full Waldspurger IV.2.2, the
  regularity and invertibility of standard intertwiners and orbit descent
  remain open.
- `51d6b0a6`: the admissibility conclusion of `SpecializationAdmissibilityStatement`
  uses `Langlands.IsAdmissible`, a condition on every open subgroup, which in
  a t.d. group is equivalent to the source's compact-open condition; this
  equivalence is not checked in Lean. The fiber is `ℂ ⊗[B] V`, with the
  factors in the opposite order to the source's.
- `22169551`: compact smooth-dual coefficients on the norm-kernel
  restriction, the unitary central character, irreducibility, the finite
  index of the central valuation image and the topological hypotheses are
  retained, not derived from cuspidality.
- `056a29f6`: compactness of the rational parabolic quotient, rational-point
  unimodularity and the modular-character identity remain geometric
  obligations.
- `57393553`: none of the input statements is proved here; some are stated
  in the form in which the proof of VII.1.3 applies them; several omit
  properness and maximality of the parabolic, and the supercuspidal
  unitarity input is stated for every connected reductive group.

Worker 709 checked the Lean and Markdown files of the modules below at
Library `d82893a7` and in the workspace. Some frozen bundles differ from the
Library:

- `f1e0aa3d` also froze an earlier RationalUniversalTensorFinitenessStatement
  Markdown file; its own pair equals the Library.
- `d6af361f` also froze unrelated filtration Markdown files that changed
  later; its own pair equals the Library.
- `53fcb4f0` froze a wide snapshot. In it, CompactQuotientProof.md differs
  from the Library at line 70 by one sentence, "is not an input of any
  theorem" against "is not an additional input of the closing theorem". No
  publication record names this change. `Induction/Definitions.lean` also
  changed later.
- The Library UnramifiedRationalNormalizedModels pair differs from the copy
  frozen by `af7e8221`, through a later build-speed refactor that introduced
  reducible `Prop` abbreviations such as `UniversalSmoothness` and rewrote
  theorem types. The definitions cited here are unchanged. The originating
  unit of the newer copy was not identified.
- The Library RationalUniversalProgeneratorComparisonProof pair differs from
  the copy frozen by `700fc1f0`. The later definition unit
  `1c65621b-e696-432e-ba07-7b5e56d9a0e5`, "Actual norm-kernel generator fixed
  vectors and dynamic compression stability", published at
  `291705a7b40579e0118c8512a32d7f8212883f2e`, named its two local instances
  `rationalUniversalProgeneratorComparisonProofPointTopology` and
  `rationalUniversalProgeneratorComparisonProofTopologicalGroup`, and added
  one Markdown paragraph saying that the naming changes no topology,
  representation, predicate or proof.
- `23d4a854` and `4cadcefc` froze wide snapshots; their own pairs equal the
  Library.
- `f12ff2f5` also froze the FiniteMatrixOpennessProof pair, `9c0f4b4c` the
  JacquetMultiplicityIrreducibility pair, and `22169551` the
  RationalUnitaryInductionIrreducibility pair; all equal the Library.
  `5bbc57bb` also froze four submission JSON files.
- `056a29f6` also froze the SemisimpleInductionIrreducibility pair, equal to
  the Library, and the Exponents/SmoothContragredientCentralSpectrum pair,
  which changed later; its own pair equals the Library.
- `57393553` also froze the MaximalLeviReducibilityReductionStatements pair,
  whose Lean file changed later; its own pair equals the Library.
- `62a8273c` submitted five pairs: its SupercuspidalCoefficientCompactSupportReduction
  pair and the Aubert/General pairs CartanCentralSupport,
  RationalCartanCentralSupport, RationalCuspidalCoefficientCompactSupport and
  RepresentedStandardCuspidality. `d8629ccb` later changed all of them except
  CartanCentralSupport. It added the three-premise statement and theorem,
  kept the four-premise ones with their signatures, and named two local
  topology instances. The four changed pairs equal the copies frozen by
  `d8629ccb`.

| File under `Langlands/` | SHA256 at Library `d82893a7` and in the workspace |
| --- | --- |
| `Representation/Plancherel/UnramifiedRationalNormalizedInducedFiniteness.lean` | `0617ebd573ef22cc943e3658b37fdccb492dd8cf2173d4af48a3510b8719fbd1` |
| `Representation/Plancherel/UnramifiedRationalNormalizedInducedFiniteness.md` | `ce6725e907e7e2de1ebf249613d312e9fc37f01ba1c3897dd348156b81a3e958` |
| `Representation/Plancherel/UnramifiedRationalNormalizedInducedFinitenessProof.lean` | `1d75679704dda94b9b860d21ad79f9bb7570f1e40ee374714cc2a3297dd82215` |
| `Representation/Plancherel/UnramifiedRationalNormalizedInducedFinitenessProof.md` | `e1443289c74c5302d341928178a99e530e6a906ef05ae4a432badfe37c63cfd5` |
| `Representation/Plancherel/RationalUniversalTensorFinitenessStatement.lean` | `5ce0db0f86c502432451935faf45926d934aaa7bcfe9c6c40270959053a9ad66` |
| `Representation/Plancherel/RationalUniversalTensorFinitenessStatement.md` | `6c9cbcf5a1ec56a5f54958f6f18428a344ebde0cc3d0fc760d26ab4a77d9ab5b` |
| `Representation/Plancherel/RationalUniversalTensorFinitenessProof.lean` | `4f0c3c5b2a714de2bc6d80d3a98f1d621d7aa25dc89a63dfb0d5b8f420b408ad` |
| `Representation/Plancherel/RationalUniversalTensorFinitenessProof.md` | `15d68129b5d55a7183288fff4f7e75cca7eec14a9cbda6f9a70c47b6113aeca8` |
| `Representation/Plancherel/RationalNormalizedInducedSpecializationStatement.lean` | `db0de525899e037249aa1a4e09bc7237c5c4bb5de12342fa26be6828cf26781f` |
| `Representation/Plancherel/RationalNormalizedInducedSpecializationStatement.md` | `553eae1ec7b157ce3f1c1ae278c82eb8e164454d39b201ef7917f1bff4974764` |
| `Representation/Plancherel/RationalNormalizedInducedSpecializationProof.lean` | `63e0905ee9a4376c202b60a93a1581a398dcd6a2dcc51751c066db9cade6e234` |
| `Representation/Plancherel/RationalNormalizedInducedSpecializationProof.md` | `5d52f4625ea7dc428f71f6d0952de80cf310d9a9040792d60fc48b95c03d346a` |
| `Representation/Plancherel/UnramifiedRationalCoefficientAlgebra.lean` | `86cfa29a5a2906b6d3e49171b3eabaca797f7b14e067494265acf1e7cca1aa25` |
| `Representation/Plancherel/UnramifiedRationalCoefficientAlgebra.md` | `c74ebdaf8391d90a97334fa328820e0da3a919d73e778fbfc7604d2aacf602aa` |
| `Representation/Plancherel/UnramifiedRationalNormalizedModels.lean` | `7674224558a8dc5375bdb6bee08d1d1eb0c91f3051d0c2bc3d6c72894f80ca5b` |
| `Representation/Plancherel/UnramifiedRationalNormalizedModels.md` | `f3c47218eb59b2f379eca821edddcf1f531920b0f1fd44d7663a600941e4598f` |
| `Representation/Plancherel/UnramifiedRationalNormalizedSpecialization.lean` | `fb06f74b3f23baee0494e77f27d6525b7ef772455041b270f5350f22637f7a2d` |
| `Representation/Plancherel/UnramifiedRationalNormalizedSpecialization.md` | `185e9aa9b8e4b6fcd79cb9062f597e6842e0295558eb479a0979d59f7b0cba77` |
| `Representation/Induction/FixedVectorModel.lean` | `9e1c49fd75c09db857a61b2e770659c95c9d45156c55c5170da6696fe05b4127` |
| `Representation/Induction/FixedVectorModel.md` | `5ad6412809cd607cece7d10f050eed4b5e7f6b067bc31753aec3bdb32c9ca0b5` |
| `Representation/Induction/CompactQuotientProof.lean` | `fc60f8cfac2022bc4b7796bc624c3d171fb7e9a6f410befe0082d00a0d0abf30` |
| `Representation/Induction/CompactQuotientProof.md` | `e187c66eb2a15a6167dcbb33265ee6da6d654a879338fc162777eb65f85c1cfc` |
| `Representation/Exponents/PositiveUnramifiedCentralTwist.lean` | `f6745a24612f14bbabda98c5436184c8529dcecb69121befd9e624a53f7f1956` |
| `Representation/Exponents/PositiveUnramifiedCentralTwist.md` | `32ddc4abcf260c13154ede7e3a68ca2673cd6037959db2dff834bc930c5e6e0b` |
| `Representation/Filtration/CentralEigenspaceSplitting.lean` | `e62bccd1f1a66809c76a7a3a8f22aac25b562080dd1caacbc36ca5c8b150361e` |
| `Representation/Filtration/CentralEigenspaceSplitting.md` | `20493f49e929a04fe92015f4e35f6b31912feb238326e8f3d7258b89b8d3147f` |
| `Representation/CuspidalSupport/RationalUniversalProgeneratorComparisonProof.lean` | `a764e19fc1c78b43e17e6a1847895e2d051139601e681e798db6c0691fec271c` |
| `Representation/CuspidalSupport/RationalUniversalProgeneratorComparisonProof.md` | `4335422884c5de9d218b8ee76ce89fa359091513c9cf4c40ccb90c133b956426` |
| `Representation/Plancherel/UnramifiedRationalConjugateAdmissibility.lean` | `1d4c183fd7a4bace32a81be8a4d3dfa5dd6ec7dc0fdfc240470d576c21eb8d35` |
| `Representation/Plancherel/UnramifiedRationalConjugateAdmissibility.md` | `3c7e00a60e7c377c169d9492f4354e843b6f3ec5c346a8c552e3be9781899247` |
| `Representation/Plancherel/ParabolicGenericIrreducibilityStatement.lean` | `14bd3cd0f0d13e1b056a4d7e2efaf7023c57869feb6d613854b552e1315af8ee` |
| `Representation/Plancherel/ParabolicGenericIrreducibilityStatement.md` | `d9a2f32519727cf39c910afda46a5e5543181fc4518386c408d9fe13caa0a6ec` |
| `Representation/Plancherel/FiniteMatrixOpennessStatement.lean` | `8f176d39dd2583f0352028c8b36d1fc39c8f87ffb5d2eee612c86caf9a23d400` |
| `Representation/Plancherel/FiniteMatrixOpennessStatement.md` | `d1249f681edf5ccaf0c8390310421ba5ffe44377bb3b555c27955dd3dd41a173` |
| `Representation/Families/RenardFamilyStatements.lean` | `08b1db42e951221c2f706b1742d6bb08e09255e719fcb3258beebae4364b62c3` |
| `Representation/Families/RenardFamilyStatements.md` | `535b20f35c867381ddfe42fe17764dc4c376da9aedc6c3617deaa943d72a3b7d` |
| `Representation/Plancherel/FiniteMatrixOpennessProof.lean` | `49b9ed3820d9d82c94d88ee3b685e04f15656ee8e9a9c8fcbc884f55b99fe1dc` |
| `Representation/Plancherel/FiniteMatrixOpennessProof.md` | `505a18ee2aebcdb1b2c23d28785fa461f7bfeef5cf42788606c776f1d1de9a93` |
| `Representation/Plancherel/CompactFixedFamilyOpennessStatement.lean` | `eddf3aa377151464051fbc7b6dd994f943950bc7ebb219cffc8b2d7e4cbaaa2a` |
| `Representation/Plancherel/CompactFixedFamilyOpennessStatement.md` | `a7e41eff126b828502f617e87ff7090b9a5238a50c6768240a83ffe13b4b3526` |
| `Representation/Plancherel/RationalUnitaryNonvanishing.lean` | `67e935d4485e203b90c2b706190b99a4922ed1e52c3b30933afb4d607d8e2f59` |
| `Representation/Plancherel/RationalUnitaryNonvanishing.md` | `3f8f3239da29179c15abd5b08bab6b850f0523d550d57b27407dc4b21e2e1ebc` |
| `Representation/Aubert/General/JacquetMultiplicityIrreducibility.lean` | `394dbae83693b1489e45cf1084548dc020eb094f0e1249d1dea6ab8f9ded1047` |
| `Representation/Aubert/General/JacquetMultiplicityIrreducibility.md` | `674f2f4ab0b3d208d5e77931a21068125ba5dacee5f159d5e3d16d4d0443e3ad` |
| `HarmonicAnalysis/HarishChandraSchwartz/LeftHaarSquareIntegrableUnitarity.lean` | `441ff85bf9705aa5b37feb0158a8003000cd82f99bc220cd69d3c15dea7d9a71` |
| `HarmonicAnalysis/HarishChandraSchwartz/LeftHaarSquareIntegrableUnitarity.md` | `9a0fa5000643dc000e0217b4ea53ef2c5eeede3451ea5fe1f23012c5e3121b1f` |
| `Representation/Unitary/CompactCoefficientProof.lean` | `7255759799be76763de386d39c59c84d08cbf6138391627754d3f5fb996b6ec0` |
| `Representation/Unitary/CompactCoefficientProof.md` | `9a7eaf9e5ea6d287feb7aa71b40f300f0c7400585691d7e69412b6a68828f536` |
| `Representation/Aubert/General/RationalCompactRestrictionUnitarity.lean` | `4a620c31771ce00a91f33be9ea60d54a3ad9f98bb5d013d2b84649f9fbbb125d` |
| `Representation/Aubert/General/RationalCompactRestrictionUnitarity.md` | `95e3b287c417d473e4321e340843e4d074178600fcfac175e2b2515d79a1bfe4` |
| `Representation/Aubert/General/NormalizedInductionUnitarity.lean` | `e6b94cc72ba02a9922dcb5ded86e7492a82d5449d20209c4bae738eccc3d6077` |
| `Representation/Aubert/General/NormalizedInductionUnitarity.md` | `11086e47da8a48360d24c7c0881b493628bbb45890b80cdb2a78345cfc1a543f` |
| `Representation/Unitary/AdmissibleSemisimplicityProof.lean` | `6ab7fc6314e497e4975515c4b29625577ad1495bc0c359b483dd25dd1c216cfe` |
| `Representation/Unitary/AdmissibleSemisimplicityProof.md` | `6be55902f968a286270dcadfe9de58a9251ff49c17c662a89731f9558fd64fc4` |
| `Representation/Exponents/MaximalLeviReducibilityUnitaryInputs.lean` | `5f1ba7a81ca82241750cfbb1338b9bd24a878c85e8b00a4d7bbcf73c38c5d659` |
| `Representation/Exponents/MaximalLeviReducibilityUnitaryInputs.md` | `c7df06abc4519cb605fa57432a1bd5823a0587ef1befe12a16de397889655438` |
| `Representation/Exponents/MaximalLeviReducibilityInductionInputs.lean` | `fb0242052e75b1f000dc66a94078bb077041fc5daa8cf00e5531384ed2ad87d8` |
| `Representation/Exponents/MaximalLeviReducibilityInductionInputs.md` | `94d9d73f7429da730d5beffc870d2c392c7034dd74dc0c9ffd537bc8334ff9ac` |
| `Representation/Exponents/SupercuspidalCoefficientCompactSupportStatement.lean` | `2a0aa51eb1fbc6f97d8444b715ba1de52bff76811f0fde8e554259228f96ee3d` |
| `Representation/Exponents/SupercuspidalCoefficientCompactSupportStatement.md` | `f25decd8ba18dbf12bb1369cb8e43d09b123f2111008a272700adfb8942fa9da` |
| `Representation/Exponents/SupercuspidalCoefficientCompactSupportReduction.lean` | `73411dfe39380cabca8ae1564cdd6020e0de16cb1cb2e2fac400645a7f0c6b1a` |
| `Representation/Exponents/SupercuspidalCoefficientCompactSupportReduction.md` | `3023c5df24fde6992ca834b985c969d20c378d635a22c2fd9ca1eb17e27f91b9` |

## Scope

This note covers VI.8 only. The Theorem that ends VI.7, on PDF p.193, and
VI.9 are outside it. The unpublished assertions remain with the whole-book
parent task. This note declares no section, chapter or book completion.
