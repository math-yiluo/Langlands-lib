# Renard VI.8: algebraic families of representations

Worker 709 wrote this note on 6 November 2026 against Library
`f73044d93e675a78ed75830ef026b3224514e510` and updated it on 7 November 2026
against Libraries `d82893a7de0b168873a15c6c7b0a731deb27aa23`,
`2816ea5d81e2fb9b0512bd1d8dec2ad7797026fd`,
`568f1cff4df2c51ba08b932716bf99235d0032c7` and
`c0c7eab6ed7a8f4f31468b6ad2abf14e21493127`. It maps every printed assertion
of VI.8, and the proof steps the source spells out, to the published Lean
declarations that state or prove them. Where no declaration does, the note
says so. It also records six source reading notes. Worker 6 owns the other
Chapter VI notes, such as the
[parabolic functors note](parabolic-functors-tempered-progress.md), and this
note does not change them.

Sixty-six published units carry the material or relate to it. They are
twenty-two statement units, fifteen proof units and twenty-nine definition
units, listed under Receipts. Worker 709 is the sole author of the statement
units `51d6b0a6`, `2c2abfbe`, `a852fcc2`, `aa949da3`, `ec9f856f`, `fdf7b191`,
`da8c4071` and `97c603d2` and of the definition units `20a07cb0` and
`e21322ee`. Worker 709 is a coauthor of the proof unit `b366b62b`, which
Worker 1603 submitted. Worker 709 is neither an author nor a coauthor of the
other fifty-five units. This note documents them and is not a review of them.

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
  and flatness (`Module.Flat`) are separate hypotheses or conclusions in the
  statements below.
- The category `M(G, B)` is `Langlands.Renard.AlgebraicFamily.FamilyModule B G`,
  in [RenardFamilyCategory](../../Langlands/Representation/Families/RenardFamilyCategory.md):
  the full subcategory of the published `SmoothRep B G` on the objects whose
  carrier is a flat `B`-module. Its morphisms are all `B`-linear
  `G`-equivariant maps. `AdmissibleFamilyModule B G` is the full subcategory
  of objects whose fixed vectors under every open subgroup with compact
  carrier are finite over `B`. Both need only a commutative ring `B` and a
  topological group `G`. No statement below is phrased through these
  categories.
- The statements for a general family are in namespace
  `Langlands.Renard.AlgebraicFamily`, in
  [RenardFamilyStatements](../../Langlands/Representation/Families/RenardFamilyStatements.md).
  They quantify over every reduced Noetherian `ℂ`-algebra `B` of finite type
  and every topological group `G` with `Langlands.Topology.IsLocallyProfinite G`.
  A compact open subgroup is `K : OpenSubgroup G` with `IsCompact (K : Set G)`.
  All five statements are proved: `FixedTensorComparisonStatement`,
  `FlatnessCriterionStatement`, `LocalFreeCoverStatement`,
  `AdmissibilityCriterionStatement` and `SpecializationAdmissibilityStatement`.
  Their conjunction `Statements` has no published proof.
- The VI.8.6 statement for a general family is in
  [RenardFamilyEndomorphismStatement](../../Langlands/Representation/Families/RenardFamilyEndomorphismStatement.md),
  with the same binders, and is proved. The VI.8.4 and VI.8.5 statements are in
  [RenardGenericIrreducibilityStatements](../../Langlands/Representation/Families/RenardGenericIrreducibilityStatements.md).
  They concern the published complex `leviInductionFunctor` of an actual
  rational parabolic. A Zariski principal open subset of `X(M)` is
  `Plancherel.rationalUnramifiedPrincipalOpen`, the nonvanishing locus of a
  polynomial in the published canonical coordinates. All three statements of
  that module are unproved.
- Three further statements are each in their own module, and all three are
  unproved: the VI.8.5 Lemma in
  [RenardCentralCharacterSplittingStatement](../../Langlands/Representation/Families/RenardCentralCharacterSplittingStatement.md),
  the VI.8.6 Example in
  [RenardSupercuspidalFamilyEndomorphismStatement](../../Langlands/Representation/Families/RenardSupercuspidalFamilyEndomorphismStatement.md)
  and the last claim of the VI.8.1 Example in
  [RenardUniversalFamilySpecializationStatement](../../Langlands/Representation/Families/RenardUniversalFamilySpecializationStatement.md).
  Rows (L5), (Ex6) and (Ex-c) describe them.
- Base change, induction and Jacquet modules over a general `B` are in
  [RenardFamilyParabolicFunctors](../../Langlands/Representation/Families/RenardFamilyParabolicFunctors.md),
  for every commutative `ℂ`-algebra `B`. `baseChange C ρ` acts on
  `C ⊗[B] V` by `1 ⊗ ρ(g)`. For a semidirect decomposition `P = M ⋉ U` of
  subgroups of `G` with `U` closed, `Induced` and `inducedRepresentation`
  are normalized induction. The inducing representation is the Levi family
  twisted by the constant half modulus `c_U^{1/2}` and inflated along the
  projection `P →* M`, as in Renard's VI.1.2.3. `Jacquet` and
  `jacquetRepresentation` are the `U`-coinvariants with the Levi acting
  through `c_U^{-1/2}`. `LeviInduced`, `leviInducedRepresentation` and
  `leviJacquetRepresentation` specialize these to an actual rational
  parabolic with rational Levi. The module defines objects only; the
  functors on morphisms are not bundled. Its Markdown records that
  Renard's `δ_P` is reciprocal to the Library's `c_U`.
  Its lemma `inducingRepresentation_eq_twist_of_isUnimodularModulus` shows
  that under `Aubert.General.IsUnimodularModulus U hU` the inducing
  representation is the twist by the half modulus on all of `P`, the twist
  used by the published complex induction. For an actual parabolic over a
  nonarchimedean local field, that hypothesis on the radical image is the
  published theorem
  `Aubert.General.RepresentedParabolic.isUnimodularModulus_pointImage_radical`
  in [LeviRadicalCompactSubgroups](../../Langlands/Representation/Exponents/LeviRadicalCompactSubgroups.md).
  It needs `[ValuativeRel k] [IsNonarchimedeanLocalField k]`, which the
  functors module does not assume; its other instance hypotheses are those
  of the module. The functors Markdown and author qualification say
  instead that this unimodularity is not proved in the Library, which is
  wrong (see the `20a07cb0` qualification below). No Library theorem
  combines the two results, and none identifies `leviInducedRepresentation`
  at `B = ℂ` with the published `leviInductionFunctor`.
- The statements on these constructions are in
  [RenardFamilyParabolicStatements](../../Langlands/Representation/Families/RenardFamilyParabolicStatements.md)
  (base change commutes with induction; Jacquet modules preserve finite
  generation) and
  [RenardFamilyParabolicFlatnessStatements](../../Langlands/Representation/Families/RenardFamilyParabolicFlatnessStatements.md)
  (flatness of induction and of Jacquet modules; induction preserves
  admissibility). They quantify over every nonarchimedean local field, every
  connected reductive group and every actual rational parabolic, including
  `P = G`, and over every reduced Noetherian `ℂ`-algebra `B` of finite type.
  All of them are unproved.
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

The published flatness, finiteness and specialization results for induced
and Jacquet families therefore concern one family: the universal unramified
twist of a smooth representation of an actual rational Levi, and its
normalized parabolic induction. Normalized induction and Jacquet functors
exist over every algebra `unramifiedRegularFunctions ν`, and normalized
induction preserves admissibility there under the hypotheses of row (L2).
For a general `B`, rows (P1), (P1-iso), (R1), (L1), (T4) and (P6) are
proved. The category of `(G, B)`-modules is
defined, and so are base change, induction and Jacquet modules of families
as objects. Base change preserves smoothness and flatness, as row (BC)
records. The flatness, admissibility, base-change and finiteness statements
for induction and Jacquet modules, rows (I), (L2), (P2), (J) and (P3), are
unproved. No named specialization construction for a general family is
defined.

## Assertion map

| Assertion | Published declarations | Status |
| --- | --- | --- |
| (D) | `Langlands.Renard.AlgebraicFamily.FamilyModule`, `flatProperty`, `FamilyModule.of`, `FamilyModule.toSmoothRep`, `AdmissibleFamilyModule`, `admissibleProperty`, `AdmissibleFamilyModule.finite_fixedVectors` in [RenardFamilyCategory](../../Langlands/Representation/Families/RenardFamilyCategory.md) | Defined. `FamilyModule B G` is the full subcategory of `SmoothRep B G` on the objects whose carrier is flat over `B`, so its morphisms are all `B`-linear `G`-equivariant maps. `AdmissibleFamilyModule B G` is its full subcategory of objects whose fixed vectors under every open subgroup with compact carrier are finite over `B`. The definitions need only a commutative ring `B` and a topological group `G`, and impose none of Renard's standing hypotheses on `B`. No additive or abelian structure is defined. The statements of the other rows take `Representation B G V` with separate smoothness and flatness hypotheses, not objects of these categories |
| (P1) | `Langlands.Renard.AlgebraicFamily.AdmissibilityCriterionStatement` in [RenardFamilyStatements](../../Langlands/Representation/Families/RenardFamilyStatements.md), proof `admissibilityCriterion` in [RenardFamilyAdmissibilityProof](../../Langlands/Representation/Families/RenardFamilyAdmissibilityProof.md). Mathlib: `Module.finitePresentation_of_finite`, `Module.Flat.projective_of_finitePresentation`, instance `Module.Flat.of_projective` | Proved, by Worker 1761 in proof task `eb5ee8fa-29f5-4671-9ecd-e6259db108d3`. For smooth `ρ`, `V` is flat with every compact-open `V^K` finite if and only if every compact-open `V^K` is finite and projective. In the forward direction, `flatness_iff_fixed_flat` of row (R1) makes each `V^K` flat; a finite module over the Noetherian `B` is finitely presented, and a flat finitely presented module is projective. In the converse, projective modules are flat, and `flatness_iff_fixed_flat` gives flatness of `V` |
| (P1-iso) | `FixedTensorComparisonStatement` (RenardFamilyStatements), proof `fixedTensorComparison` in [RenardFamilyFixedTensorProof](../../Langlands/Representation/Families/RenardFamilyFixedTensorProof.md); helpers `coefficientAverage`, `coefficientFixedProjection`, `coefficientFixedProjection_comp`, `trivialTensor_isSmooth`, `coefficientAverage_tensor`, `fixedTensorComparison_of_smooth` (same module); private helpers `fixedTensorMap_bijective` and `fixedCoefficientFiber_bijective` in [RationalNormalizedInducedSpecializationProof](../../Langlands/Representation/Plancherel/RationalNormalizedInducedSpecializationProof.md) | Proved, by Worker 1761 in proof task `eb5ee8fa`. For smooth `ρ`, compact open `K` and every `B`-module `E`, the map `E ⊗[B] V^K → E ⊗[B] V` is injective and its range is `(E ⊗[B] V)^K`, with `G` acting through the second factor. The statement does not state the inverse. The proof restricts scalars along `ℂ → B` and uses the published finite-orbit averaging of `Langlands.Compact.CharZero`; naturality makes the average `B`-linear, and `coefficientFixedProjection` is a `B`-linear retraction of `V` onto `V^K`. Averaging on `E ⊗[B] V` acts as `id ⊗ e_K`, so tensoring the retraction gives the source's inverse `e ⊗ v ↦ e ⊗ e_K v`. `fixedTensorComparison_of_smooth` needs only a commutative `ℂ`-algebra `B`, smoothness and a compact open subgroup. The earlier private helpers prove the comparison for the universal family and `E = ℂ` through `evaluation r χ`, without a flatness premise |
| (R1) | `FlatnessCriterionStatement` (RenardFamilyStatements), proofs `flatnessCriterion` and `flatness_iff_fixed_flat` in [RenardFamilyFlatnessProof](../../Langlands/Representation/Families/RenardFamilyFlatnessProof.md); `flat_of_smooth_fixed_flat` in [UnramifiedRationalNormalizedInducedFinitenessProof](../../Langlands/Representation/Plancherel/UnramifiedRationalNormalizedInducedFinitenessProof.md) | Proved, by Worker 1761 in proof task `eb5ee8fa`. `flatness_iff_fixed_flat` holds for every commutative `ℂ`-algebra `B` and locally profinite `G`: a smooth `V` is flat if and only if every compact-open `V^K` is. The forward direction applies `Module.Flat.of_retract` to the retraction `coefficientFixedProjection` of row (P1-iso). The reverse direction is the earlier `flat_of_smooth_fixed_flat`, which holds over any commutative ring for a locally compact nonarchimedean group and uses the equational criterion `Module.Flat.of_forall_isTrivialRelation`; the published `Langlands.Topology.LocallyProfiniteProof.vanDantzig` supplies the nonarchimedean structure |
| (Sp) | `evaluation`, `tensorEvaluation`, `inducedEvaluation`, `jacquetEvaluation`; `InducedSpecializationFiber`; `SpecializationAdmissibilityStatement` (RenardFamilyStatements) | Defined for the universal family, its induction and its Jacquet model. For a general family there is no named construction or functor: `SpecializationAdmissibilityStatement` writes the fiber inline as `ℂ ⊗[B] V`, with `B` acting on `ℂ` through `χ : B →ₐ[ℂ] ℂ` and `g` acting by `Module.End.baseChangeHom B ℂ V (ρ g)`. Related: the predicate `Langlands.Renard.AlgebraicFamily.CompactCompressionPrincipalOpen.IsFullSpecialization S A χ D`, in [CompactCompressionPrincipalOpen](../../Langlands/Representation/Families/CompactCompressionPrincipalOpen.md), says that some intertwiner from a smooth representation `A` with `S`-coefficients to a smooth representation `D`, compatible with `χ : S →ₐ[ℂ] ℂ`, has bijective scalar extension `ℂ ⊗[S] A → D`, so that `D` is the fiber of `A` at `χ` up to isomorphism. It is a helper for row (P4) |
| (L1) | `SpecializationAdmissibilityStatement` (RenardFamilyStatements), proof `specializationAdmissibility` in [RenardFamilySpecializationProof](../../Langlands/Representation/Families/RenardFamilySpecializationProof.md) | Proved, by Worker 1761 in proof task `eb5ee8fa`. For smooth flat `ρ` with every compact-open `V^K` finite, and every `χ`, the fiber `ℂ ⊗[B] V` is `Langlands.IsAdmissible`. Its tensor factors are in the opposite order to the source's `V ⊗_B B/I_χ`. The proof shows that scalar extension preserves smoothness (`baseChange_isSmooth`, row (BC)), and that `ℂ ⊗[B] V^K` maps onto the `K`-fixed vectors of the fiber by the fixed-tensor comparison of row (P1-iso), so these are finite-dimensional. Every open subgroup contains a compact open one (Van Dantzig), which gives the all-open-subgroups condition of `IsAdmissible`. The proof does not use the flatness hypothesis, which the statement keeps |
| (Ex-a) | `universalRepresentation`, `isSmooth_universalRepresentation` (Models); `universalTensorFlatness` in [RationalUniversalTensorFinitenessProof](../../Langlands/Representation/Plancherel/RationalUniversalTensorFinitenessProof.md) | Defined; smoothness proved. Flatness of `B ⊗[ℂ] E` is proved with no admissibility hypothesis |
| (Ex-b) | `RationalUniversalTensorFinitenessStatement` in [RationalUniversalTensorFinitenessStatement](../../Langlands/Representation/Plancherel/RationalUniversalTensorFinitenessStatement.md); proof `rationalUniversalTensorFiniteness`; `universalTensorFixedComparison`, `universalTensorFiniteness`; `Langlands.Plancherel.universalTensorFixedInclusion_bijective`, `Langlands.Plancherel.universalTensorFixed_finite_projective` | Proved. For `σ` admissible, `B ⊗[ℂ] E` is flat, and for every compact open `J` there is an equivalence between the `J`-fixed vectors of `universalRepresentation` and `B ⊗ σ^J` whose inverse is the canonical inclusion `tensorFixedInclusion`; the fixed space is finite and projective. The comparison needs no admissibility; finiteness uses `IsAdmissible σ`. `tensorFixedEquiv`, in the c957a9bb proof module, is a variant over a field `k` for any group. Admissibility of `V_B` itself is also proved: `universalRepresentation_isAdmissible`, in [UnramifiedRationalConjugateAdmissibility](../../Langlands/Representation/Plancherel/UnramifiedRationalConjugateAdmissibility.md), says that `universalRepresentation r σ` is `IsAdmissible` over `RegularAlgebra r` when `σ` is. Its generic form `Langlands.Plancherel.isAdmissible_universalUnramifiedRepresentation` holds for a locally compact nonarchimedean group, continuous `ν` and Noetherian `unramifiedRegularFunctions ν` |
| (Ex-c) | `Langlands.Renard.AlgebraicFamily.UniversalSpecializationStatement` in [RenardUniversalFamilySpecializationStatement](../../Langlands/Representation/Families/RenardUniversalFamilySpecializationStatement.md); `tensorEvaluation`, `tensorEvaluation_inducing_action` (Specialization) | Stated, unproved; proof task `5e350f7e-8ef9-47a2-9c4e-db945cc4586e`. For every group `G` with a topology, every family `ν : I → (G →* ℝ≥0ˣ)`, every complex representation `π` on `V`, not assumed smooth, and every `χ` in `Plancherel.unramifiedCharacters ν`, the statement asserts a `ℂ`-linear equivalence `e : ℂ ⊗[B] (B ⊗[ℂ] V) ≃ V`, with `B = Plancherel.unramifiedRegularFunctions ν` acting on `ℂ` through evaluation at `χ`. It intertwines `baseChange ℂ` of `Plancherel.universalUnramifiedRepresentation ν π` with the twist `π ⊗ χ`, and `e (c ⊗ (b ⊗ v)) = (c · b(χ)) v`. Only the last claim of the Example is stated, in the generality its author qualifications record. For the universal family of an actual Levi, the map to `π ⊗ χ` is the published `tensorEvaluation`, with its equivariance proved; the Specialization Markdown makes no fiber claim. (C2) below proves the induced form |
| (I) | `Langlands.Renard.AlgebraicFamily.LeviInduced`, `leviInducedRepresentation`, `Induced`, `inducedRepresentation`, `isSmooth_inducedRepresentation`, `induced_covariant_levi_unipotent` in [RenardFamilyParabolicFunctors](../../Langlands/Representation/Families/RenardFamilyParabolicFunctors.md); `InductionFlatStatement` in [RenardFamilyParabolicFlatnessStatements](../../Langlands/Representation/Families/RenardFamilyParabolicFlatnessStatements.md); `Induced`, `inducedRepresentation` (Models); `Langlands.Plancherel.UnramifiedNormalized.normalizedInductionFunctor` in [UnramifiedNormalizedModels](../../Langlands/Representation/Plancherel/UnramifiedNormalizedModels.md); `universalInduced_flat` (c957a9bb proof module) | Over a general `B` the induced family is defined as an object and is smooth, with Renard's covariance (VI.1.2.3) proved; the functor on morphisms is not bundled. Its flatness is stated, unproved: `InductionFlatStatement` says that for smooth `σ` on a flat `B`-module `E`, `LeviInduced … σ` is flat over `B`; proof task `9631258e-aa94-42dc-8780-79b148f09c97`. Over any `unramifiedRegularFunctions ν`, `normalizedInductionFunctor` is normalized induction on smooth representations. Flatness of the induced family is proved for the universal family only |
| (VI.8.2.1) | `Langlands.Induction.fixedEvaluationEquiv`, `Langlands.Induction.exists_finset_doubleCoset_representatives` in [FixedVectorModel](../../Langlands/Representation/Induction/FixedVectorModel.md) | Proved for unnormalized `smoothInduced P σ` over any commutative coefficient ring: for a finite set `t` of double-coset representatives, the `K`-fixed vectors are equivalent to `∏ i : t, fixedVectors σ (conjOpenSubgroup P K i)`. The subgroups are literal open subgroups of `P`, and the finite product plays the role of the direct sum |
| (L2) | `InductionAdmissibleStatement` (RenardFamilyParabolicFlatnessStatements); `Langlands.Induction.smoothInduced_isAdmissible_of_compactSpace` in [CompactQuotientProof](../../Langlands/Representation/Induction/CompactQuotientProof.md); `UniversalInducedCoefficientFinitenessStatement` in [UnramifiedRationalNormalizedInducedFiniteness](../../Langlands/Representation/Plancherel/UnramifiedRationalNormalizedInducedFiniteness.md), proof `universalInducedCoefficientFiniteness`; `universalInducing_fixed_finite_free`, `universalInduced_fixed_finite_free`; `Langlands.Plancherel.UnramifiedNormalized.isAdmissible_inducedRepresentation` (UnramifiedRationalConjugateAdmissibility) | For a general `B`, stated, unproved: `InductionAdmissibleStatement` says that for smooth `σ` on a flat `E` whose fixed vectors under every compact open subgroup of `M(F)` are finite over `B`, the fixed vectors of `leviInducedRepresentation … σ` under every compact open subgroup of `G(F)` are finite over `B`; flatness, the rest of admissibility, is row (I). Proof task `9631258e`. Proved in three special forms. The first: unnormalized smooth induction from any subgroup `P` with compact `P\G` preserves `IsAdmissible` over any Noetherian ring. The second: for `π` admissible, the universal normalized induced family is flat and its compact-open fixed spaces are finite and projective. The proof shows they are finite free. The third: over a Noetherian `unramifiedRegularFunctions ν`, normalized induction of any admissible representation is admissible. It assumes a locally compact nonarchimedean group `H`, a semidirect decomposition `d` of a subgroup `Q` with closed normal factor `V` and continuous projection `d.projection`, and compact `Q\H` |
| (BC) | `Langlands.Renard.AlgebraicFamily.baseChange`, `baseChange_tmul` (RenardFamilyParabolicFunctors); `Langlands.Renard.AlgebraicFamily.baseChange_isSmooth`, `baseChange_fixed_finite` (RenardFamilySpecializationProof). Mathlib: instance `Module.Flat.baseChange` | Defined on objects: for a commutative `B`-algebra `C`, `baseChange C ρ` acts on `C ⊗[B] V` by `1 ⊗ ρ(g)`, with the scalars on the left. Preservation of smoothness is proved by Worker 1761 in proof task `eb5ee8fa`, as a step of row (L1). `baseChange_isSmooth` holds for every commutative ring `B`, commutative `B`-algebra `A`, group `G` with a topology and smooth `ρ`. Its conclusion is smoothness of `(Module.End.baseChangeHom B A V).toMonoidHom.comp ρ`, which is `baseChange A ρ` by definition, although the theorem does not use that name. Preservation of flatness is Mathlib's instance `Module.Flat.baseChange`: `C ⊗[B] V` is flat over `C` when `V` is flat over `B`. In the same proof module, `baseChange_fixed_finite` assumes a commutative `ℂ`-algebra `B`, a topological group `G`, smooth `ρ` and a compact open `K` with `V^K` finite over `B`. It concludes that the `K`-fixed vectors of the scalar extension are finite over `A`. No theorem states that `baseChange` sends objects of `FamilyModule B G` to objects of `FamilyModule C G`, and the functor on morphisms is not bundled |
| (P2) | `InductionBaseChangeStatement` in [RenardFamilyParabolicStatements](../../Langlands/Representation/Families/RenardFamilyParabolicStatements.md); `Langlands.Plancherel.scalarExtensionOfSemilinear` (Statement module) | Stated, unproved; proof task `4df85a84-3852-487f-8906-e6796bdf997f`. For `C` with `[CommRing C] [Algebra ℂ C] [IsNoetherianRing C] [IsReduced C] [Algebra B C] [IsScalarTower ℂ B C]`, not assumed of finite type, and smooth `σ` on a flat `B`-module `E`, there is a `C`-linear equivalence `C ⊗[B] LeviInduced … σ ≃ LeviInduced … (baseChange C σ)` intertwining the two actions of `G(F)`. The scalar tower is Worker 709's reading of "`C` soit un `B`-module", recorded in the statement's Markdown; see reading note 2. Naturality in `E` is not stated |
| (VI.8.2.2) | `InductionBaseChangeStatement` (RenardFamilyParabolicStatements); `inducedScalarExtension`, `inducedScalarExtension_tmul` | For a general `B`, part of the unproved `InductionBaseChangeStatement`: its equivalence `e` satisfies `Induction.eval _ _ (e (c ⊗ₜ f)) g = c ⊗ₜ Induction.eval _ _ f g`, which determines `e`. For the universal family, defined for `C = ℂ` through `evaluation r χ`, with the pure-tensor formula proved |
| (C2) | `RationalNormalizedInducedSpecializationStatement`; proof `rationalNormalizedInducedSpecialization`; `Langlands.Plancherel.UnramifiedNormalized.inducedSpecializationEquiv`, `inducedSpecializationEquiv_tmul` in [UnramifiedNormalizedInducedSpecialization](../../Langlands/Representation/Plancherel/UnramifiedNormalizedInducedSpecialization.md) | Proved for the universal normalized induced family: for every smooth `π` and every unramified character `χ`, `inducedScalarExtension r h hU π χ` is bijective. No admissibility is assumed. This combines (C2) with (Ex-c). The definition unit `c08a8104`, by Worker 1444 with coauthor Worker 1635, extracts the group-generic part of that proof. For a locally compact nonarchimedean group `G`, a closed subgroup `P = M ⋉ U` with `U` closed, continuous projection to `M` and compact `P\G`, any family `ν` of continuous positive characters of `M` and any complex representation of `M`, `inducedSpecializationEquiv` is the `ℂ`-linear equivalence from the fiber at `χ` of the universal normalized induced module over `unramifiedRegularFunctions ν` to the complex normalized induction of the twist by `χ`, with `z ⊗ f ↦ z • inducedEvaluation f`. No root presentation is used |
| (J) | `Langlands.Renard.AlgebraicFamily.Jacquet`, `jacquetRepresentation`, `leviJacquetRepresentation`, `isSmooth_jacquetRepresentation` (RenardFamilyParabolicFunctors); `JacquetFlatStatement` (RenardFamilyParabolicFlatnessStatements); `Jacquet`, `jacquetRepresentation` (Models); `Langlands.Plancherel.UnramifiedNormalized.normalizedJacquetFunctor` (UnramifiedNormalizedModels); `jacquetEvaluation` (Specialization) | Over a general `B` the normalized Jacquet module is defined as an object, the `U`-coinvariants with `M` acting through `c_U^{-1/2}`, and preserves smoothness. Its flatness is stated, unproved: `JacquetFlatStatement` says that for smooth `ρ` on a flat `B`-module `V`, `Jacquet ρ (pointImage (r ≫ p))` is flat over `B`. It has no Levi binders, since the `B`-module `V_N` does not depend on the Levi or the normalization. Proof task `9631258e`. Over any `unramifiedRegularFunctions ν`, `normalizedJacquetFunctor` is the normalized Jacquet functor on smooth representations, and the specialization map is defined for the universal family only |
| (P3) | `JacquetFiniteTypeStatement` (RenardFamilyParabolicStatements); related: `Langlands.Plancherel.RationalSupercuspidalJacquetFamilyFiniteStatement` in [UnramifiedRationalJacquetFinitenessStatement](../../Langlands/Representation/Plancherel/UnramifiedRationalJacquetFinitenessStatement.md) | Stated, unproved; proof task `4df85a84`. For smooth `ρ` on a flat `B`-module `V` with `ρ.asModule` finite over `MonoidAlgebra B (rationalPoints G)`, the module `(leviJacquetRepresentation … ρ).asModule` is finite over `MonoidAlgebra B (rationalPoints M)`. This is Worker 709's reading of "`B`-modules de type fini", recorded in the statement's Markdown; see reading note 3. The conjunction of (P2) and (P3) is `ParabolicStatements`. Related, not the Proposition: for the universal supercuspidal family, finiteness of the Jacquet module is the separate target `RationalSupercuspidalJacquetFamilyFiniteStatement`, which is unproved; see the [uniform compression note](uniform-compression-progress.md) |
| (T4) | `LocalFreeCoverStatement` (RenardFamilyStatements), proof `localFreeCover` in [RenardLocalFreeCoverProof](../../Langlands/Representation/Families/RenardLocalFreeCoverProof.md). Mathlib: `Module.free_of_flat_of_isLocalRing`, `Module.FinitePresentation.exists_free_localizedModule_powers`, `Module.Finite.of_localizationSpan`, `Module.freeLocus_eq_univ_iff`, `Module.basicOpen_subset_freeLocus_iff` | Proved, in proof task `f10ce878-b279-4004-8426-7e12cf971e20`, by Worker 1603 with coauthor Worker 709. For `B` as in VI.8 and a `B`-module `M`: `M` is finite and projective if and only if there are `f : Fin r → B` generating the unit ideal such that each localization `LocalizedModule (Submonoid.powers (f i)) M` is finite and free over `Localization.Away (f i)`. The proof uses only Mathlib, not Bourbaki's text. For the forward direction, the set of `t` with finite free localization at `t` spans the unit ideal: otherwise it lies in a maximal ideal `m`, the localization at `m` is free over the local ring, and finite presentation gives such a `t` outside `m`. A finite subset then gives the cover. For the converse, the cover makes `M` finite, `IsNoetherianRing B` makes it finitely presented, and every prime lies in a basic open set of the cover, which is in the free locus. Of the hypotheses on `B` beyond `CommRing`, only `IsNoetherianRing B` is used |
| (Sp-φ) | none | Not stated |
| (P4) | `Langlands.Renard.AlgebraicFamily.InducedIrreducibilityOpenStatement` in [RenardGenericIrreducibilityStatements](../../Langlands/Representation/Families/RenardGenericIrreducibilityStatements.md). Related: `Langlands.Plancherel.FiniteMatrixIrreducibilityOpennessStatement` in [FiniteMatrixOpennessStatement](../../Langlands/Representation/Plancherel/FiniteMatrixOpennessStatement.md), proved by `Langlands.Plancherel.finiteMatrixIrreducibilityOpenness` in [FiniteMatrixOpennessProof](../../Langlands/Representation/Plancherel/FiniteMatrixOpennessProof.md); `Langlands.Plancherel.CompactFixedFamilyOpennessStatement` in [CompactFixedFamilyOpennessStatement](../../Langlands/Representation/Plancherel/CompactFixedFamilyOpennessStatement.md), proved by `Langlands.Plancherel.compactFixedFamilyOpenness` in [CompactFixedFamilyOpennessProof](../../Langlands/Representation/Plancherel/CompactFixedFamilyOpennessProof.md); `Langlands.Renard.AlgebraicFamily.MatrixGenerationWitness.wordDeterminant`, `specialize_wordDeterminant`, `exists_principal_neighborhood` in [MatrixGenerationWitness](../../Langlands/Representation/Families/MatrixGenerationWitness.md) | Stated, unproved; proof task `2113598c-9c21-461a-9a44-f46066850c3e`. For an actual rational parabolic of a connected reductive group, an irreducible smooth `ρ` of the Levi points and an unramified character `ψ₀` with `i_P^G(ρ ⊗ ψ₀)` irreducible, the statement asserts a polynomial `f` in the published canonical coordinates of `X(M)` whose principal open set contains `ψ₀` and on which every `i_P^G(ρ ⊗ ψ)` is irreducible. Here `i_P^G` is the published `leviInductionFunctor`. That the open set contains `ψ₀`, which the source proof provides, is a reading recorded in the statement's Markdown. Related, not the Proposition: the statement `FiniteMatrixIrreducibilityOpennessStatement` concerns, for `x` in a topological space, a family of complex square matrices `A x j` on a finite coordinate space, indexed by `j` in any type, with every entry continuous in `x`. It asserts that the set of `x` at which the matrices `A x j` have no common invariant subspace other than zero and the whole space is open. It concerns finite matrices and openness in a given topology, not Zariski openness in `X(M)` or irreducibility of `π_ψ`. It is proved through the openness of generation of the full matrix algebra, `Langlands.Plancherel.FiniteMatrixOpenness.isOpen_adjoin_eq_top`, and Burnside's theorem `Langlands.SandwichDimensionBound.action_surjective`; the source argues through Burnside's theorem and a determinant. `CompactFixedFamilyOpennessStatement`, proved by `compactFixedFamilyOpenness`, transfers this to smooth representations. For a family `A x` of nontrivial smooth complex representations, indexed by a topological space, it takes one compact open `K` such that every irreducible subquotient of every `A x` has a nonzero `K`-fixed vector, bases of the `K`-fixed spaces indexed by one finite type, and continuous entries of the matrices `UnitarizabilityContinuation.fixedMatrix`. It asserts that the set of `x` with `A x` irreducible is open. It again concerns openness in a given topology, and it supplies neither the subgroup `K`, nor the bases, nor an irreducible `π_{ψ_0}`. The definition unit `054b6891`, by Worker 1444 in proof task `2113598c`, implements the determinant step algebraically, over any commutative `ℂ`-algebra `B`. For a family of square matrices `A j` over `B` whose specialization at `χ₀ : B →ₐ[ℂ] ℂ` is irreducible in the sense of `Langlands.UnitarizabilityContinuation.IsIrreducibleFamily`, `exists_principal_neighborhood` gives `f : B` with `χ₀ f = 1` such that the specialization at every `χ` with `χ f ≠ 0` is irreducible. The witness `f` is the determinant `wordDeterminant` of words in a free algebra, which replace the source's Hecke operators. Its Markdown records that it supplies neither a detecting compact open subgroup for induced unramified twists, nor a coefficient matrix model of their fixed vectors, nor the conversion from a regular function to a polynomial in the canonical coordinates, and that it does not prove `InducedIrreducibilityOpenStatement`. Since Library `c0c7eab6`, further helpers from proof tasks `2113598c` and `468db4c1` are published. The unproved statement `Langlands.Renard.AlgebraicFamily.InducedTwistsUniformDetectionStatement` (`3794a38a`, Worker 452), in [InducedTwistsUniformDetectionStatement](../../Langlands/Representation/Families/InducedTwistsUniformDetectionStatement.md), extracts a step of the source proof. With the binders of `InducedIrreducibilityOpenStatement`, it asserts one compact open `K` of `G(k)` such that every irreducible subquotient of every `leviInductionFunctor` of `ρ ⊗ ψ`, for every unramified `ψ`, has a nonzero `K`-fixed vector. The source's paragraph proves more: one `K` detects the whole inertial support. In [InducedIrreducibilityOpenReduction](../../Langlands/Representation/Families/InducedIrreducibilityOpenReduction.md), `exists_principal_neighborhood_of_detection` derives the conclusion of `InducedIrreducibilityOpenStatement` for `ρ` and `ψ₀` from that statement and a family `A` with `IsGlobalCoefficientFamily A M e D`, defined in [GlobalCompressionPrincipalOpen](../../Langlands/Representation/Families/GlobalCompressionPrincipalOpen.md). There `e` identifies `B` with the regular functions on `X(M)`, every compact-open fixed space of `A` is free and finite over `B`, and `A` specializes fully, in the sense of `IsFullSpecialization`, to `D ψ = i_P^G(ρ ⊗ ψ)` at every `ψ`. No Library declaration constructs such a family or proves the detection statement, so `InducedIrreducibilityOpenStatement` remains unproved. The supporting definition units are as follows. `53476945` and `2ea5a23c`, by Worker 452, give the matrices `CompactCompressionMatrices.fixedMatrix` and `coefficientMatrix` of the compact average on a fixed-vector basis, in [CompactCompressionMatrices](../../Langlands/Representation/Families/CompactCompressionMatrices.md) and [CompactCompressionSpecialization](../../Langlands/Representation/Families/CompactCompressionSpecialization.md). `isIrreducible_iff_fixedMatrix` says that a nontrivial representation whose irreducible subquotients are all detected by `K` is irreducible exactly when its matrix family is, and `fixedMatrix_specializedBasis` says that the matrices of a fiber are the evaluated coefficient matrices. `d1330c28` and `14ba7211`, by Worker 1444 with coauthor Worker 1664, give `LocalizedMatrixPrincipalOpen.exists_polynomial_principal_neighborhood` in [LocalizedMatrixPrincipalOpen](../../Langlands/Representation/Families/LocalizedMatrixPrincipalOpen.md) and `UnramifiedPolynomialWitness.rationalRegularPolynomial` in [UnramifiedPolynomialWitness](../../Langlands/Representation/Families/UnramifiedPolynomialWitness.md). They turn the determinant witness of `054b6891`, after one localization, into a polynomial in the canonical coordinates whose principal open set is its nonvanishing locus. `16cce2f4` and `d7259534`, by Worker 452 with coauthors Workers 1664 and 1444, give `IsFullSpecialization`, the localized assembly `CompactCompressionPrincipalOpen.exists_polynomial_principal_neighborhood`, the global assembly and the reduction above. `fc7de660`, by Worker 1444, gives `ActualLevi.parameterEquiv` and `regularAlgebraEquiv` in [ActualLeviUnramifiedParameters](../../Langlands/Representation/Families/ActualLeviUnramifiedParameters.md), which transport unramified characters and regular functions along the Levi point equivalence. `c08a8104` is described in row (C2). The units from proof task `468db4c1` are by Worker 1598. The unproved `Langlands.Plancherel.RationalLeviInductionOpennessStatement` (`c6c03e68`), in [RationalLeviInductionOpennessStatement](../../Langlands/Representation/Plancherel/RationalLeviInductionOpennessStatement.md), concerns an admissible nonzero smooth inducing representation and one given compact open subgroup detecting every irreducible subquotient of every fiber. It asserts that the irreducible locus of `UnramifiedLeviInduction` is open in the continuous-character topology, not that it is Zariski open, and it keeps compactness of the quotient by the parabolic as a hypothesis. The unproved `Langlands.Plancherel.UnramifiedUniformGenerationStatement` (`afd034f2`), in [UnramifiedUniformGenerationStatement](../../Langlands/Representation/Plancherel/UnramifiedUniformGenerationStatement.md), asserts one compact open subgroup whose fixed vectors generate every fiber, for a finite-length inducing representation, given an opposite Iwahori contraction basis and `G = PK`; generation is not detection of subquotients. The definition unit `cc17f613`, `RationalNormalized.inducedLeviNormalizationEquiv` in [RationalLeviFixedMatrices](../../Langlands/Representation/Plancherel/RationalLeviFixedMatrices.md), identifies each fiber normalized on all of `P` (`complexInduced`) with `UnramifiedLeviInduction`, normalized on the Levi, and transports fixed bases and their matrices; radical unimodularity comes from the published `parabolicRadical_isUnimodular` |
| (T5) | `Langlands.Renard.AlgebraicFamily.GenericInducedIrreducibilityStatement` (RenardGenericIrreducibilityStatements). Related: `Langlands.Plancherel.ConditionalParabolicGenericIrreducibilityStatement` in [ParabolicGenericIrreducibilityStatement](../../Langlands/Representation/Plancherel/ParabolicGenericIrreducibilityStatement.md) | Stated, unproved; proof task `822bbd74-8853-4535-87b2-aede25e9a259`. For an irreducible supercuspidal `ρ`, the statement asserts a nonzero polynomial `f` in the same coordinates such that every `i_P^G(ρ ⊗ ψ)` with `ψ` in its principal open set is irreducible. The statement's Markdown explains why a nonzero `f` gives a nonempty Zariski open set. The conjunction of (P4) and (T5) is `GenericIrreducibilityStatements`. Related, not the Theorem: the unproved statement `ConditionalParabolicGenericIrreducibilityStatement` is adapted from Waldspurger 2003, Proposition IV.2.2(i) and the beginning of IV.3, not from Renard. For an irreducible smooth representation `π` of the Levi points that is square-integrable modulo the image `C` of the split component, it asserts a nonempty set `D` of unramified characters, open in the continuous-character topology, on which the induction `UnramifiedLeviInduction` of `π` twisted by `χ` is irreducible. Its hypothesis is square integrability, not supercuspidality, and its locus is open in that topology, not Zariski open. It does not by itself give a Zariski-open locus, and no Library declaration connects it to (T5). Its proof task is `468db4c1-297b-4d4e-8534-ed8de150ffc5` |
| (T5-a) | `Langlands.Aubert.General.RepresentedParabolic.exists_positive_unramifiedCharacter_norm_mul_eq_one`, `twistUnitaryCentralCharacter`, `exists_positive_unramifiedTwist_unitaryCentralCharacter` in [PositiveUnramifiedCentralTwist](../../Langlands/Representation/Exponents/PositiveUnramifiedCentralTwist.md) | Proved for a connected reductive group: an irreducible smooth representation has a positive unramified twist with unitary central character. The module was published with the VII.1.3 proof unit `228c630c`, which uses it. See reading note 5. The second claim, that a supercuspidal representation with unitary central character is unitary, is stated, unproved, as `Langlands.Aubert.General.RepresentedParabolic.SupercuspidalUnitaryCentralCharacterUnitarizableStatement` in [MaximalLeviReducibilityUnitaryInputs](../../Langlands/Representation/Exponents/MaximalLeviReducibilityUnitaryInputs.md). It covers every connected reductive group, with supercuspidality as vanishing of the normalized Jacquet modules of all proper parabolics; its proof task is `df1b860d-7b40-4e1b-9e06-fd01618045ff`. The source's route through VI.2.1 and IV.3.2 is split as follows. `SupercuspidalUnitaryCoefficientCompactSupportStatement`, in [SupercuspidalCoefficientCompactSupportStatement](../../Langlands/Representation/Exponents/SupercuspidalCoefficientCompactSupportStatement.md), states VI.2.1 (a) ⇒ (b) for these representations, when irreducible: for every unitary central character datum, every descended coefficient norm has compact support on the quotient by the full abstract centre. It is unproved. In [SupercuspidalCoefficientCompactSupportReduction](../../Langlands/Representation/Exponents/SupercuspidalCoefficientCompactSupportReduction.md), `supercuspidalUnitaryCoefficientCompactSupportStructuralReduction` derives it from the three unproved statements `StandardCocharacterStatement`, `RelativeRootSystemStatement` and `JointSpecialCompactBasisExistenceStatement`; the earlier `supercuspidalUnitaryCoefficientCompactSupportReduction` also assumes `ParabolicDynamicStatement`. For IV.3.2, `Langlands.UnitaryCentralCharacter.isUnitarizable_of_compact_coefficientNorm_of_nonarchimedean`, in [CompactCoefficientProof](../../Langlands/Representation/Unitary/CompactCoefficientProof.md), proves that a smooth irreducible representation of a nonarchimedean group with a unitary central character datum and compactly supported coefficient norms is unitarizable. No Library declaration composes these into a proof of `SupercuspidalUnitaryCentralCharacterUnitarizableStatement`. Two variants are proved: `Langlands.Aubert.General.RationalPointFamily.isUnitarizable_of_compact_normKernel_restriction`, in [RationalCompactRestrictionUnitarity](../../Langlands/Representation/Aubert/General/RationalCompactRestrictionUnitarity.md), assumes compact coefficients after restriction to the norm kernel, and `Langlands.HarishChandraSchwartz.isUnitarizable_of_irreducible_isSquareIntegrable_leftHaar`, in [LeftHaarSquareIntegrableUnitarity](../../Langlands/HarmonicAnalysis/HarishChandraSchwartz/LeftHaarSquareIntegrableUnitarity.md), assumes square integrability modulo a central subgroup. The forward VI.2.1 proof for standard families is in Worker 6's [VI.2.1 map](cuspidal-decomposition-source-map.md) |
| (T5-b) | `Langlands.Aubert.General.RepresentedParabolic.LeviInductionUnitarizableStatement` (MaximalLeviReducibilityUnitaryInputs); `leviInductionUnitarizable_of_inputs` in [MaximalLeviReducibilityInductionInputs](../../Langlands/Representation/Exponents/MaximalLeviReducibilityInductionInputs.md); `Langlands.Aubert.General.normalizedInductionFunctor_obj_isUnitarizable_of_compactSpace` in [NormalizedInductionUnitarity](../../Langlands/Representation/Aubert/General/NormalizedInductionUnitarity.md); `Langlands.admissibleUnitarySemisimplicity` in [AdmissibleSemisimplicityProof](../../Langlands/Representation/Unitary/AdmissibleSemisimplicityProof.md); `Langlands.Plancherel.rationalUnramifiedRegular_exists_unitary_finset_ne_zero` in [RationalUnitaryNonvanishing](../../Langlands/Representation/Plancherel/RationalUnitaryNonvanishing.md) | Partly stated. The first claim, that normalized induction from an actual rational parabolic preserves unitarizability, is the unproved `LeviInductionUnitarizableStatement` (Renard IV.2.3). `leviInductionUnitarizable_of_inputs` derives it from four unproved structural statements: `RationalReductiveUnimodularityStatement`, `StandardCocharacterStatement`, `ArbitraryParabolicQuotientCompactStatement` and `ParabolicRootPresentationExistenceStatement`. `normalizedInductionFunctor_obj_isUnitarizable_of_compactSpace` proves it for a closed subgroup `P` with compact `P\G`, keeping the triviality of the modular character of `G` and the identity for the modular character of `P` as premises. For "hence completely reducible", `admissibleUnitarySemisimplicity` proves `AdmissibleUnitarySemisimplicityStatement`: when compact open subgroups are cofinal, an admissible unitarizable representation is semisimple. The filtration from VI.5.3(iii) and the pairwise distinctness of the central characters outside a Zariski closed subset are not stated as steps of VI.8.5. Related: `rationalUnramifiedRegular_exists_unitary_finset_ne_zero` gives, for a connected reductive group, one unitary unramified character at which finitely many nonzero regular functions are all nonzero; it proves nothing about central characters. Since Library `c0c7eab6`, the structural inputs of the distinctness step are stated. The unproved `Langlands.Aubert.General.RepresentedParabolic.LeviNormalizerWeylGroupStatements` (`90015773`, Worker 1697), in [LeviNormalizerQuotientStatements](../../Langlands/Representation/Exponents/LeviNormalizerQuotientStatements.md), is the conjunction of two statements for an actual rational Levi `M` of an actual rational parabolic over a nonarchimedean local field. `LeviNormalizerFiniteQuotientStatement` asserts finitely many points `g j` of `G(k)` normalizing `M` such that every point normalizing `M` lies in some `g j · M(k)` (V.4.3.3 with V.3.7). `LeviNormalizerNormFixingStatement` asserts that a point normalizing `M` whose automorphism preserves every rational-character norm on the centre of `M(k)` lies in `M(k)` (V.3.5). The Markdown names a consumer `genericInducedIrreducibility_of_inputs`, which is not in the Library at `c0c7eab6`. Four definition units by Worker 1739 from proof task `822bbd74` prove both conclusions when a cocharacter whose dynamic parabolic is the given `p` is supplied: `IsRationalLeviSubgroup.exists_finite_normalizer_representatives_of_dynamicParabolic` and `mem_pointImage_of_normalizes_of_norm_of_dynamicParabolic` in [DynamicLeviNormalizer](../../Langlands/Representation/Exponents/DynamicLeviNormalizer.md) (`7e5d7c99`), built from `IsSplitComponent.exists_finite_normalizer_representatives` in [FiniteNormalizerRepresentatives](../../Langlands/Representation/Exponents/FiniteNormalizerRepresentatives.md) (`54a4c290`), `IsSplitComponent.mem_range_of_normalizes_of_norm` in [LeviNormalizerBridge](../../Langlands/Representation/Exponents/LeviNormalizerBridge.md) (`c46d1642`) and `IsSplitComponent.comp_automorphism_eq_of_norm` in [SplitComponentNormRigidity](../../Langlands/Representation/Plancherel/SplitComponentNormRigidity.md) (`d5ecc4cf`). Since the dynamic presentation stays an input, no Library theorem derives `LeviNormalizerWeylGroupStatements` from them |
| (L5) | `Langlands.Renard.AlgebraicFamily.CentralCharacterSplittingStatement` in [RenardCentralCharacterSplittingStatement](../../Langlands/Representation/Families/RenardCentralCharacterSplittingStatement.md). Related: `Langlands.CentralCharacterSplitting.splitting_of_distinct_centralCharacters`, `HasCentralCharacterSplitting`, `iSup_centralCharacterSpace_eq_top` in [CentralCharacterSplitting](../../Langlands/Representation/Filtration/CentralCharacterSplitting.md); `Langlands.CentralEigenspaceSplitting.eigenSubrep`, `eigenEquivGraded`, `iSup_eigenSubrep` in [CentralEigenspaceSplitting](../../Langlands/Representation/Filtration/CentralEigenspaceSplitting.md) | Stated, unproved; proof task `5c0deaf5-6a6f-45df-ba43-e623ce9dcd51`. For any field `k`, any group `G`, any subgroup `Z` of the centre, every `A : Rep k G` with a filtration `s : ObjectRepFiltration A n` and injective `χ : Fin n → Z →* kˣ` such that each `z ∈ Z` acts on graded piece `i` by `χ i z`, the statement asserts `A ≅ ∐ i, s.gradedRepresentation i` in `Rep k G`. Related, not the statement: the definition unit `61300f68`, by Worker 1739 in proof task `822bbd74`, proves `splitting_of_distinct_centralCharacters` under the same hypotheses with `Z` the full centre and `[Infinite k]`. Its conclusion `HasCentralCharacterSplitting s χ` says that each central-character subrepresentation for `χ i` is equivalent to graded piece `i`, that these subrepresentations are independent, and that every subrepresentation is the supremum of its intersections with them; `iSup_centralCharacterSpace_eq_top` adds that they span. No Library theorem converts this into the coproduct isomorphism. The proof finds one element of the group algebra on which the characters take pairwise distinct values, which is where `Infinite k` is used, and applies `CentralEigenspaceSplitting`. That earlier module assumes one central element taking pairwise distinct scalars; see reading note 4 |
| (T5-c) | `Langlands.Aubert.General.isIrreducible_induction_of_semisimple_jacquetHom_rank_le_one`, `isIrreducible_induction_of_unitary_jacquetHom_rank_le_one` in [JacquetMultiplicityIrreducibility](../../Langlands/Representation/Aubert/General/JacquetMultiplicityIrreducibility.md) | Related, not the step. A nontrivial semisimple normalized induction `I σ` is irreducible if `Hom(r(I σ), σ)` has rank at most one; Frobenius reciprocity is applied inside the proof. The unitary version replaces semisimplicity by admissibility, unitarizability and cofinal compact opens, through `admissibleUnitarySemisimplicity`. The rank bound, which the source obtains from (T5-b) and (L5), is a hypothesis |
| (P6) | `Langlands.Renard.AlgebraicFamily.EndomorphismScalarStatement` in [RenardFamilyEndomorphismStatement](../../Langlands/Representation/Families/RenardFamilyEndomorphismStatement.md); proof `endomorphismScalar` and helpers `exists_fixedVectors_retraction`, `projective_fixedVectors`, `eq_zero_of_forall_linearForm`, `exists_fiber_scalar` in [RenardFamilyEndomorphismProof](../../Langlands/Representation/Families/RenardFamilyEndomorphismProof.md) | Proved, by Worker 950 in proof task `69958e59-18ba-448c-be38-d73030086488`. Take a smooth flat `ρ` with every compact-open `V^K` finite, a `G`-equivariant `B`-linear `φ`, and a Zariski-dense `Ξ`, meaning that every `b` vanishing on `Ξ` vanishes at every point. If every fiber `ℂ ⊗[B] V` at a point of `Ξ` is irreducible, then `φ` is the action of some `b : B`. It is stated for every locally profinite `G`. The proof does not follow the source's route through local freeness and does not use the statements of rows (P1) and (L1), which were unproved when it was published. Each compact-open `V^K` is a `B`-linear retract of the flat `V` and finite over the Noetherian `B`, hence projective. Linear forms `V →ₗ[B] B` separate vectors. Schur's lemma on the fibers at the points of `Ξ` and the Nullstellensatz give a linear relation between `φ` and the linear forms. Nakayama's lemma gives an element of the ideal of values of linear forms that acts as the identity on `V`, and writing it through linear forms produces `b`. See reading note 6 |
| (Ex6) | `Langlands.Renard.AlgebraicFamily.SupercuspidalFamilyEndomorphismStatement` in [RenardSupercuspidalFamilyEndomorphismStatement](../../Langlands/Representation/Families/RenardSupercuspidalFamilyEndomorphismStatement.md) | Stated, unproved; proof task `8ed6fa75-244f-4b83-9093-00ded0bdf73f`. For a nonarchimedean local field, a connected reductive group, an actual rational parabolic with rational Levi `M` and geometric unipotent radical, including `P = G`, and an irreducible supercuspidal smooth `σ` of `M(k)`, let `B` be `Plancherel.unramifiedRegularFunctions` of the rational norm characters of `M` and `ρ_B` the universal family `universalUnramifiedRepresentation` on `B ⊗[ℂ] W`. The statement asserts that every `B`-linear endomorphism of `LeviInduced … ρ_B` commuting with `leviInducedRepresentation` is multiplication by some `b : B`. The induction is the general-family construction of row (I). Only the first paragraph of the Example is stated; the consequence for the centre of `M(G)[ρ]`, which recovers VI.4.5, is not. Row (P6) is proved, but the source's route also needs (T5), which is unproved, and an identification of the fibers of `LeviInduced … ρ_B` with the induced twists |

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
   them. `CentralCharacterSplitting` assumes the source's hypothesis and
   replaces the single element by a linear combination of central elements,
   which exists over an infinite field such as `ℂ`. Over `𝔽_3` the four
   characters of `(ℤ/2)^2` into `{±1}` are pairwise distinct, but every
   linear combination takes at most three values on them, since `𝔽_3` has
   three elements.
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
   `V = ⋃_K V^K`. The published proof `endomorphismScalar` does not use
   this gluing. Its last step is algebraic, as row (P6) describes.

## Unpublished assertions

At Library `c0c7eab6` these assertions have no published statement:

1. (Sp) as a named construction for general families.
2. The functors on morphisms of (BC), (I) and (J) over a general `B`, and
   base change as a construction from `FamilyModule B G` to
   `FamilyModule C G`. Base change preserves smoothness and flatness, as
   row (BC) records.
3. (Sp-φ) and (T5-c); (T5-b) apart from its first claim and the normalizer
   inputs of `90015773`; and the consequence of (Ex6) for the centre of
   `M(G)[ρ]`.

The definition unit `b4543cde`, a Markdown correction of `20a07cb0` by
Worker 709, is accepted but is not in the Library at `c0c7eab6`, so this note
does not describe it.

These are stated but unproved:

- The conjunction `Statements` of the five statements of `51d6b0a6`. Each of
  the five is proved: (P1-iso), (R1), (T4), (P1) and (L1) by `850f515b`,
  `8f8bfb65`, `b366b62b`, `d6be4520` and `121e7cb2`. The RenardFamilyStatements
  Markdown refers to this note's earlier numbering, in which the five
  assertions were unpublished items 2, 3, 4 and 8.
- (P2) with (VI.8.2.2), and (P3), by `InductionBaseChangeStatement`,
  `JacquetFiniteTypeStatement` and their conjunction `ParabolicStatements`
  of `aa949da3`, with proof task `4df85a84-3852-487f-8906-e6796bdf997f`.
- The flatness in (I), (L2) and the flatness in (J), by
  `InductionFlatStatement`, `InductionAdmissibleStatement`,
  `JacquetFlatStatement` and their conjunction `ParabolicFlatnessStatements`
  of `ec9f856f`, with proof task `9631258e-aa94-42dc-8780-79b148f09c97`.
- (P4) and (T5), by `InducedIrreducibilityOpenStatement` and
  `GenericInducedIrreducibilityStatement` of `a852fcc2`, with proof tasks
  `2113598c-9c21-461a-9a44-f46066850c3e` and
  `822bbd74-8853-4535-87b2-aede25e9a259`.
- The second claim of (T5-a) and the first claim of (T5-b), by
  `SupercuspidalUnitaryCentralCharacterUnitarizableStatement` and
  `LeviInductionUnitarizableStatement` of `57393553`; and the VI.2.1 input
  `SupercuspidalUnitaryCoefficientCompactSupportStatement` of `156a0ca5`,
  which `62a8273c` and `d8629ccb` reduce to unproved structural statements.
- (L5), (Ex6) and (Ex-c), by `CentralCharacterSplittingStatement` of
  `fdf7b191`, `SupercuspidalFamilyEndomorphismStatement` of `da8c4071` and
  `UniversalSpecializationStatement` of `97c603d2`, with proof tasks
  `5c0deaf5-6a6f-45df-ba43-e623ce9dcd51`,
  `8ed6fa75-244f-4b83-9093-00ded0bdf73f` and
  `5e350f7e-8ef9-47a2-9c4e-db945cc4586e`.
- The helper statements `InducedTwistsUniformDetectionStatement` of
  `3794a38a`, `RationalLeviInductionOpennessStatement` of `c6c03e68` and
  `UnramifiedUniformGenerationStatement` of `afd034f2` (row (P4)), and
  `LeviNormalizerWeylGroupStatements` of `90015773` (row (T5-b)).

They remain with the whole-book parent task and these proof tasks. (P6), stated by `2c2abfbe`, is
proved by `52d9f689`. The three VI.8 statements
`UniversalInducedCoefficientFinitenessStatement`,
`RationalUniversalTensorFinitenessStatement` and
`RationalNormalizedInducedSpecializationStatement` came from statement task
`e2884067-b19a-4685-91d9-e62316299fc3`, and all three are proved. Of the
related statements, `4cadcefc` (row (T5)) is unproved, `b933342c` (row (P4))
is proved by `c3682633`, and `f12ff2f5` (row (P4)) is proved by `3c4b264f`.
The definition units `20a07cb0` and `e21322ee` carry the constructions of
rows (D), (BC), (I) and (J), and `054b6891` the determinant witnesses of row
(P4). The fourteen definition units new at `c0c7eab6` are helpers for rows
(P4), (C2), (L5) and (T5-b); none of them proves a statement of this note.

## Receipts

All sixty-six units are accepted and published. Each independent reviewer
approves without qualifications. Submitter and coauthors come from the
review-task bindings. Several bindings of units new at `c0c7eab6` list the
submitter among the coauthors; the table names the submitter once.
Twenty-one units record author
qualifications, summarized after the tables.

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
| VI.8.6 statement (`Langlands.Renard.AlgebraicFamily.EndomorphismScalarStatement`) | `2c2abfbe-19c0-4af3-9fff-586b312dbc63` | Worker 709 | Reviewer 17484 | `2816ea5d81e2fb9b0512bd1d8dec2ad7797026fd` |
| VI.8.4 and VI.8.5 statements (`Langlands.Renard.AlgebraicFamily.GenericIrreducibilityStatements`) | `a852fcc2-c3c6-40d3-9d89-56f6b85894e5` | Worker 709 | Reviewer 17501 | `2816ea5d81e2fb9b0512bd1d8dec2ad7797026fd` |
| Proof `Langlands.Plancherel.compactFixedFamilyOpenness` | `3c4b264f-ebe4-40ad-b040-51dd08b8d6be` | Worker 1598 | Reviewer 17456 | `2816ea5d81e2fb9b0512bd1d8dec2ad7797026fd` |
| VI.8.2 and VI.8.3 family constructions (`Langlands.Renard.AlgebraicFamily.leviInducedRepresentation`) | `20a07cb0-9490-40db-81c0-aefa82aa3fb1` | Worker 709 | Reviewer 17542 | `8b14de0b5103d5fc1e615f094904129bf8cfe3a3` |
| VI.8.1 category of `(G, B)`-modules (`Langlands.Renard.AlgebraicFamily.FamilyModule`) | `e21322ee-eddf-4bd9-8e70-9ea73c1b6bda` | Worker 709 | Reviewer 17566 | `0de01f0733138058931a79588c434f55c4639cbc` |
| VI.8.2 and VI.8.3 Propositions (`Langlands.Renard.AlgebraicFamily.ParabolicStatements`) | `aa949da3-cb50-4f5c-8dd4-513b8d9a6dfa` | Worker 709 | Reviewer 17589 | `0de01f0733138058931a79588c434f55c4639cbc` |
| VI.8.2 and VI.8.3 flatness and admissibility (`Langlands.Renard.AlgebraicFamily.ParabolicFlatnessStatements`) | `ec9f856f-48d8-4387-9bc8-0e7f08049065` | Worker 709 | Reviewer 17604 | `0de01f0733138058931a79588c434f55c4639cbc` |
| Proof `Langlands.Renard.AlgebraicFamily.localFreeCover` | `b366b62b-fdb1-4e65-9595-5a98329a8ddf` | Worker 1603; Worker 709 | Reviewer 17573 | `0de01f0733138058931a79588c434f55c4639cbc` |
| Proof `Langlands.Renard.AlgebraicFamily.fixedTensorComparison` | `850f515b-ab16-4f67-8baa-9281a12dbba1` | Worker 1761 | Reviewer 17578 | `0de01f0733138058931a79588c434f55c4639cbc` |
| Proof `Langlands.Renard.AlgebraicFamily.flatnessCriterion` | `8f8bfb65-8621-498f-af6a-0c167ceb8810` | Worker 1761 | Reviewer 17633 | `0de01f0733138058931a79588c434f55c4639cbc` |
| Proof `Langlands.Renard.AlgebraicFamily.endomorphismScalar` | `52d9f689-00dd-46e0-b376-9f1dd88f203a` | Worker 950 | Reviewer 17599 | `0de01f0733138058931a79588c434f55c4639cbc` |
| Matrix generation witnesses (`Langlands.Renard.AlgebraicFamily.MatrixGenerationWitness.wordDeterminant`) | `054b6891-91d6-45b1-90e8-343803bd2fbf` | Worker 1444 | Reviewer 17634 | `0de01f0733138058931a79588c434f55c4639cbc` |
| VI.8.5 Lemma statement (`Langlands.Renard.AlgebraicFamily.CentralCharacterSplittingStatement`) | `fdf7b191-6d84-4d58-88fb-237d0439d005` | Worker 709 | Reviewer 17694 | `a419cc8566081d901325c46ed3d626b2ebb04395` |
| VI.8.6 Example statement (`Langlands.Renard.AlgebraicFamily.SupercuspidalFamilyEndomorphismStatement`) | `da8c4071-8c14-42fb-8db4-07a7e70c864d` | Worker 709 | Reviewer 17801 | `a419cc8566081d901325c46ed3d626b2ebb04395` |
| VI.8.1 Example statement (`Langlands.Renard.AlgebraicFamily.UniversalSpecializationStatement`) | `97c603d2-ed5a-4a63-b107-f7ae7d97d826` | Worker 709 | Reviewer 17872 | `a419cc8566081d901325c46ed3d626b2ebb04395` |
| Proof `Langlands.Renard.AlgebraicFamily.admissibilityCriterion` | `d6be4520-5042-4f50-b8b6-8e7e7c2d4d30` | Worker 1761 | Reviewer 17652 | `a419cc8566081d901325c46ed3d626b2ebb04395` |
| Proof `Langlands.Renard.AlgebraicFamily.specializationAdmissibility` | `121e7cb2-5eb7-411c-b684-e4a558b96717` | Worker 1761 | Reviewer 17680 | `a419cc8566081d901325c46ed3d626b2ebb04395` |
| Central-character splitting (`Langlands.CentralCharacterSplitting.algebraFiltration`) | `61300f68-c176-4665-a243-65f423ee1e77` | Worker 1739 | Reviewer 17665 | `a419cc8566081d901325c46ed3d626b2ebb04395` |
| Actual Levi parameters (`Langlands.Renard.AlgebraicFamily.ActualLevi.parameterEquiv`) | `fc7de660-5a12-4ddd-9503-e186b533eb08` | Worker 1444 | Reviewer 17786 | `a419cc8566081d901325c46ed3d626b2ebb04395` |
| Uniform detection statement (`Langlands.Renard.AlgebraicFamily.InducedTwistsUniformDetectionStatement`) | `3794a38a-abb4-4ba6-b017-fb7b7452a619` | Worker 452 | Reviewer 17721 | `a419cc8566081d901325c46ed3d626b2ebb04395` |
| Localized compression assembly (`Langlands.Renard.AlgebraicFamily.CompactCompressionPrincipalOpen.IsFullSpecialization`) | `16cce2f4-903c-4064-baac-4a749eaf1bc6` | Worker 452; Workers 1664 and 1444 | Reviewer 17747 | `a419cc8566081d901325c46ed3d626b2ebb04395` |
| Compression matrices (`Langlands.Renard.AlgebraicFamily.CompactCompressionMatrices.fixedMatrix`) | `53476945-697c-4c0b-bff1-7f225c6a30b2` | Worker 452 | Reviewer 17658 | `a419cc8566081d901325c46ed3d626b2ebb04395` |
| Global coefficient families (`Langlands.Renard.AlgebraicFamily.CompactCompressionPrincipalOpen.IsGlobalCoefficientFamily`) | `d7259534-6390-4b3b-98b3-42e42c91b63e` | Worker 452; Workers 1664 and 1444 | Reviewer 17863 | `a419cc8566081d901325c46ed3d626b2ebb04395` |
| Specialized compression matrices (`Langlands.Renard.AlgebraicFamily.CompactCompressionMatrices.coefficientMatrix`) | `2ea5a23c-c745-4389-8020-3c4f3fc3a076` | Worker 452 | Reviewer 17708 | `a419cc8566081d901325c46ed3d626b2ebb04395` |
| Localized matrix neighborhoods (`Langlands.Renard.AlgebraicFamily.LocalizedMatrixPrincipalOpen.regularWitness`) | `d1330c28-7c80-4b27-928f-23c4bd0c5e3f` | Worker 1444; Worker 1664 | Reviewer 17711 | `a419cc8566081d901325c46ed3d626b2ebb04395` |
| Polynomial witnesses (`Langlands.Renard.AlgebraicFamily.UnramifiedPolynomialWitness.rationalRegularPolynomial`) | `14ba7211-ee9b-4a72-a338-db968eef48cd` | Worker 1444; Worker 1664 | Reviewer 17664 | `a419cc8566081d901325c46ed3d626b2ebb04395` |
| Generic induced specialization (`Langlands.Plancherel.UnramifiedNormalized.inducedSpecializationEquiv`) | `c08a8104-98e2-482c-87c8-7f07bf3a41e4` | Worker 1444; Worker 1635 | Reviewer 17742 | `a419cc8566081d901325c46ed3d626b2ebb04395` |
| Levi normalization fixed matrices (`Langlands.Plancherel.RationalNormalized.inducedLeviNormalizationEquiv`) | `cc17f613-6c68-4f94-bc45-5b93d8165392` | Worker 1598 | Reviewer 17684 | `a419cc8566081d901325c46ed3d626b2ebb04395` |
| Levi induction openness statement (`Langlands.Plancherel.RationalLeviInductionOpennessStatement`) | `c6c03e68-df08-48b9-8c78-38347333e56e` | Worker 1598 | Reviewer 17724 | `a419cc8566081d901325c46ed3d626b2ebb04395` |
| Uniform generation statement (`Langlands.Plancherel.UnramifiedUniformGenerationStatement`) | `afd034f2-f518-4c6d-ae66-8f8fb92c9a91` | Worker 1598 | Reviewer 17789 | `a419cc8566081d901325c46ed3d626b2ebb04395` |
| Dynamic Levi normalizers (`Langlands.GroupScheme.IsRationalLeviSubgroup.normalizerRepresentativesOfDynamicParabolic`) | `7e5d7c99-0587-4823-85b5-160fcb2812db` | Worker 1739 | Reviewer 17877 | `a419cc8566081d901325c46ed3d626b2ebb04395` |
| Finite normalizer representatives (`Langlands.GroupScheme.representativeNormalizerPoints`) | `54a4c290-fc05-46cb-a690-a549bda7bdea` | Worker 1739 | Reviewer 17839 | `a419cc8566081d901325c46ed3d626b2ebb04395` |
| Levi normalizer bridge (`Langlands.GroupScheme.IsSplitComponent.automorphismRestrictionIso`) | `c46d1642-8495-4993-a389-23154b224db5` | Worker 1739 | Reviewer 17805 | `a419cc8566081d901325c46ed3d626b2ebb04395` |
| Split-component norm rigidity (`Langlands.GroupScheme.IsSplitComponent.automorphismRestriction`) | `d5ecc4cf-69d6-435a-84fa-811f15c56a11` | Worker 1739 | Reviewer 17757 | `a419cc8566081d901325c46ed3d626b2ebb04395` |
| Levi normalizer statements (`Langlands.Aubert.General.RepresentedParabolic.LeviNormalizerWeylGroupStatements`) | `90015773-9e7c-4965-a995-5336cc21534e` | Worker 1697 | Reviewer 17700 | `a419cc8566081d901325c46ed3d626b2ebb04395` |

The VI.4.1 comparison `700fc1f0` is not a VI.8 result. It is listed because
the prerequisite section of the uniform compression note now cites it. The
statements `4cadcefc`, `b933342c` and `f12ff2f5` and the units `c3682633`,
`3c4b264f`, `9c0f4b4c`, `5c9af9f3` and `cb817814` are related to (T5), (P4) and the steps
of (T5) only, as the rows explain. All of them except `4cadcefc` came from
its proof task `468db4c1-297b-4d4e-8534-ed8de150ffc5`. The unit `57393553`
states the inputs for the unitary case of VII.1.3; this note uses two of
them. `62a8273c` and `d8629ccb` are conditional reductions, and
their reviewers record that they do not complete their host task. The
definition unit `054b6891` is a helper for (P4) and does not prove it. Of the
twenty-three units new at `c0c7eab6`, the three statement units by Worker 709
and the proofs `d6be4520` and `121e7cb2` carry rows (L5), (Ex6), (Ex-c), (P1)
and (L1); `121e7cb2` also proves the smoothness claim of row (BC). The other eighteen are helpers for rows (P4), (C2), (L5) and
(T5-b), as those rows explain; the statements among them are unproved.

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
| `2c2abfbe` | `f5d1f399-a1f8-4ab5-a981-90b92abd4857` | `8257a8ca-837a-4080-baf8-762b39e85b96` | `d2e1ace7-2261-41a1-9410-4aa669673356` (`lean.statement@1`) | `a86981edcf6b4f218733e6cafd45f493` |
| `a852fcc2` | `f5d1f399-a1f8-4ab5-a981-90b92abd4857` | `3b2e1b68-45f4-4ad7-93d4-82f7a8a834cc` | `1d658455-f5b1-4e7c-aa94-223b37235807` (`lean.statement@1`) | `0fa62a00f08641d5ac71a2b422bb0fed` |
| `3c4b264f` | `468db4c1-297b-4d4e-8534-ed8de150ffc5` | `3d833238-c6bb-4be4-8022-ee708cdac863` | `a3548efe-574f-4f5e-b350-78d5fe195f3a` (`lean.proof@1`) | `566322375fb64384a9be6077feb9d24b` |
| `20a07cb0` | `f5d1f399-a1f8-4ab5-a981-90b92abd4857` | `f7ac8a39-53b5-4fee-b36c-e4e847b1ece3` | `58c16490-ed0b-4a3f-a4d1-816c4b9d2c8e` (`lean.definition@1`) | `7cca5802a5ab441f9db0235afe50dc90` |
| `e21322ee` | `f5d1f399-a1f8-4ab5-a981-90b92abd4857` | `91a833b5-aaf1-437e-83fb-0436782a3dfd` | `8fd61f23-f06a-40d9-8a89-fae49ddab472` (`lean.definition@1`) | `2bc7fc2dd03844eead68d6525a0e61d6` |
| `aa949da3` | `f5d1f399-a1f8-4ab5-a981-90b92abd4857` | `d9aeafab-c149-4f4f-bcde-a1dd1f4bdeee` | `a89a0740-0c94-4ad5-99eb-8d75f3a49570` (`lean.statement@1`) | `9b3383e5e1f1433bafc1730cb25e1025` |
| `ec9f856f` | `f5d1f399-a1f8-4ab5-a981-90b92abd4857` | `32043101-1a78-4c3b-88ad-ca2011521d50` | `8ba35f10-1bf7-49de-ac74-d717ae426d8b` (`lean.statement@1`) | `79a5e9a4ab4e4c4b9ea1d1b34cb452a8` |
| `b366b62b` | `f10ce878-b279-4004-8426-7e12cf971e20` | `63c682ac-04d0-4a6c-a88d-8ec2551048e3` | `41654b4f-57fa-469b-9d6b-c52614d41b7a` (`lean.proof@1`) | `d78db5503c114cffa0e5dbc7a160818d` |
| `850f515b` | `eb5ee8fa-29f5-4671-9ecd-e6259db108d3` | `6165f8f0-b201-43da-ab36-045a00611619` | `50f84222-3596-4550-a115-d9cc1f2bb190` (`lean.proof@1`) | `67a7ab9baffd4c31a6b6c295f80328be` |
| `8f8bfb65` | `eb5ee8fa-29f5-4671-9ecd-e6259db108d3` | `11472351-2914-4e21-9e07-b31975ba5915` | `897921b0-fda9-41c5-8886-8f375da5d380` (`lean.proof@1`) | `a0edda4e0eda4cb69a8cd998905d8620` |
| `52d9f689` | `69958e59-18ba-448c-be38-d73030086488` | `9f231649-ac9f-438e-ad7d-7720603a6125` | `be36781c-203a-424e-b17b-be7189208759` (`lean.proof@1`) | `6efa4d84468c43d69034cbb1c06fcf73` |
| `054b6891` | `2113598c-9c21-461a-9a44-f46066850c3e` | `967f0fa7-33b2-49b2-bd81-2a1ab7ce6095` | `5a102f8e-f04b-41d5-a24d-91846e15a364` (`lean.definition@1`) | `a4c90a7a723a45c9b0f57f0dd6595fbe` |
| `fdf7b191` | `f5d1f399-a1f8-4ab5-a981-90b92abd4857` | `1860c1ea-ee5e-41d7-a5ab-1f8dd8714274` | `4f5e3328-d636-44d1-bcb7-f8d24c7d4703` (`lean.statement@1`) | `ca0078bcef2c41c3a3e31b2d200d58c2` |
| `da8c4071` | `f5d1f399-a1f8-4ab5-a981-90b92abd4857` | `6a4111d9-1ca3-493e-b600-f974b37d3a84` | `252176f4-bdb3-4d86-b8f7-f8571259359c` (`lean.statement@1`) | `370e51c93e454b6fbd6eb41aca307770` |
| `97c603d2` | `f5d1f399-a1f8-4ab5-a981-90b92abd4857` | `8daadb08-1fb8-48d2-adf0-c6970c2c349b` | `e08df165-3008-4216-af29-52058fc9302e` (`lean.statement@1`) | `20ac0f4eedb74622a79fd5f8b0be379b` |
| `d6be4520` | `eb5ee8fa-29f5-4671-9ecd-e6259db108d3` | `415b9d1e-a681-4b79-b6e0-0fa7e517df3b` | `0e74c2fb-cc60-424c-80fe-fcdc8827d25b` (`lean.proof@1`) | `63f48e84d1644935a5e96fcff59f332e` |
| `121e7cb2` | `eb5ee8fa-29f5-4671-9ecd-e6259db108d3` | `17f164c4-7d74-4ddf-91b6-16ffdae4aa6d` | `ec58abb0-da2d-4c5a-979d-99e2f339a035` (`lean.proof@1`) | `61fb7ade428e4e1aaff20ff971bb6cc3` |
| `61300f68` | `822bbd74-8853-4535-87b2-aede25e9a259` | `77602ca7-0301-4412-8f52-36a13bc3746c` | `034367cf-e081-4a28-8b49-f5f7d37eaf4b` (`lean.definition@1`) | `dab7cd5219cc417b87b6e15645f359d4` |
| `fc7de660` | `2113598c-9c21-461a-9a44-f46066850c3e` | `729048c2-307f-4f59-aaea-7510fd818cfd` | `1c1dc033-30f0-49ee-834c-4ec80cc75774` (`lean.definition@1`) | `2e7a1f88216349f980c407b5e09e9077` |
| `3794a38a` | `2113598c-9c21-461a-9a44-f46066850c3e` | `c1290b99-5288-4428-810f-3512a30b531a` | `c0963c18-1a66-4d9b-9c62-4e71fa40cdb5` (`lean.statement@1`) | `4e17521f125f49f4a51c1c259ac8fa05` |
| `16cce2f4` | `2113598c-9c21-461a-9a44-f46066850c3e` | `403364dc-f09e-4994-821b-1e6edfa3c3fd` | `dc0e1772-c50e-46da-b6ab-660ca2570152` (`lean.definition@1`) | `7977f811b6b74d9ab53e448797edc14b` |
| `53476945` | `2113598c-9c21-461a-9a44-f46066850c3e` | `706152fc-ce5d-44cf-b3c2-28b58605dbb8` | `6c9b3ecb-1342-4c1c-b1ce-eb0672fb5a23` (`lean.definition@1`) | `c5d1ad54e40045f6b57e97267358fe63` |
| `d7259534` | `2113598c-9c21-461a-9a44-f46066850c3e` | `48a0a26e-b025-469d-81f4-3bacb368b2a5` | `787e051e-0a65-46f9-86c9-333a96be1e5e` (`lean.definition@1`) | `371a3819221f4443824fb71d7a01c0b7` |
| `2ea5a23c` | `2113598c-9c21-461a-9a44-f46066850c3e` | `f5dee44f-a723-44de-ae22-c8779c104493` | `c834ea0c-f431-481a-b6d8-444f39644d72` (`lean.definition@1`) | `491caeff348049c18ac822064da6abbe` |
| `d1330c28` | `2113598c-9c21-461a-9a44-f46066850c3e` | `3900f8bd-7a62-4f42-8324-2c039dd9f1f6` | `5d69fd9b-7207-45ea-bdf2-4d628bb1b7f2` (`lean.definition@1`) | `569b5b6dec314bd5893993715976ea06` |
| `14ba7211` | `2113598c-9c21-461a-9a44-f46066850c3e` | `abb59210-d703-4c9e-ae6a-a882c0a172c6` | `ae5e2b17-2b61-4b0d-82d9-da762aac448a` (`lean.definition@1`) | `119d66e5751b47379caec4ff32f77c9a` |
| `c08a8104` | `2113598c-9c21-461a-9a44-f46066850c3e` | `be815929-7426-42d4-b868-a6ed42239153` | `0ffc4c7d-c6c6-4758-8758-7823cb3157cd` (`lean.definition@1`) | `4d928944d04b4387a4a7ac1d7cbe7f3f` |
| `cc17f613` | `468db4c1-297b-4d4e-8534-ed8de150ffc5` | `de74349a-efbc-4708-a4d8-b04ffe753495` | `14f0d4bb-a4fe-40f3-abbc-4f8512a2673e` (`lean.definition@1`) | `d759f37f729d429d9e50900042214108` |
| `c6c03e68` | `468db4c1-297b-4d4e-8534-ed8de150ffc5` | `979a0d3d-fc89-4159-a431-5a6442969c37` | `fcaaa1cd-30d9-4d6f-bcfc-cba0a8fef6ad` (`lean.statement@1`) | `4e66b5a98ad24b4582a5ac19026b1c2e` |
| `afd034f2` | `468db4c1-297b-4d4e-8534-ed8de150ffc5` | `f5c21b55-75d9-4a07-8cb4-ad50c33923ff` | `ef814742-7b08-4198-8cbe-8d67007c50a0` (`lean.statement@1`) | `b5ca936a3526428585bf65f02561d7a3` |
| `7e5d7c99` | `822bbd74-8853-4535-87b2-aede25e9a259` | `7e1c0540-eba4-4348-988c-d16d6decfd9b` | `6465ba38-ce2f-4d67-ad4a-c4dc3e4bd615` (`lean.definition@1`) | `f546fc9a32bf46f48e2a1ef64ffd378e` |
| `54a4c290` | `822bbd74-8853-4535-87b2-aede25e9a259` | `a938fcc2-fe64-457d-964e-8a40fd2ec8c9` | `8c94e88f-18c2-432f-b295-b44b6fcd1bcf` (`lean.definition@1`) | `089e53bc98df4a17aa05065bf431ab2c` |
| `c46d1642` | `822bbd74-8853-4535-87b2-aede25e9a259` | `aa6da2b0-528d-4f3e-a402-8dd7d8551d19` | `fd8cf952-69c1-49dc-af69-4dc2a4a654d8` (`lean.definition@1`) | `fc9e89a438af40888d3e506509f491b9` |
| `d5ecc4cf` | `822bbd74-8853-4535-87b2-aede25e9a259` | `df37ecd4-d60b-4e2b-bdc6-976bcbb89315` | `d2088875-e43d-45a6-9efa-15649faa21ac` (`lean.definition@1`) | `6e2ac2ca72b44468991a34be46e74e11` |
| `90015773` | `822bbd74-8853-4535-87b2-aede25e9a259` | `ff1672bb-d725-41fd-8ed0-664e9e20c120` | `9f261c6f-85ff-49c5-a90f-59e6ed415d21` (`lean.statement@1`) | `d271d39948f74b00a02ec722e8fed4be` |

The fifteen `lean.proof@1` receipts record the checks `lake-build`,
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
- `2c2abfbe`: the statement is made for every locally profinite `G`, and
  the source's proof was checked outside Lean to work in this generality;
  Zariski density is encoded through vanishing of elements of `B`; the
  specialization is `ℂ ⊗[B] V`, with the factors in the opposite order to the
  source's.
- `a852fcc2`: the VI.8.4 open set is required to contain `ψ₀`, which the
  source proof provides; Zariski open sets of `X(M)` are represented by
  principal open sets of polynomials in the published canonical coordinates,
  a correspondence argued in the Markdown and not checked in Lean; every
  actual rational parabolic, including `P = G`, is allowed.
- `20a07cb0`: only objects, defining laws and one comparison lemma are
  given; the functors on morphisms are not bundled, and flatness, the VI.8.2
  base-change isomorphism and the VI.8.3 finiteness are not asserted. No
  Noetherian, finite-type, reduced, flatness or smoothness hypothesis is
  imposed on `B`, `C` or the families. Induction uses the Levi half modulus
  inflated along the projection (VI.1.2.3), not the half modulus on all of
  `P` used by the published complex `Aubert.General.normalizedInductionFunctor`,
  `RepresentedParabolic.inductionFunctor` and `Plancherel.UnramifiedNormalizedModels`.
  The two agree under `Aubert.General.IsUnimodularModulus`
  (`inducingRepresentation_eq_twist_of_isUnimodularModulus`). The
  qualification goes on to say that the Library does not establish this
  hypothesis for represented radicals, so that agreement of
  `leviInducedRepresentation` at `B = ℂ` with the published complex
  induction is neither stated nor known in the Library. That part is
  inaccurate. `RepresentedParabolic.isUnimodularModulus_pointImage_radical`
  proves the hypothesis for the image of the unipotent radical of every
  closed subgroup over a nonarchimedean local field. Worker 709, the author, found the error after
  publication. What remains true is that no Library theorem states the
  agreement. The identification of `c_U` with Renard's `δ_P^{-1}` is a
  documented convention conversion, not a Lean statement.
- `e21322ee`: the definitions need only a commutative ring `B`; Renard's
  standing hypotheses on `B` are not imposed. Admissibility quantifies over
  open subgroups with compact carrier, as in RenardFamilyStatements, not over
  all open subgroups as the published `SmoothRep.IsAdmissible` does. No
  additive or abelian structure and no functor other than the two inclusions
  is defined.
- `aa949da3`: the scalars are on the left, as in Mathlib's base change, and
  the symmetry of the tensor product over `B` identifies the two orders.
  "`C` soit un `B`-module" is read as a commutative `B`-algebra with
  `IsScalarTower ℂ B C`, and "`B`-modules de type fini" as finite generation
  over the group algebra; both readings are Worker 709's. Naturality in `E`
  is not stated; the pure-tensor formula (VI.8.2.2) determines the
  isomorphism. Only the normalized Jacquet module is stated.
- `ec9f856f`: (I) states only flatness, since the other conditions hold by
  construction; (L2) states only finite generation of the compact-open fixed
  modules; (J) has no Levi binders, which is formally more general than the
  source, a reading that is Worker 709's; the functors on morphisms are not
  bundled.
- `fdf7b191`: the statement takes any group, any field, any representation
  and any central subgroup `Z`, which contains the source's case
  `Z = Z(G)`, a reading that is Worker 709's; the distinct central characters
  are given characters `χ_i`, pairwise distinct, with no continuity; the
  direct sum is the coproduct in `Rep k G`, and compatibility with the
  filtration is not stated.
- `da8c4071`: `B` is the published algebra of evaluation functions on `X(M)`,
  not the group algebra of `Λ(M)`; only the first paragraph of the Example is
  stated, not the consequence for the centre of `M(G)[ρ]`; the universal
  family is `B ⊗ W` rather than `W ⊗ B`, and the instance settings do not
  change the meaning.
- `97c603d2`: the statement is made for any group with a topology, any
  family of norm characters and any representation, smoothness not being
  needed; `B` is the algebra of evaluation functions rather than `ℂ[Λ(G)]`;
  the tensor orders are those of the published models, the fiber uses
  `ℂ` with `B` acting through `χ` rather than `B/I_χ`, and `π ⊗ χ` is the twist
  on `V` itself; only the last paragraph of the Example is stated.
- `90015773`: the statements are made over nonarchimedean local fields only,
  as in the source, and involve no topology on rational points; the
  faithfulness statement reformulates V.3.5 through norms on the centre of
  `M(F)`.

Worker 709 checked the Lean and Markdown files of the modules below at
Libraries `d82893a7`, `2816ea5d`, `568f1cff` and `c0c7eab6` and in the
workspace. The six files of `2c2abfbe`, `a852fcc2` and `3c4b264f` are new at
`2816ea5d`. The RenardFamilyParabolicFunctors pair of `20a07cb0` is new at
`8b14de0b`, and the sixteen files of the eight units added after it in the
previous update are new at `0de01f07`. The forty-eight files of the
twenty-four modules added in this update are new at `c0c7eab6`; their units
were published at `a419cc85`. Every other file is unchanged between
`d82893a7` and `c0c7eab6`. The table gives the hashes at `c0c7eab6`. Each file
in the workspace equals the Library, except RenardFamilyParabolicFunctors.md,
which in the workspace is the accepted, unpublished text of `b4543cde`.
Some frozen bundles differ from the Library:

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
- `a852fcc2` also froze the RenardFamilyEndomorphismStatement pair, equal to
  the Library. The own pairs of `2c2abfbe`, `a852fcc2` and `3c4b264f` equal
  the Library.
- `e21322ee` also froze the RenardFamilyParabolicFunctors pair, equal to the
  Library; the previous version of this note, equal to the Library at
  `568f1cff`; and `notes/renard/coverage.md` and `wiki/README.md`, which
  differ from the Library. `aa949da3` and `ec9f856f` each froze both of their statement
  pairs and the RenardFamilyCategory pair, all equal to the Library.
  `8f8bfb65` also froze the RenardFamilyFixedTensorProof pair, equal to the
  Library. The own pairs of all nine units added in the previous update
  equal the Library.
- `90015773` froze a LeviNormalizerQuotientStatements Markdown file that
  differs from the Library at line 46: the frozen copy writes
  `w = g j * l(p(m))`, the Library copy `w = g j * p(l(m))`. The review of
  `90015773` records the frozen expression as a harmless composition-order
  typo. Every other file frozen by the twenty-three units added in this
  update equals the Library. Besides their own pairs, they froze the pairs of
  other new units, the RenardFamilyCategory, RenardFamilyParabolicStatements,
  RenardFamilyParabolicFlatnessStatements, RenardFamilyFixedTensorProof,
  RenardFamilyFlatnessProof and MatrixGenerationWitness pairs, and, for
  `cc17f613`, `c6c03e68` and `afd034f2`, the
  RationalContinuousFixedBasesStatement and UnramifiedRationalFixedMatrices
  pairs. The InducedIrreducibilityOpenReduction pair is part of the bundle of
  `d7259534`, and the DynamicLeviNormalizer pair is the own pair of
  `7e5d7c99`.

| File under `Langlands/` | SHA256 at Library `c0c7eab6` |
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
| `Representation/Families/RenardFamilyEndomorphismStatement.lean` | `4ac205b3088fdf0951433cdf9b5206f0f8b56698a423f9996140d8ba6ea450ac` |
| `Representation/Families/RenardFamilyEndomorphismStatement.md` | `f19ce9ab3b841a5666cb5e9508e96fd2630b2718f0bc9595dd1a47f88896c878` |
| `Representation/Families/RenardGenericIrreducibilityStatements.lean` | `1397c5e2089ca4911130f0b38fc765a6b8177cd8e236907d9bfb912ab14fc932` |
| `Representation/Families/RenardGenericIrreducibilityStatements.md` | `09be6d017f5ee6edc3159f64602317e6d09db221bef6767ae7dab79aa634504a` |
| `Representation/Plancherel/CompactFixedFamilyOpennessProof.lean` | `695a3814d2dae88a1a2c3e437c64fceefe7779585277321b25d539d40896a905` |
| `Representation/Plancherel/CompactFixedFamilyOpennessProof.md` | `dca2856a73beb5c7cd0644dca435f89c33316f06684d5fa1ea5698f9619fec2c` |
| `Representation/Families/RenardFamilyParabolicFunctors.lean` | `f44635a8084d28f69d2a0e66df7e13195839f39c7e6fa5e9a6e3ca33d0cbab29` |
| `Representation/Families/RenardFamilyParabolicFunctors.md` | `ecf63a858785a66a4736ee9822f0897880ed7b36ec07688cfd7cf8868a95b31f` |
| `Representation/Families/RenardFamilyCategory.lean` | `faf7faf3c9681cd171a7b166828d84b3dcc630d6d7dec869b289af97d6caeb32` |
| `Representation/Families/RenardFamilyCategory.md` | `0dbafcdd43aa717773418c6e988c94a30be19b9506c07fecd85466c006864820` |
| `Representation/Families/RenardFamilyParabolicStatements.lean` | `5e1af6e065d6e8498d53425bf3fd87f7c8f37cc2dcfd6c1d9b28d09ca5148c3b` |
| `Representation/Families/RenardFamilyParabolicStatements.md` | `a89ab03b3ffff794f1163aceea8892e572313f8a076eaff51c9a6a04bfe63545` |
| `Representation/Families/RenardFamilyParabolicFlatnessStatements.lean` | `392a5e1986d68396b91206025b01772c8a6f20498d2d007a42bfc4e9bc975783` |
| `Representation/Families/RenardFamilyParabolicFlatnessStatements.md` | `2722a9fbe56ee4f1bfe212f8bdf59a02874472f2523ad91277317213c110b050` |
| `Representation/Families/RenardLocalFreeCoverProof.lean` | `7c79b24d1062097b8d289018628a2d587b6be5763db8e1e30b91f399466918e6` |
| `Representation/Families/RenardLocalFreeCoverProof.md` | `c36b4b6ca0a77c8d3d6ca8df37192ec5f50dd35b9ad9009f9a1f1f592563ae1e` |
| `Representation/Families/RenardFamilyFixedTensorProof.lean` | `b090834c7a0fa8f98f5b93542413d3f9996c6fe21ba11417f1ed5c6009f68a3a` |
| `Representation/Families/RenardFamilyFixedTensorProof.md` | `3d6fde03888c98f2cd5e7b711f24b4eb322331658d70a89c3fc73d60a6af5191` |
| `Representation/Families/RenardFamilyFlatnessProof.lean` | `bf858348aaf58a7f10052a8f8f8c49f1832d05f3f7f878a179bc8c3420691be9` |
| `Representation/Families/RenardFamilyFlatnessProof.md` | `d3690e566f1817caf318f1884b74d11e2a893fcb0d4d11bfd2782d5d9015a527` |
| `Representation/Families/RenardFamilyEndomorphismProof.lean` | `1ab1afa4e5cb00a9b6c37e1ae02a55f6a3966a3688ff992d644b880a70d1e155` |
| `Representation/Families/RenardFamilyEndomorphismProof.md` | `4838234c5b775acfc4516948fe9c9dab49120c5f32b3df20d28d4ce17770912e` |
| `Representation/Families/MatrixGenerationWitness.lean` | `6261b290ccb5b1c0132bd92923f29f73ffdcc55e300d91f2d19822d0d84e7928` |
| `Representation/Families/MatrixGenerationWitness.md` | `05883c38fa8e7d806ed15cffb5919913d2806ceb462a9059a3d58daf2990d9ab` |
| `Representation/Families/RenardCentralCharacterSplittingStatement.lean` | `40989be1e4a4a544f19e1d5bddbbec0b926955d214123255827b3acabf20e746` |
| `Representation/Families/RenardCentralCharacterSplittingStatement.md` | `2ed6d8564a3632792c3e382786ac92ffbb3b5f73bd0b20d477f919eaf70e9639` |
| `Representation/Families/RenardSupercuspidalFamilyEndomorphismStatement.lean` | `a6affd5a19ff17e0497299b7da66e29d9e1dd403636859373fedb936f1913bd4` |
| `Representation/Families/RenardSupercuspidalFamilyEndomorphismStatement.md` | `95213d3529150f9cb0bb6271a253479413f909d46e4996e205ba07f1fbb55f0c` |
| `Representation/Families/RenardUniversalFamilySpecializationStatement.lean` | `9aeb6b688a853df8059a192bb309b92bfd4456d6d3d65bc829cb09dc97fb0df5` |
| `Representation/Families/RenardUniversalFamilySpecializationStatement.md` | `0b83b2f6f91dab477e48ab05ce085a57fcde97853e510e8abe1e1d6a158097c5` |
| `Representation/Families/RenardFamilyAdmissibilityProof.lean` | `46d31383e016f5df17d505f01fb34098165b1e055651b03987a628348c0a9890` |
| `Representation/Families/RenardFamilyAdmissibilityProof.md` | `4c0038fc02367988d1b5afa170137059f8dce35563acbda6f25f020d056c314b` |
| `Representation/Families/RenardFamilySpecializationProof.lean` | `6f960d2c68eafca96785f0666f8f058fa8ce1ce9789a6663a8b226ce909d2414` |
| `Representation/Families/RenardFamilySpecializationProof.md` | `e64915469f9834520ce5af53836da849d5a66e1d2d5277f4d1ec2eb9f33c1370` |
| `Representation/Filtration/CentralCharacterSplitting.lean` | `ac84fe433c778a09455777308674154d9f674dc08c491e758182cdbe894a19ed` |
| `Representation/Filtration/CentralCharacterSplitting.md` | `ee7154663647c17094e07b96fd545135ab839d6bf01d37bf63eac641ee33611b` |
| `Representation/Families/InducedTwistsUniformDetectionStatement.lean` | `972c1634be818faeada61ebb0605070c9fe874e0d8af1e756e0f95282be2b648` |
| `Representation/Families/InducedTwistsUniformDetectionStatement.md` | `74f5eab0964c455d52d4802f432c3f2152ed7c34ba90221477dd23d0965e3dee` |
| `Representation/Families/InducedIrreducibilityOpenReduction.lean` | `a9e0ba398bbcac0d8678dd528b91b111fdac6092fafeb10946b90594bf72b041` |
| `Representation/Families/InducedIrreducibilityOpenReduction.md` | `92c51552b24dcc447c2fb435226809c2362308fab4fe778dd04a173c6e641299` |
| `Representation/Families/GlobalCompressionPrincipalOpen.lean` | `ea766f329817dc458809c46d935daa7c20505a1ea55bfd58a7e62ee674790c06` |
| `Representation/Families/GlobalCompressionPrincipalOpen.md` | `93eee3b6d30ec2e526354b0d570855daf1e5a02e0520a7f0c9e5447c1c2d51f7` |
| `Representation/Families/CompactCompressionPrincipalOpen.lean` | `9475768ef8c3a46fe1bfb1be47edb069076891f76adc0c0deda3170a1d40f67a` |
| `Representation/Families/CompactCompressionPrincipalOpen.md` | `045af66a7e8dd0b5b088c377072745db6fe0d22fbe9a3be54eeabefcece3ffd4` |
| `Representation/Families/CompactCompressionMatrices.lean` | `f29545bbbca89e3f83d2eaca6cb4d378e3109543a819280eb6b51e14ab8143cf` |
| `Representation/Families/CompactCompressionMatrices.md` | `5f2c769a95038dfa1cf0eb929ddc8a7ead175691469968f77513ba890d8983f8` |
| `Representation/Families/CompactCompressionSpecialization.lean` | `535338da51f477a0106ac3507d615c53a34e10612d45ff7812e19154265d559f` |
| `Representation/Families/CompactCompressionSpecialization.md` | `fea4466cf903ce1a51f63ca0d01002b9db7a31ecf3ef2e17ccd62875057c0057` |
| `Representation/Families/LocalizedMatrixPrincipalOpen.lean` | `7161defdf9d3bca17aa3e5b93304c6d970a6848c20564ef3763c728a3ba4bddd` |
| `Representation/Families/LocalizedMatrixPrincipalOpen.md` | `32aa49cb9bd67f5ae0b26802bc86e240a8689e566c7a9e780de09a11ee998583` |
| `Representation/Families/UnramifiedPolynomialWitness.lean` | `b3e81e420c6704f4c88d5bd70790ead0592dde5c952655ba5a94c73faae629ce` |
| `Representation/Families/UnramifiedPolynomialWitness.md` | `db1b1dda6cfa3b440c27ff3f604302141e39d43900deab153de1ae10affdfd86` |
| `Representation/Families/ActualLeviUnramifiedParameters.lean` | `a4bd6a01f43955e68375b52a59c28e5b2cef4cd547a1430116adbdb7e25974d1` |
| `Representation/Families/ActualLeviUnramifiedParameters.md` | `3b7a50ae51cbb32acf865e22e9b13ee173efc9b22d01bae2d052b26aaba3e353` |
| `Representation/Plancherel/UnramifiedNormalizedInducedSpecialization.lean` | `d675573b332c9e9743b2355cb59fd3881b68e3377a89930ae3cfaee490144a4d` |
| `Representation/Plancherel/UnramifiedNormalizedInducedSpecialization.md` | `2bc2d20ba17db92a3e98f25d3df200b2255b615ab69985fc1911fbbb26747739` |
| `Representation/Plancherel/RationalLeviFixedMatrices.lean` | `4f31c2f5fa15e6b708f3b0214d84d78723d8097ec5ba9dcbc2f6e72178b31dec` |
| `Representation/Plancherel/RationalLeviFixedMatrices.md` | `47a8c57e8555c619b269b37e922dd24a2ae787225357b3c49ee5afe7583a61f1` |
| `Representation/Plancherel/RationalLeviInductionOpennessStatement.lean` | `59b4598451b91ae02a3206d4bd78f5200a2155fffa90cfefa54aa284d5167ac6` |
| `Representation/Plancherel/RationalLeviInductionOpennessStatement.md` | `c291ef8791e03d98efaa5262673ffd49e592d8b887a2af098115159cad86b61c` |
| `Representation/Plancherel/UnramifiedUniformGenerationStatement.lean` | `34c70d3d8794b4a63cba25175b5b449e9ad0082684b2c4b52ebe050e372eaaed` |
| `Representation/Plancherel/UnramifiedUniformGenerationStatement.md` | `eb803c5470945a1700c1843f1a4910e0cd508cea803ef2748aeea6248f1235d1` |
| `Representation/Exponents/LeviNormalizerQuotientStatements.lean` | `2b8ff4cc0f8f94b0f06d70d37e5623997cef947ba7b15783a8096f57f8171c2b` |
| `Representation/Exponents/LeviNormalizerQuotientStatements.md` | `7edb7364628e4b45e30885c2b8b5b4d23ace6c8b3b28c56ff9f69f7cc211ecab` |
| `Representation/Exponents/DynamicLeviNormalizer.lean` | `0aae564346b57829df0cd1a0b6d742a511ef2968591c14da8ff638925f5c36ba` |
| `Representation/Exponents/DynamicLeviNormalizer.md` | `0b183e094e530285ae8ce1f241b0871ef91947bdae48534549f56f6267471966` |
| `Representation/Exponents/FiniteNormalizerRepresentatives.lean` | `6fa1363cee61eb889ddf283648f44e43e2fe269c4b4dd1ef59d8e0a3a063e82b` |
| `Representation/Exponents/FiniteNormalizerRepresentatives.md` | `63f42bf609386a6e6538bfb7dee0a4efb6a9ecc52c6f0814f80f7578d2114544` |
| `Representation/Exponents/LeviNormalizerBridge.lean` | `57f6681ab88b345c00cb22ad2cd18cc3e377fbb6e1f256f750dee1acb0d729af` |
| `Representation/Exponents/LeviNormalizerBridge.md` | `1b50d2ee40682d0578759061f95b97ac6001ee66a13edef6115990335a2fe516` |
| `Representation/Plancherel/SplitComponentNormRigidity.lean` | `1ed12178992a99aa29085adf24be84d88f7023710c7c33749de810e07abc4149` |
| `Representation/Plancherel/SplitComponentNormRigidity.md` | `42c97f6209f0df1f7f25d190a9680499a2acba0ddc0552a7c2ce436acd1cf9cd` |

## Scope

This note covers VI.8 only. The Theorem that ends VI.7, on PDF p.193, and
VI.9 are outside it. The unpublished assertions remain with the whole-book
parent task. This note declares no section, chapter or book completion.
