# Renard VI.8: algebraic families of representations

This note was written on 6 November 2026 against Library
`f73044d93e675a78ed75830ef026b3224514e510` and updated it on 7 November 2026
against Libraries `d82893a7de0b168873a15c6c7b0a731deb27aa23`,
`2816ea5d81e2fb9b0512bd1d8dec2ad7797026fd`,
`568f1cff4df2c51ba08b932716bf99235d0032c7`,
`c0c7eab6ed7a8f4f31468b6ad2abf14e21493127` and
`ddb0a9c0d562246b405e8f1149220107e7407d1d`. It maps every printed assertion
of VI.8, and the proof steps the source spells out, to the published Lean
declarations that state or prove them. Where no declaration does, the note
says so. It also records six source reading notes. The other
Chapter VI notes, such as the
[parabolic functors note](parabolic-functors-tempered-progress.md), are
separate, and this note does not change them.

Seventy-seven published modules carry the material or relate to it. They are
twenty-seven statement modules, sixteen proof modules and thirty-four definition
modules, listed under "Modules in the Library". The definition
`Langlands.Renard.AlgebraicFamily.leviInducedRepresentation` exists in two
versions; the second corrects the Markdown and leaves the Lean file unchanged.

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
pp.193–194 and VI.8.6 on pp.194–195. PDF pp.193–201 were read for this
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
  Their conjunction `Statements` is proved by
  `Langlands.Renard.AlgebraicFamily.statements` in
  [RenardFamilyStatementsAggregateProof](../../Langlands/Representation/Families/RenardFamilyStatementsAggregateProof.md),
  which combines the five published proofs.
- The VI.8.6 statement for a general family is in
  [RenardFamilyEndomorphismStatement](../../Langlands/Representation/Families/RenardFamilyEndomorphismStatement.md),
  with the same binders, and is proved. The VI.8.4 and VI.8.5 statements are in
  [RenardGenericIrreducibilityStatements](../../Langlands/Representation/Families/RenardGenericIrreducibilityStatements.md).
  They concern the published complex `leviInductionFunctor` of an actual
  rational parabolic. A Zariski principal open subset of `X(M)` is
  `Plancherel.rationalUnramifiedPrincipalOpen`, the nonvanishing locus of a
  polynomial in the published canonical coordinates. All three statements of
  that module are unproved. Row (P4) describes the published reduction of the
  VI.8.4 statement to three statements, two of them unproved.
- Three further statements are each in their own module: the VI.8.5 Lemma in
  [RenardCentralCharacterSplittingStatement](../../Langlands/Representation/Families/RenardCentralCharacterSplittingStatement.md),
  the VI.8.6 Example in
  [RenardSupercuspidalFamilyEndomorphismStatement](../../Langlands/Representation/Families/RenardSupercuspidalFamilyEndomorphismStatement.md)
  and the last claim of the VI.8.1 Example in
  [RenardUniversalFamilySpecializationStatement](../../Langlands/Representation/Families/RenardUniversalFamilySpecializationStatement.md).
  Rows (L5), (Ex6) and (Ex-c) describe them. The VI.8.5 Lemma and the VI.8.1
  Example claim are now proved (`centralCharacterSplitting`,
  `universalSpecialization`); the VI.8.6 Example is unproved: the Library derives it
  only from further hypotheses.
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
  of the module. The Markdown and an author qualification of the first
  version said instead that this unimodularity is not proved in
  the Library, which was wrong. The second version corrects both,
  and its Markdown is the Library's (see the qualifications below). No
  Library theorem combines the two results, and none identifies
  `leviInducedRepresentation` at `B = ℂ` with the published
  `leviInductionFunctor`.
- The statements on these constructions are in
  [RenardFamilyParabolicStatements](../../Langlands/Representation/Families/RenardFamilyParabolicStatements.md)
  (base change commutes with induction; Jacquet modules preserve finite
  generation) and
  [RenardFamilyParabolicFlatnessStatements](../../Langlands/Representation/Families/RenardFamilyParabolicFlatnessStatements.md)
  (flatness of induction and of Jacquet modules; induction preserves
  admissibility). They quantify over every nonarchimedean local field, every
  connected reductive group and every actual rational parabolic, including
  `P = G`, and over every reduced Noetherian `ℂ`-algebra `B` of finite type.
  All of them are now proved (`inductionBaseChange`, `jacquetFiniteType`,
  `inductionFlat`, `inductionAdmissible`, `jacquetFlat`).
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
proved, and so is the conjunction `Statements` of the first five. The category of `(G, B)`-modules is
defined, and so are base change, induction and Jacquet modules of families
as objects. Base change preserves smoothness and flatness, as row (BC)
records. The flatness, admissibility, base-change and finiteness statements
for induction and Jacquet modules, rows (I), (L2), (P2), (J) and (P3), are
now proved too (`inductionFlat`, `inductionAdmissible`, `inductionBaseChange`, `jacquetFlat`, `jacquetFiniteType`). No named specialization construction for a general family is
defined.

## Assertion map

| Assertion | Published declarations | Status |
| --- | --- | --- |
| (D) | `Langlands.Renard.AlgebraicFamily.FamilyModule`, `flatProperty`, `FamilyModule.of`, `FamilyModule.toSmoothRep`, `AdmissibleFamilyModule`, `admissibleProperty`, `AdmissibleFamilyModule.finite_fixedVectors` in [RenardFamilyCategory](../../Langlands/Representation/Families/RenardFamilyCategory.md) | Defined. `FamilyModule B G` is the full subcategory of `SmoothRep B G` on the objects whose carrier is flat over `B`, so its morphisms are all `B`-linear `G`-equivariant maps. `AdmissibleFamilyModule B G` is its full subcategory of objects whose fixed vectors under every open subgroup with compact carrier are finite over `B`. The definitions need only a commutative ring `B` and a topological group `G`, and impose none of Renard's standing hypotheses on `B`. No additive or abelian structure is defined. The statements of the other rows take `Representation B G V` with separate smoothness and flatness hypotheses, not objects of these categories |
| (P1) | `Langlands.Renard.AlgebraicFamily.AdmissibilityCriterionStatement` in [RenardFamilyStatements](../../Langlands/Representation/Families/RenardFamilyStatements.md), proof `admissibilityCriterion` in [RenardFamilyAdmissibilityProof](../../Langlands/Representation/Families/RenardFamilyAdmissibilityProof.md). Mathlib: `Module.finitePresentation_of_finite`, `Module.Flat.projective_of_finitePresentation`, instance `Module.Flat.of_projective` | Proved. For smooth `ρ`, `V` is flat with every compact-open `V^K` finite if and only if every compact-open `V^K` is finite and projective. In the forward direction, `flatness_iff_fixed_flat` of row (R1) makes each `V^K` flat; a finite module over the Noetherian `B` is finitely presented, and a flat finitely presented module is projective. In the converse, projective modules are flat, and `flatness_iff_fixed_flat` gives flatness of `V` |
| (P1-iso) | `FixedTensorComparisonStatement` (RenardFamilyStatements), proof `fixedTensorComparison` in [RenardFamilyFixedTensorProof](../../Langlands/Representation/Families/RenardFamilyFixedTensorProof.md); helpers `coefficientAverage`, `coefficientFixedProjection`, `coefficientFixedProjection_comp`, `trivialTensor_isSmooth`, `coefficientAverage_tensor`, `fixedTensorComparison_of_smooth` (same module); private helpers `fixedTensorMap_bijective` and `fixedCoefficientFiber_bijective` in [RationalNormalizedInducedSpecializationProof](../../Langlands/Representation/Plancherel/RationalNormalizedInducedSpecializationProof.md) | Proved. For smooth `ρ`, compact open `K` and every `B`-module `E`, the map `E ⊗[B] V^K → E ⊗[B] V` is injective and its range is `(E ⊗[B] V)^K`, with `G` acting through the second factor. The statement does not state the inverse. The proof restricts scalars along `ℂ → B` and uses the published finite-orbit averaging of `Langlands.Compact.CharZero`; naturality makes the average `B`-linear, and `coefficientFixedProjection` is a `B`-linear retraction of `V` onto `V^K`. Averaging on `E ⊗[B] V` acts as `id ⊗ e_K`, so tensoring the retraction gives the source's inverse `e ⊗ v ↦ e ⊗ e_K v`. `fixedTensorComparison_of_smooth` needs only a commutative `ℂ`-algebra `B`, smoothness and a compact open subgroup. The earlier private helpers prove the comparison for the universal family and `E = ℂ` through `evaluation r χ`, without a flatness premise |
| (R1) | `FlatnessCriterionStatement` (RenardFamilyStatements), proofs `flatnessCriterion` and `flatness_iff_fixed_flat` in [RenardFamilyFlatnessProof](../../Langlands/Representation/Families/RenardFamilyFlatnessProof.md); `flat_of_smooth_fixed_flat` in [UnramifiedRationalNormalizedInducedFinitenessProof](../../Langlands/Representation/Plancherel/UnramifiedRationalNormalizedInducedFinitenessProof.md) | Proved. `flatness_iff_fixed_flat` holds for every commutative `ℂ`-algebra `B` and locally profinite `G`: a smooth `V` is flat if and only if every compact-open `V^K` is. The forward direction applies `Module.Flat.of_retract` to the retraction `coefficientFixedProjection` of row (P1-iso). The reverse direction is the earlier `flat_of_smooth_fixed_flat`, which holds over any commutative ring for a locally compact nonarchimedean group and uses the equational criterion `Module.Flat.of_forall_isTrivialRelation`; the published `Langlands.Topology.LocallyProfiniteProof.vanDantzig` supplies the nonarchimedean structure |
| (Sp) | `evaluation`, `tensorEvaluation`, `inducedEvaluation`, `jacquetEvaluation`; `InducedSpecializationFiber`; `SpecializationAdmissibilityStatement` (RenardFamilyStatements) | Defined for the universal family, its induction and its Jacquet model. For a general family there is no named construction or functor: `SpecializationAdmissibilityStatement` writes the fiber inline as `ℂ ⊗[B] V`, with `B` acting on `ℂ` through `χ : B →ₐ[ℂ] ℂ` and `g` acting by `Module.End.baseChangeHom B ℂ V (ρ g)`. Related: the predicate `Langlands.Renard.AlgebraicFamily.CompactCompressionPrincipalOpen.IsFullSpecialization S A χ D`, in [CompactCompressionPrincipalOpen](../../Langlands/Representation/Families/CompactCompressionPrincipalOpen.md), says that some intertwiner from a smooth representation `A` with `S`-coefficients to a smooth representation `D`, compatible with `χ : S →ₐ[ℂ] ℂ`, has bijective scalar extension `ℂ ⊗[S] A → D`, so that `D` is the fiber of `A` at `χ` up to isomorphism. It is a helper for row (P4) |
| (L1) | `SpecializationAdmissibilityStatement` (RenardFamilyStatements), proof `specializationAdmissibility` in [RenardFamilySpecializationProof](../../Langlands/Representation/Families/RenardFamilySpecializationProof.md) | Proved. For smooth flat `ρ` with every compact-open `V^K` finite, and every `χ`, the fiber `ℂ ⊗[B] V` is `Langlands.IsAdmissible`. Its tensor factors are in the opposite order to the source's `V ⊗_B B/I_χ`. The proof shows that scalar extension preserves smoothness (`baseChange_isSmooth`, row (BC)), and that `ℂ ⊗[B] V^K` maps onto the `K`-fixed vectors of the fiber by the fixed-tensor comparison of row (P1-iso), so these are finite-dimensional. Every open subgroup contains a compact open one (Van Dantzig), which gives the all-open-subgroups condition of `IsAdmissible`. The proof does not use the flatness hypothesis, which the statement keeps |
| (Ex-a) | `universalRepresentation`, `isSmooth_universalRepresentation` (Models); `universalTensorFlatness` in [RationalUniversalTensorFinitenessProof](../../Langlands/Representation/Plancherel/RationalUniversalTensorFinitenessProof.md) | Defined; smoothness proved. Flatness of `B ⊗[ℂ] E` is proved with no admissibility hypothesis |
| (Ex-b) | `RationalUniversalTensorFinitenessStatement` in [RationalUniversalTensorFinitenessStatement](../../Langlands/Representation/Plancherel/RationalUniversalTensorFinitenessStatement.md); proof `rationalUniversalTensorFiniteness`; `universalTensorFixedComparison`, `universalTensorFiniteness`; `Langlands.Plancherel.universalTensorFixedInclusion_bijective`, `Langlands.Plancherel.universalTensorFixed_finite_projective` | Proved. For `σ` admissible, `B ⊗[ℂ] E` is flat, and for every compact open `J` there is an equivalence between the `J`-fixed vectors of `universalRepresentation` and `B ⊗ σ^J` whose inverse is the canonical inclusion `tensorFixedInclusion`; the fixed space is finite and projective. The comparison needs no admissibility; finiteness uses `IsAdmissible σ`. `tensorFixedEquiv`, in the c957a9bb proof module, is a variant over a field `k` for any group. Admissibility of `V_B` itself is also proved: `universalRepresentation_isAdmissible`, in [UnramifiedRationalConjugateAdmissibility](../../Langlands/Representation/Plancherel/UnramifiedRationalConjugateAdmissibility.md), says that `universalRepresentation r σ` is `IsAdmissible` over `RegularAlgebra r` when `σ` is. Its generic form `Langlands.Plancherel.isAdmissible_universalUnramifiedRepresentation` holds for a locally compact nonarchimedean group, continuous `ν` and Noetherian `unramifiedRegularFunctions ν` |
| (Ex-c) | `Langlands.Renard.AlgebraicFamily.UniversalSpecializationStatement` in [RenardUniversalFamilySpecializationStatement](../../Langlands/Representation/Families/RenardUniversalFamilySpecializationStatement.md); `tensorEvaluation`, `tensorEvaluation_inducing_action` (Specialization) | Stated; now proved, as `universalSpecialization` (`Langlands/Representation/Families/RenardUniversalFamilySpecializationProof.lean`). For every group `G` with a topology, every family `ν : I → (G →* ℝ≥0ˣ)`, every complex representation `π` on `V`, not assumed smooth, and every `χ` in `Plancherel.unramifiedCharacters ν`, the statement asserts a `ℂ`-linear equivalence `e : ℂ ⊗[B] (B ⊗[ℂ] V) ≃ V`, with `B = Plancherel.unramifiedRegularFunctions ν` acting on `ℂ` through evaluation at `χ`. It intertwines `baseChange ℂ` of `Plancherel.universalUnramifiedRepresentation ν π` with the twist `π ⊗ χ`, and `e (c ⊗ (b ⊗ v)) = (c · b(χ)) v`. Only the last claim of the Example is stated, in the generality its author qualifications record. For the universal family of an actual Levi, the map to `π ⊗ χ` is the published `tensorEvaluation`, with its equivariance proved; the Specialization Markdown makes no fiber claim. (C2) below proves the induced form |
| (I) | `Langlands.Renard.AlgebraicFamily.LeviInduced`, `leviInducedRepresentation`, `Induced`, `inducedRepresentation`, `isSmooth_inducedRepresentation`, `induced_covariant_levi_unipotent` in [RenardFamilyParabolicFunctors](../../Langlands/Representation/Families/RenardFamilyParabolicFunctors.md); `InductionFlatStatement` in [RenardFamilyParabolicFlatnessStatements](../../Langlands/Representation/Families/RenardFamilyParabolicFlatnessStatements.md); `Induced`, `inducedRepresentation` (Models); `Langlands.Plancherel.UnramifiedNormalized.normalizedInductionFunctor` in [UnramifiedNormalizedModels](../../Langlands/Representation/Plancherel/UnramifiedNormalizedModels.md); `universalInduced_flat` (c957a9bb proof module) | Over a general `B` the induced family is defined as an object and is smooth, with Renard's covariance (VI.1.2.3) proved; the functor on morphisms is not bundled. Its flatness is stated: `InductionFlatStatement` says that for smooth `σ` on a flat `B`-module `E`, `LeviInduced … σ` is flat over `B`; proved, as `inductionFlat` (`Langlands/Representation/Families/RenardFamilyParabolicFlatnessProof.lean`). Over any `unramifiedRegularFunctions ν`, `normalizedInductionFunctor` is normalized induction on smooth representations. Flatness of the induced family is proved for the universal family only |
| (VI.8.2.1) | `Langlands.Induction.fixedEvaluationEquiv`, `Langlands.Induction.exists_finset_doubleCoset_representatives` in [FixedVectorModel](../../Langlands/Representation/Induction/FixedVectorModel.md) | Proved for unnormalized `smoothInduced P σ` over any commutative coefficient ring: for a finite set `t` of double-coset representatives, the `K`-fixed vectors are equivalent to `∏ i : t, fixedVectors σ (conjOpenSubgroup P K i)`. The subgroups are literal open subgroups of `P`, and the finite product plays the role of the direct sum |
| (L2) | `InductionAdmissibleStatement` (RenardFamilyParabolicFlatnessStatements); `Langlands.Induction.smoothInduced_isAdmissible_of_compactSpace` in [CompactQuotientProof](../../Langlands/Representation/Induction/CompactQuotientProof.md); `UniversalInducedCoefficientFinitenessStatement` in [UnramifiedRationalNormalizedInducedFiniteness](../../Langlands/Representation/Plancherel/UnramifiedRationalNormalizedInducedFiniteness.md), proof `universalInducedCoefficientFiniteness`; `universalInducing_fixed_finite_free`, `universalInduced_fixed_finite_free`; `Langlands.Plancherel.UnramifiedNormalized.isAdmissible_inducedRepresentation` (UnramifiedRationalConjugateAdmissibility) | For a general `B`, stated: `InductionAdmissibleStatement` says that for smooth `σ` on a flat `E` whose fixed vectors under every compact open subgroup of `M(F)` are finite over `B`, the fixed vectors of `leviInducedRepresentation … σ` under every compact open subgroup of `G(F)` are finite over `B`; flatness, the rest of admissibility, is row (I). Now proved, as `inductionAdmissible` (`Langlands/Representation/Families/RenardFamilyParabolicFlatnessProof.lean`); before that, proved in three special forms. The first: unnormalized smooth induction from any subgroup `P` with compact `P\G` preserves `IsAdmissible` over any Noetherian ring. The second: for `π` admissible, the universal normalized induced family is flat and its compact-open fixed spaces are finite and projective. The proof shows they are finite free. The third: over a Noetherian `unramifiedRegularFunctions ν`, normalized induction of any admissible representation is admissible. It assumes a locally compact nonarchimedean group `H`, a semidirect decomposition `d` of a subgroup `Q` with closed normal factor `V` and continuous projection `d.projection`, and compact `Q\H` |
| (BC) | `Langlands.Renard.AlgebraicFamily.baseChange`, `baseChange_tmul` (RenardFamilyParabolicFunctors); `Langlands.Renard.AlgebraicFamily.baseChange_isSmooth`, `baseChange_fixed_finite` (RenardFamilySpecializationProof). Mathlib: instance `Module.Flat.baseChange` | Defined on objects: for a commutative `B`-algebra `C`, `baseChange C ρ` acts on `C ⊗[B] V` by `1 ⊗ ρ(g)`, with the scalars on the left. Preservation of smoothness is proved, as a step of row (L1). `baseChange_isSmooth` holds for every commutative ring `B`, commutative `B`-algebra `A`, group `G` with a topology and smooth `ρ`. Its conclusion is smoothness of `(Module.End.baseChangeHom B A V).toMonoidHom.comp ρ`, which is `baseChange A ρ` by definition, although the theorem does not use that name. Preservation of flatness is Mathlib's instance `Module.Flat.baseChange`: `C ⊗[B] V` is flat over `C` when `V` is flat over `B`. In the same proof module, `baseChange_fixed_finite` assumes a commutative `ℂ`-algebra `B`, a topological group `G`, smooth `ρ` and a compact open `K` with `V^K` finite over `B`. It concludes that the `K`-fixed vectors of the scalar extension are finite over `A`. No theorem states that `baseChange` sends objects of `FamilyModule B G` to objects of `FamilyModule C G`, and the functor on morphisms is not bundled |
| (P2) | `InductionBaseChangeStatement` in [RenardFamilyParabolicStatements](../../Langlands/Representation/Families/RenardFamilyParabolicStatements.md); `Langlands.Plancherel.scalarExtensionOfSemilinear` (Statement module) | Stated; now proved, as `inductionBaseChange` (`Langlands/Representation/Families/RenardFamilyInductionBaseChangeProof.lean`). For `C` with `[CommRing C] [Algebra ℂ C] [IsNoetherianRing C] [IsReduced C] [Algebra B C] [IsScalarTower ℂ B C]`, not assumed of finite type, and smooth `σ` on a flat `B`-module `E`, there is a `C`-linear equivalence `C ⊗[B] LeviInduced … σ ≃ LeviInduced … (baseChange C σ)` intertwining the two actions of `G(F)`. The scalar tower is the reading of "`C` soit un `B`-module", recorded in the statement's Markdown; see reading note 2. Naturality in `E` is not stated |
| (VI.8.2.2) | `InductionBaseChangeStatement` (RenardFamilyParabolicStatements); `inducedScalarExtension`, `inducedScalarExtension_tmul` | For a general `B`, part of `InductionBaseChangeStatement`, now proved (`inductionBaseChange`): its equivalence `e` satisfies `Induction.eval _ _ (e (c ⊗ₜ f)) g = c ⊗ₜ Induction.eval _ _ f g`, which determines `e`. For the universal family, defined for `C = ℂ` through `evaluation r χ`, with the pure-tensor formula proved |
| (C2) | `RationalNormalizedInducedSpecializationStatement`; proof `rationalNormalizedInducedSpecialization`; `Langlands.Plancherel.UnramifiedNormalized.inducedSpecializationEquiv`, `inducedSpecializationEquiv_tmul` in [UnramifiedNormalizedInducedSpecialization](../../Langlands/Representation/Plancherel/UnramifiedNormalizedInducedSpecialization.md) | Proved for the universal normalized induced family: for every smooth `π` and every unramified character `χ`, `inducedScalarExtension r h hU π χ` is bijective. No admissibility is assumed. This combines (C2) with (Ex-c). The definition `Langlands.Plancherel.UnramifiedNormalized.inducedSpecializationEquiv` extracts the group-generic part of that proof. For a locally compact nonarchimedean group `G`, a closed subgroup `P = M ⋉ U` with `U` closed, continuous projection to `M` and compact `P\G`, any family `ν` of continuous positive characters of `M` and any complex representation of `M`, `inducedSpecializationEquiv` is the `ℂ`-linear equivalence from the fiber at `χ` of the universal normalized induced module over `unramifiedRegularFunctions ν` to the complex normalized induction of the twist by `χ`, with `z ⊗ f ↦ z • inducedEvaluation f`. No root presentation is used |
| (J) | `Langlands.Renard.AlgebraicFamily.Jacquet`, `jacquetRepresentation`, `leviJacquetRepresentation`, `isSmooth_jacquetRepresentation` (RenardFamilyParabolicFunctors); `JacquetFlatStatement` (RenardFamilyParabolicFlatnessStatements); `Jacquet`, `jacquetRepresentation` (Models); `Langlands.Plancherel.UnramifiedNormalized.normalizedJacquetFunctor` (UnramifiedNormalizedModels); `jacquetEvaluation` (Specialization) | Over a general `B` the normalized Jacquet module is defined as an object, the `U`-coinvariants with `M` acting through `c_U^{-1/2}`, and preserves smoothness. Its flatness is stated: `JacquetFlatStatement` says that for smooth `ρ` on a flat `B`-module `V`, `Jacquet ρ (pointImage (r ≫ p))` is flat over `B`. It has no Levi binders, since the `B`-module `V_N` does not depend on the Levi or the normalization. The flatness statement `JacquetFlatStatement` is proved, as `jacquetFlat` (`Langlands/Representation/Families/RenardFamilyParabolicFlatnessProof.lean`). Over any `unramifiedRegularFunctions ν`, `normalizedJacquetFunctor` is the normalized Jacquet functor on smooth representations, and the specialization map is defined for the universal family only |
| (P3) | `JacquetFiniteTypeStatement` (RenardFamilyParabolicStatements); related: `Langlands.Plancherel.RationalSupercuspidalJacquetFamilyFiniteStatement` in [UnramifiedRationalJacquetFinitenessStatement](../../Langlands/Representation/Plancherel/UnramifiedRationalJacquetFinitenessStatement.md) | Stated; now proved, as `jacquetFiniteType` (`Langlands/Representation/Families/RenardFamilyJacquetFiniteTypeProof.lean`). For smooth `ρ` on a flat `B`-module `V` with `ρ.asModule` finite over `MonoidAlgebra B (rationalPoints G)`, the module `(leviJacquetRepresentation … ρ).asModule` is finite over `MonoidAlgebra B (rationalPoints M)`. This is the reading of "`B`-modules de type fini", recorded in the statement's Markdown; see reading note 3. The conjunction of (P2) and (P3) is `ParabolicStatements`. Related, not the Proposition: for the universal supercuspidal family, finiteness of the Jacquet module is the separate target `RationalSupercuspidalJacquetFamilyFiniteStatement`, now proved (`Langlands.Plancherel.rationalSupercuspidalJacquetFamilyFinite`); see the [uniform compression note](uniform-compression-progress.md) |
| (T4) | `LocalFreeCoverStatement` (RenardFamilyStatements), proof `localFreeCover` in [RenardLocalFreeCoverProof](../../Langlands/Representation/Families/RenardLocalFreeCoverProof.md). Mathlib: `Module.free_of_flat_of_isLocalRing`, `Module.FinitePresentation.exists_free_localizedModule_powers`, `Module.Finite.of_localizationSpan`, `Module.freeLocus_eq_univ_iff`, `Module.basicOpen_subset_freeLocus_iff` | Proved. For `B` as in VI.8 and a `B`-module `M`: `M` is finite and projective if and only if there are `f : Fin r → B` generating the unit ideal such that each localization `LocalizedModule (Submonoid.powers (f i)) M` is finite and free over `Localization.Away (f i)`. The proof uses only Mathlib, not Bourbaki's text. For the forward direction, the set of `t` with finite free localization at `t` spans the unit ideal: otherwise it lies in a maximal ideal `m`, the localization at `m` is free over the local ring, and finite presentation gives such a `t` outside `m`. A finite subset then gives the cover. For the converse, the cover makes `M` finite, `IsNoetherianRing B` makes it finitely presented, and every prime lies in a basic open set of the cover, which is in the free locus. Of the hypotheses on `B` beyond `CommRing`, only `IsNoetherianRing B` is used |
| (Sp-φ) | none | Not stated |
| (P4) | `Langlands.Renard.AlgebraicFamily.InducedIrreducibilityOpenStatement` in [RenardGenericIrreducibilityStatements](../../Langlands/Representation/Families/RenardGenericIrreducibilityStatements.md). Related: `Langlands.Plancherel.FiniteMatrixIrreducibilityOpennessStatement` in [FiniteMatrixOpennessStatement](../../Langlands/Representation/Plancherel/FiniteMatrixOpennessStatement.md), proved by `Langlands.Plancherel.finiteMatrixIrreducibilityOpenness` in [FiniteMatrixOpennessProof](../../Langlands/Representation/Plancherel/FiniteMatrixOpennessProof.md); `Langlands.Plancherel.CompactFixedFamilyOpennessStatement` in [CompactFixedFamilyOpennessStatement](../../Langlands/Representation/Plancherel/CompactFixedFamilyOpennessStatement.md), proved by `Langlands.Plancherel.compactFixedFamilyOpenness` in [CompactFixedFamilyOpennessProof](../../Langlands/Representation/Plancherel/CompactFixedFamilyOpennessProof.md); `Langlands.Renard.AlgebraicFamily.MatrixGenerationWitness.wordDeterminant`, `specialize_wordDeterminant`, `exists_principal_neighborhood` in [MatrixGenerationWitness](../../Langlands/Representation/Families/MatrixGenerationWitness.md) | Stated, unproved: the Library derives it only from further hypotheses, by `inducedIrreducibilityOpen_of_statements`. For an actual rational parabolic of a connected reductive group, an irreducible smooth `ρ` of the Levi points and an unramified character `ψ₀` with `i_P^G(ρ ⊗ ψ₀)` irreducible, the statement asserts a polynomial `f` in the published canonical coordinates of `X(M)` whose principal open set contains `ψ₀` and on which every `i_P^G(ρ ⊗ ψ)` is irreducible. Here `i_P^G` is the published `leviInductionFunctor`. That the open set contains `ψ₀`, which the source proof provides, is a reading recorded in the statement's Markdown. Related, not the Proposition: the statement `FiniteMatrixIrreducibilityOpennessStatement` concerns, for `x` in a topological space, a family of complex square matrices `A x j` on a finite coordinate space, indexed by `j` in any type, with every entry continuous in `x`. It asserts that the set of `x` at which the matrices `A x j` have no common invariant subspace other than zero and the whole space is open. It concerns finite matrices and openness in a given topology, not Zariski openness in `X(M)` or irreducibility of `π_ψ`. It is proved through the openness of generation of the full matrix algebra, `Langlands.Plancherel.FiniteMatrixOpenness.isOpen_adjoin_eq_top`, and Burnside's theorem `Langlands.SandwichDimensionBound.action_surjective`; the source argues through Burnside's theorem and a determinant. `CompactFixedFamilyOpennessStatement`, proved by `compactFixedFamilyOpenness`, transfers this to smooth representations. For a family `A x` of nontrivial smooth complex representations, indexed by a topological space, it takes one compact open `K` such that every irreducible subquotient of every `A x` has a nonzero `K`-fixed vector, bases of the `K`-fixed spaces indexed by one finite type, and continuous entries of the matrices `UnitarizabilityContinuation.fixedMatrix`. It asserts that the set of `x` with `A x` irreducible is open. It again concerns openness in a given topology, and it supplies neither the subgroup `K`, nor the bases, nor an irreducible `π_{ψ_0}`. The definition `Langlands.Renard.AlgebraicFamily.MatrixGenerationWitness.wordDeterminant` implements the determinant step algebraically, over any commutative `ℂ`-algebra `B`. For a family of square matrices `A j` over `B` whose specialization at `χ₀ : B →ₐ[ℂ] ℂ` is irreducible in the sense of `Langlands.UnitarizabilityContinuation.IsIrreducibleFamily`, `exists_principal_neighborhood` gives `f : B` with `χ₀ f = 1` such that the specialization at every `χ` with `χ f ≠ 0` is irreducible. The witness `f` is the determinant `wordDeterminant` of words in a free algebra, which replace the source's Hecke operators. Its Markdown records that it supplies neither a detecting compact open subgroup for induced unramified twists, nor a coefficient matrix model of their fixed vectors, nor the conversion from a regular function to a polynomial in the canonical coordinates, and that it does not prove `InducedIrreducibilityOpenStatement`. Since Library `c0c7eab6`, further helpers are published. The unproved statement `Langlands.Renard.AlgebraicFamily.InducedTwistsUniformDetectionStatement` (`Langlands.Renard.AlgebraicFamily.InducedTwistsUniformDetectionStatement`), in [InducedTwistsUniformDetectionStatement](../../Langlands/Representation/Families/InducedTwistsUniformDetectionStatement.md), extracts a step of the source proof. With the binders of `InducedIrreducibilityOpenStatement`, it asserts one compact open `K` of `G(k)` such that every irreducible subquotient of every `leviInductionFunctor` of `ρ ⊗ ψ`, for every unramified `ψ`, has a nonzero `K`-fixed vector. The source's paragraph proves more: one `K` detects the whole inertial support. In [InducedIrreducibilityOpenReduction](../../Langlands/Representation/Families/InducedIrreducibilityOpenReduction.md), `exists_principal_neighborhood_of_detection` derives the conclusion of `InducedIrreducibilityOpenStatement` for `ρ` and `ψ₀` from that statement and a family `A` with `IsGlobalCoefficientFamily A M e D`, defined in [GlobalCompressionPrincipalOpen](../../Langlands/Representation/Families/GlobalCompressionPrincipalOpen.md). There `e` identifies `B` with the regular functions on `X(M)`, every compact-open fixed space of `A` is free and finite over `B`, and `A` specializes fully, in the sense of `IsFullSpecialization`, to `D ψ = i_P^G(ρ ⊗ ψ)` at every `ψ`. Since Library `ddb0a9c0`, such a family is constructed and the reduction is assembled. The definition `Langlands.Renard.AlgebraicFamily.ActualLevi.universalFamily` works in namespace `Langlands.Renard.AlgebraicFamily.ActualLevi`, in [ActualLeviUnramifiedInducedFamily](../../Langlands/Representation/Families/ActualLeviUnramifiedInducedFamily.md). Over `coefficientAlgebra`, the regular functions on the transported unramified parameters, `universalFamily` is the published universal normalized induction on the literal Levi image, applied to `ρ` pulled back along the Levi-point equivalence, with its action restricted to complex scalars. `fiber` at `ψ` is the published `leviInductionFunctor` of `ρ` twisted by `ψ`. `universalFamily_fixed_finite_free` makes every compact-open fixed space finite and free over the coefficients when `ρ` is admissible and the quotient by the parabolic is compact. `universalFamily_specialization` gives, under compactness of the quotient alone, an intertwiner `specializationEvaluation` to `fiber` with bijective scalar extension. Its Markdown cites the base-change step of VI.8.2, PDF pp.196–197. The definition `Langlands.Renard.AlgebraicFamily.InducedIrreducibilityOpenAssembly.Inputs` is in [InducedIrreducibilityOpenAssembly](../../Langlands/Representation/Families/InducedIrreducibilityOpenAssembly.md), namespace `Langlands.Renard.AlgebraicFamily.InducedIrreducibilityOpenAssembly`. `universalFamily_isGlobalCoefficientFamily` shows that this family is a global coefficient family for admissible `ρ` and compact quotient, through `ActualLevi.regularAlgebraEquiv` and `isFullSpecialization_of_toRingHom_eq`. `inducedIrreducibilityOpen_of_statements` derives `InducedIrreducibilityOpenStatement` from three statements: `Langlands.Aubert.General.RationalPointsIrreducibleAdmissibleStatement`, Jacquet's theorem that irreducible smooth representations are admissible (VI.2.2); `Langlands.Aubert.General.RepresentedParabolic.ArbitraryParabolicQuotientCompactStatement`, compactness of the quotient by every parabolic (V.5.1); and `InducedTwistsUniformDetectionStatement`. The structure `Inputs` packages the three, and `inducedIrreducibilityOpen_of_inputs` applies the theorem to it. Of the three, the Library now proves the second (`arbitraryParabolicQuotientCompact`); the other two have no unconditional proof. The published `rationalPointsIrreducibleAdmissible_of_jacquetCartanDatum` assumes `RationalPointsJacquetCartanDatumStatement`, which `rationalPointsJacquetCartanDatum_of` derives from `JointSpecialCompactBasisExistenceStatement`, `StandardCocharacterStatement` and `StandardParabolicOrderStatement` (the last two now proved, by `standardCocharacter` and `standardParabolicOrder`; the first unproved), and no Library theorem proves `InducedTwistsUniformDetectionStatement` without hypotheses. So `InducedIrreducibilityOpenStatement` remains unproved. The supporting definitions are as follows. `Langlands.Renard.AlgebraicFamily.CompactCompressionMatrices.fixedMatrix` and `Langlands.Renard.AlgebraicFamily.CompactCompressionMatrices.coefficientMatrix` give the matrices `CompactCompressionMatrices.fixedMatrix` and `coefficientMatrix` of the compact average on a fixed-vector basis, in [CompactCompressionMatrices](../../Langlands/Representation/Families/CompactCompressionMatrices.md) and [CompactCompressionSpecialization](../../Langlands/Representation/Families/CompactCompressionSpecialization.md). `isIrreducible_iff_fixedMatrix` says that a nontrivial representation whose irreducible subquotients are all detected by `K` is irreducible exactly when its matrix family is, and `fixedMatrix_specializedBasis` says that the matrices of a fiber are the evaluated coefficient matrices. `Langlands.Renard.AlgebraicFamily.LocalizedMatrixPrincipalOpen.regularWitness` and `Langlands.Renard.AlgebraicFamily.UnramifiedPolynomialWitness.rationalRegularPolynomial` give `LocalizedMatrixPrincipalOpen.exists_polynomial_principal_neighborhood` in [LocalizedMatrixPrincipalOpen](../../Langlands/Representation/Families/LocalizedMatrixPrincipalOpen.md) and `UnramifiedPolynomialWitness.rationalRegularPolynomial` in [UnramifiedPolynomialWitness](../../Langlands/Representation/Families/UnramifiedPolynomialWitness.md). They turn the determinant witness of `Langlands.Renard.AlgebraicFamily.MatrixGenerationWitness.wordDeterminant`, after one localization, into a polynomial in the canonical coordinates whose principal open set is its nonvanishing locus. `Langlands.Renard.AlgebraicFamily.CompactCompressionPrincipalOpen.IsFullSpecialization` and `Langlands.Renard.AlgebraicFamily.CompactCompressionPrincipalOpen.IsGlobalCoefficientFamily` give `IsFullSpecialization`, the localized assembly `CompactCompressionPrincipalOpen.exists_polynomial_principal_neighborhood`, the global assembly and the reduction above. `Langlands.Renard.AlgebraicFamily.ActualLevi.parameterEquiv` gives `ActualLevi.parameterEquiv` and `regularAlgebraEquiv` in [ActualLeviUnramifiedParameters](../../Langlands/Representation/Families/ActualLeviUnramifiedParameters.md), which transport unramified characters and regular functions along the Levi point equivalence. `Langlands.Plancherel.UnramifiedNormalized.inducedSpecializationEquiv` is described in row (C2). The three statements `Langlands.Plancherel.RationalLeviInductionOpennessStatement`, `Langlands.Plancherel.UnramifiedUniformGenerationStatement` and `Langlands.Plancherel.RationalNormalized.inducedLeviNormalizationEquiv` below come from the work on the proof of (T5). The unproved `Langlands.Plancherel.RationalLeviInductionOpennessStatement` (`Langlands.Plancherel.RationalLeviInductionOpennessStatement`), in [RationalLeviInductionOpennessStatement](../../Langlands/Representation/Plancherel/RationalLeviInductionOpennessStatement.md), concerns an admissible nonzero smooth inducing representation and one given compact open subgroup detecting every irreducible subquotient of every fiber. It asserts that the irreducible locus of `UnramifiedLeviInduction` is open in the continuous-character topology, not that it is Zariski open, and it keeps compactness of the quotient by the parabolic as a hypothesis. The unproved `Langlands.Plancherel.UnramifiedUniformGenerationStatement` (`Langlands.Plancherel.UnramifiedUniformGenerationStatement`), in [UnramifiedUniformGenerationStatement](../../Langlands/Representation/Plancherel/UnramifiedUniformGenerationStatement.md), asserts one compact open subgroup whose fixed vectors generate every fiber, for a finite-length inducing representation, given an opposite Iwahori contraction basis and `G = PK`; generation is not detection of subquotients. The definition `Langlands.Plancherel.RationalNormalized.inducedLeviNormalizationEquiv`, `RationalNormalized.inducedLeviNormalizationEquiv` in [RationalLeviFixedMatrices](../../Langlands/Representation/Plancherel/RationalLeviFixedMatrices.md), identifies each fiber normalized on all of `P` (`complexInduced`) with `UnramifiedLeviInduction`, normalized on the Levi, and transports fixed bases and their matrices; radical unimodularity comes from the published `parabolicRadical_isUnimodular` |
| (T5) | `Langlands.Renard.AlgebraicFamily.GenericInducedIrreducibilityStatement` (RenardGenericIrreducibilityStatements). Related: `Langlands.Plancherel.ConditionalParabolicGenericIrreducibilityStatement` in [ParabolicGenericIrreducibilityStatement](../../Langlands/Representation/Plancherel/ParabolicGenericIrreducibilityStatement.md) | Stated, unproved: the Library derives it only from further hypotheses, by `genericInducedIrreducibility_of_statements`. For an irreducible supercuspidal `ρ`, the statement asserts a nonzero polynomial `f` in the same coordinates such that every `i_P^G(ρ ⊗ ψ)` with `ψ` in its principal open set is irreducible. The statement's Markdown explains why a nonzero `f` gives a nonempty Zariski open set. The conjunction of (P4) and (T5) is `GenericIrreducibilityStatements`. Related, not the Theorem: the statement `ConditionalParabolicGenericIrreducibilityStatement`, now proved (`conditionalParabolicGenericIrreducibility`), is adapted from Waldspurger 2003, Proposition IV.2.2(i) and the beginning of IV.3, not from Renard. For an irreducible smooth representation `π` of the Levi points that is square-integrable modulo the image `C` of the split component, it asserts a nonempty set `D` of unramified characters, open in the continuous-character topology, on which the induction `UnramifiedLeviInduction` of `π` twisted by `χ` is irreducible. Its hypothesis is square integrability, not supercuspidality, and its locus is open in that topology, not Zariski open. It does not by itself give a Zariski-open locus, and no Library declaration connects it to (T5). Since Library `ddb0a9c0`, that statement is reduced to (P4). The module of the statement `Langlands.Plancherel.ParabolicGenericIrreducibilityReductionStatement` defines `Langlands.Plancherel.ParabolicGenericIrreducibilityReductionStatement` in [ParabolicGenericIrreducibilityReduction](../../Langlands/Representation/Plancherel/ParabolicGenericIrreducibilityReduction.md), and `conditionalParabolicGenericIrreducibility_of_statements` there proves it: `UnitaryRegularParabolicIrreducibilityStatement`, of row (T5-c), and the (P4) statement `InducedIrreducibilityOpenStatement` imply `ConditionalParabolicGenericIrreducibilityStatement`. The proof takes a regular unitary twist by `exists_unitary_twist_isNormalizerRegular` of row (T5-b), makes the induction irreducible there, and applies (P4). `Langlands.Plancherel.representedInductionLeviEquiv`, in [RepresentedInductionComparison](../../Langlands/Representation/Plancherel/RepresentedInductionComparison.md) (`Langlands.Plancherel.representedInductionLeviEquiv`), identifies the literal `UnramifiedLeviInduction` with the `leviInductionFunctor` of an intrinsic twist, and the principal open set is pulled back to an open set of unramified characters. In ParabolicGenericIrreducibilityReduction, `ParabolicGenericIrreducibilityStructuralReductionStatement`, proved by `conditionalParabolicGenericIrreducibility_of_structuralStatements`, derives the same target from eight statements: `RepresentedGeometricLemmaStatement`, `TemperedSquareIntegrableUnitaryPartStatement`, `ArbitraryParabolicQuotientCompactStatement`, `SquareIntegrableNormalizedTemperedStatement`, `ArbitraryParabolicJacquetAdmissibilityStatement`, `RationalReductiveUnimodularityStatement`, `StandardCocharacterStatement` and `InducedIrreducibilityOpenStatement`. Of the eight, the Library now proves all but `TemperedSquareIntegrableUnitaryPartStatement` and `InducedIrreducibilityOpenStatement`; the target itself is proved, by `conditionalParabolicGenericIrreducibility`. Neither reduction concerns `GenericInducedIrreducibilityStatement` |
| (T5-a) | `Langlands.Aubert.General.RepresentedParabolic.exists_positive_unramifiedCharacter_norm_mul_eq_one`, `twistUnitaryCentralCharacter`, `exists_positive_unramifiedTwist_unitaryCentralCharacter` in [PositiveUnramifiedCentralTwist](../../Langlands/Representation/Exponents/PositiveUnramifiedCentralTwist.md) | Proved for a connected reductive group: an irreducible smooth representation has a positive unramified twist with unitary central character. The module was published with the VII.1.3 proof `maximalLeviSupercuspidalReducibilityFromInputs`, which uses it. See reading note 5. The second claim, that a supercuspidal representation with unitary central character is unitary, is stated, unproved, as `Langlands.Aubert.General.RepresentedParabolic.SupercuspidalUnitaryCentralCharacterUnitarizableStatement` in [MaximalLeviReducibilityUnitaryInputs](../../Langlands/Representation/Exponents/MaximalLeviReducibilityUnitaryInputs.md). It covers every connected reductive group, with supercuspidality as vanishing of the normalized Jacquet modules of all proper parabolics. The source's route through VI.2.1 and IV.3.2 is split as follows. `SupercuspidalUnitaryCoefficientCompactSupportStatement`, in [SupercuspidalCoefficientCompactSupportStatement](../../Langlands/Representation/Exponents/SupercuspidalCoefficientCompactSupportStatement.md), states VI.2.1 (a) ⇒ (b) for these representations, when irreducible: for every unitary central character datum, every descended coefficient norm has compact support on the quotient by the full abstract centre. It is unproved. In [SupercuspidalCoefficientCompactSupportReduction](../../Langlands/Representation/Exponents/SupercuspidalCoefficientCompactSupportReduction.md), `supercuspidalUnitaryCoefficientCompactSupportStructuralReduction` derives it from the three statements `StandardCocharacterStatement`, `RelativeRootSystemStatement` and `JointSpecialCompactBasisExistenceStatement`, of which the Library now proves the first two (`standardCocharacter`, `relativeRootSystem`), so that it rests on the third alone; the earlier `supercuspidalUnitaryCoefficientCompactSupportReduction` also assumes `ParabolicDynamicStatement`. For IV.3.2, `Langlands.UnitaryCentralCharacter.isUnitarizable_of_compact_coefficientNorm_of_nonarchimedean`, in [CompactCoefficientProof](../../Langlands/Representation/Unitary/CompactCoefficientProof.md), proves that a smooth irreducible representation of a nonarchimedean group with a unitary central character datum and compactly supported coefficient norms is unitarizable. No Library declaration composes these into a proof of `SupercuspidalUnitaryCentralCharacterUnitarizableStatement`. Two variants are proved: `Langlands.Aubert.General.RationalPointFamily.isUnitarizable_of_compact_normKernel_restriction`, in [RationalCompactRestrictionUnitarity](../../Langlands/Representation/Aubert/General/RationalCompactRestrictionUnitarity.md), assumes compact coefficients after restriction to the norm kernel, and `Langlands.HarishChandraSchwartz.isUnitarizable_of_irreducible_isSquareIntegrable_leftHaar`, in [LeftHaarSquareIntegrableUnitarity](../../Langlands/HarmonicAnalysis/HarishChandraSchwartz/LeftHaarSquareIntegrableUnitarity.md), assumes square integrability modulo a central subgroup. The forward VI.2.1 proof for standard families is in the [VI.2.1 map](cuspidal-decomposition-source-map.md) |
| (T5-b) | `Langlands.Aubert.General.RepresentedParabolic.LeviInductionUnitarizableStatement` (MaximalLeviReducibilityUnitaryInputs); `leviInductionUnitarizable_of_inputs` in [MaximalLeviReducibilityInductionInputs](../../Langlands/Representation/Exponents/MaximalLeviReducibilityInductionInputs.md); `Langlands.Aubert.General.normalizedInductionFunctor_obj_isUnitarizable_of_compactSpace` in [NormalizedInductionUnitarity](../../Langlands/Representation/Aubert/General/NormalizedInductionUnitarity.md); `Langlands.admissibleUnitarySemisimplicity` in [AdmissibleSemisimplicityProof](../../Langlands/Representation/Unitary/AdmissibleSemisimplicityProof.md); `Langlands.Plancherel.rationalUnramifiedRegular_exists_unitary_finset_ne_zero` in [RationalUnitaryNonvanishing](../../Langlands/Representation/Plancherel/RationalUnitaryNonvanishing.md) | Partly stated. The first claim, that normalized induction from an actual rational parabolic preserves unitarizability, is `LeviInductionUnitarizableStatement` (Renard IV.2.3), now proved (`leviInductionUnitarizable`). `leviInductionUnitarizable_of_inputs` derives it from four structural statements, all now proved: `RationalReductiveUnimodularityStatement`, `StandardCocharacterStatement`, `ArbitraryParabolicQuotientCompactStatement` and `ParabolicRootPresentationExistenceStatement`. `normalizedInductionFunctor_obj_isUnitarizable_of_compactSpace` proves it for a closed subgroup `P` with compact `P\G`, keeping the triviality of the modular character of `G` and the identity for the modular character of `P` as premises. For "hence completely reducible", `admissibleUnitarySemisimplicity` proves `AdmissibleUnitarySemisimplicityStatement`: when compact open subgroups are cofinal, an admissible unitarizable representation is semisimple. The filtration from VI.5.3(iii) and the pairwise distinctness of the central characters outside a Zariski closed subset are not stated as steps of VI.8.5. Related: `rationalUnramifiedRegular_exists_unitary_finset_ne_zero` gives, for a connected reductive group, one unitary unramified character at which finitely many nonzero regular functions are all nonzero; it proves nothing about central characters. Since Library `c0c7eab6`, the structural inputs of the distinctness step are stated. The statement `Langlands.Aubert.General.RepresentedParabolic.LeviNormalizerWeylGroupStatements` (`Langlands.Aubert.General.RepresentedParabolic.LeviNormalizerWeylGroupStatements`), in [LeviNormalizerQuotientStatements](../../Langlands/Representation/Exponents/LeviNormalizerQuotientStatements.md), now proved (`leviNormalizerWeylGroupStatements`), is the conjunction of two statements for an actual rational Levi `M` of an actual rational parabolic over a nonarchimedean local field. `LeviNormalizerFiniteQuotientStatement` asserts finitely many points `g j` of `G(k)` normalizing `M` such that every point normalizing `M` lies in some `g j · M(k)` (V.4.3.3 with V.3.7). `LeviNormalizerNormFixingStatement` asserts that a point normalizing `M` whose automorphism preserves every rational-character norm on the centre of `M(k)` lies in `M(k)` (V.3.5). The Markdown names a consumer `genericInducedIrreducibility_of_inputs`, which is not in the Library at `ddb0a9c0`. Four definition modules prove both conclusions when a cocharacter whose dynamic parabolic is the given `p` is supplied: `IsRationalLeviSubgroup.exists_finite_normalizer_representatives_of_dynamicParabolic` and `mem_pointImage_of_normalizes_of_norm_of_dynamicParabolic` in [DynamicLeviNormalizer](../../Langlands/Representation/Exponents/DynamicLeviNormalizer.md) (`Langlands.GroupScheme.IsRationalLeviSubgroup.normalizerRepresentativesOfDynamicParabolic`), built from `IsSplitComponent.exists_finite_normalizer_representatives` in [FiniteNormalizerRepresentatives](../../Langlands/Representation/Exponents/FiniteNormalizerRepresentatives.md) (`Langlands.GroupScheme.representativeNormalizerPoints`), `IsSplitComponent.mem_range_of_normalizes_of_norm` in [LeviNormalizerBridge](../../Langlands/Representation/Exponents/LeviNormalizerBridge.md) (`Langlands.GroupScheme.IsSplitComponent.automorphismRestrictionIso`) and `IsSplitComponent.comp_automorphism_eq_of_norm` in [SplitComponentNormRigidity](../../Langlands/Representation/Plancherel/SplitComponentNormRigidity.md) (`Langlands.GroupScheme.IsSplitComponent.automorphismRestriction`). Since the dynamic presentation stays an input, no Library theorem derives `LeviNormalizerWeylGroupStatements` from them. Since Library `ddb0a9c0`, a weaker form of the distinctness step is proved. The module of the statement `Langlands.Plancherel.RegularUnitaryTwistExistenceStatement` defines `Langlands.Plancherel.RegularUnitaryTwistExistenceStatement` in [ParabolicRegularUnitaryTwist](../../Langlands/Representation/Plancherel/ParabolicRegularUnitaryTwist.md), and `regularUnitaryTwistExistence` there proves it. Take a nonarchimedean local field, a connected reductive group whose point group is nonarchimedean, a `ParabolicRootPresentation r` of an actual rational parabolic with Levi, and a nontrivial smooth representation `π` of the literal Levi points with a central character. Then some unramified character `χ` of the full rational-norm family has `‖χ m‖ = 1` for every `m` and makes `π.twist χ` `IsNormalizerRegular`: no point of the normalizer of the Levi points outside them fixes its isomorphism class. This gives one regular unitary point, not the complement of a Zariski closed subset, and regularity rather than pairwise distinct central characters. The Markdown cites the central-character separation in the source proof, printed p.194 / PDF p.200, and the proof separates central characters through finitely many regular functions. Its main lemma `exists_unitary_twist_isNormalizerRegular` uses `exists_finite_normalizer_representatives_of_dynamicParabolic` and `mem_pointImage_of_normalizes_of_norm_of_dynamicParabolic` of `Langlands.GroupScheme.IsRationalLeviSubgroup.normalizerRepresentativesOfDynamicParabolic`, with `r` supplying the dynamic presentation, and `rationalUnramifiedRegular_exists_unitary_finset_ne_zero`. Its Markdown calls `Langlands.GroupScheme.IsRationalLeviSubgroup.normalizerRepresentativesOfDynamicParabolic` approved but unpublished, which is out of date: `Langlands.GroupScheme.IsRationalLeviSubgroup.normalizerRepresentativesOfDynamicParabolic` was published at `a419cc85`. The same submission named the local topology instance of RationalUnitaryNonvanishing.lean `rationalUnitaryNonvanishingPointTopology`; no declaration there changed |
| (L5) | `Langlands.Renard.AlgebraicFamily.CentralCharacterSplittingStatement` in [RenardCentralCharacterSplittingStatement](../../Langlands/Representation/Families/RenardCentralCharacterSplittingStatement.md). Related: `Langlands.CentralCharacterSplitting.splitting_of_distinct_centralCharacters`, `HasCentralCharacterSplitting`, `iSup_centralCharacterSpace_eq_top` in [CentralCharacterSplitting](../../Langlands/Representation/Filtration/CentralCharacterSplitting.md); `Langlands.CentralEigenspaceSplitting.eigenSubrep`, `eigenEquivGraded`, `iSup_eigenSubrep` in [CentralEigenspaceSplitting](../../Langlands/Representation/Filtration/CentralEigenspaceSplitting.md) | Stated; now proved, as `centralCharacterSplitting` (`Langlands/Representation/Families/RenardCentralCharacterSplittingProof.lean`). For any field `k`, any group `G`, any subgroup `Z` of the centre, every `A : Rep k G` with a filtration `s : ObjectRepFiltration A n` and injective `χ : Fin n → Z →* kˣ` such that each `z ∈ Z` acts on graded piece `i` by `χ i z`, the statement asserts `A ≅ ∐ i, s.gradedRepresentation i` in `Rep k G`. Related, not the statement: the module of the definition `Langlands.CentralCharacterSplitting.algebraFiltration` proves `splitting_of_distinct_centralCharacters` under the same hypotheses with `Z` the full centre and `[Infinite k]`. Its conclusion `HasCentralCharacterSplitting s χ` says that each central-character subrepresentation for `χ i` is equivalent to graded piece `i`, that these subrepresentations are independent, and that every subrepresentation is the supremum of its intersections with them; `iSup_centralCharacterSpace_eq_top` adds that they span. No Library theorem converts this into the coproduct isomorphism. The proof finds one element of the group algebra on which the characters take pairwise distinct values, which is where `Infinite k` is used, and applies `CentralEigenspaceSplitting`. That earlier module assumes one central element taking pairwise distinct scalars; see reading note 4 |
| (T5-c) | `Langlands.Aubert.General.isIrreducible_induction_of_semisimple_jacquetHom_rank_le_one`, `isIrreducible_induction_of_unitary_jacquetHom_rank_le_one` in [JacquetMultiplicityIrreducibility](../../Langlands/Representation/Aubert/General/JacquetMultiplicityIrreducibility.md). Related: `Langlands.Plancherel.UnitaryRegularParabolicIrreducibilityStatement`, `unitaryRegularParabolicIrreducibility_of_statements` in [ParabolicUnitaryPointIrreducibility](../../Langlands/Representation/Plancherel/ParabolicUnitaryPointIrreducibility.md); `Langlands.Plancherel.RegularSquareIntegrableJacquetMultiplicityStatement` in [RegularJacquetMultiplicityStatement](../../Langlands/Representation/Plancherel/RegularJacquetMultiplicityStatement.md); `Langlands.Plancherel.regularSquareIntegrableJacquetMultiplicity_of_statements` in [RegularSquareIntegrableJacquetMultiplicityReduction](../../Langlands/Representation/Plancherel/RegularSquareIntegrableJacquetMultiplicityReduction.md); `Langlands.Plancherel.isSquareIntegrableModCenter_pullback_of_modCentralSubgroup` in [ParabolicSquareIntegrableModCenter](../../Langlands/Representation/Plancherel/ParabolicSquareIntegrableModCenter.md) | Related, not the step. A nontrivial semisimple normalized induction `I σ` is irreducible if `Hom(r(I σ), σ)` has rank at most one; Frobenius reciprocity is applied inside the proof. The unitary version replaces semisimplicity by admissibility, unitarizability and cofinal compact opens, through `admissibleUnitarySemisimplicity`. The rank bound, which the source obtains from (T5-b) and (L5), is a hypothesis. Also related: the statement `UnitaryRegularParabolicIrreducibilityStatement`, which has no theorem but follows from proved results (the reduction below, all four of whose inputs are proved) (published with `Langlands.Plancherel.UnitaryRegularParabolicIrreducibilityReductionStatement`), adapted from Waldspurger 2003, Proposition IV.2.2(i), asserts for an irreducible `π` of the Levi points that is square-integrable modulo `C`, and a unitary unramified `χ` with `π.twist χ` normalizer-regular, that the induction `UnramifiedLeviInduction` of `π` twisted by `χ` is irreducible. Its hypothesis is square integrability modulo `C`, not supercuspidality, and it concerns `UnramifiedLeviInduction`, not the fibres of the family of (T5). In the same module `UnitaryRegularParabolicIrreducibilityReductionStatement`, proved by `unitaryRegularParabolicIrreducibility_of_statements`, derives it from `RegularSquareIntegrableJacquetMultiplicityStatement`, `RationalReductiveUnimodularityStatement`, `StandardCocharacterStatement` and `ArbitraryParabolicQuotientCompactStatement`; the proof applies `isIrreducible_induction_of_unitary_jacquetHom_rank_le_one`. The first input (the statement `Langlands.Plancherel.RegularSquareIntegrableJacquetMultiplicityStatement`, published at commit `a419cc85`) is the rank bound: for such `π` with `IsNormalizerRegular π`, the intertwining maps from the Jacquet module of `leviTwistedInductionFunctor` applied to `π` into `π` have rank at most one. Its docstring calls it the Jacquet multiplicity consequence of Waldspurger 2003, Corollary III.7.3, and its module records it as a derived target. It is now proved (`regularSquareIntegrableJacquetMultiplicity`). `RegularSquareIntegrableJacquetMultiplicityReductionStatement` (`Langlands.Plancherel.RegularSquareIntegrableJacquetMultiplicityReductionStatement`), proved by `regularSquareIntegrableJacquetMultiplicity_of_statements`, derives it from five statements, of which only `TemperedSquareIntegrableUnitaryPartStatement` is still unproved: `RepresentedGeometricLemmaStatement`, `TemperedSquareIntegrableUnitaryPartStatement`, `ArbitraryParabolicQuotientCompactStatement`, `SquareIntegrableNormalizedTemperedStatement` and `ArbitraryParabolicJacquetAdmissibilityStatement`. Its route bounds Hom spaces along the geometric-lemma filtration instead of decomposing the weak Jacquet module as in Waldspurger III.7.2–III.7.3. Its proof uses `isSquareIntegrableModCenter_pullback_of_modCentralSubgroup` from the module of the definition `Langlands.Plancherel.schemeCenterToParabolicCenter`. None of these modules proves the step |
| (P6) | `Langlands.Renard.AlgebraicFamily.EndomorphismScalarStatement` in [RenardFamilyEndomorphismStatement](../../Langlands/Representation/Families/RenardFamilyEndomorphismStatement.md); proof `endomorphismScalar` and helpers `exists_fixedVectors_retraction`, `projective_fixedVectors`, `eq_zero_of_forall_linearForm`, `exists_fiber_scalar` in [RenardFamilyEndomorphismProof](../../Langlands/Representation/Families/RenardFamilyEndomorphismProof.md) | Proved. Take a smooth flat `ρ` with every compact-open `V^K` finite, a `G`-equivariant `B`-linear `φ`, and a Zariski-dense `Ξ`, meaning that every `b` vanishing on `Ξ` vanishes at every point. If every fiber `ℂ ⊗[B] V` at a point of `Ξ` is irreducible, then `φ` is the action of some `b : B`. It is stated for every locally profinite `G`. The proof does not follow the source's route through local freeness and does not use the statements of rows (P1) and (L1), which were unproved when it was published. Each compact-open `V^K` is a `B`-linear retract of the flat `V` and finite over the Noetherian `B`, hence projective. Linear forms `V →ₗ[B] B` separate vectors. Schur's lemma on the fibers at the points of `Ξ` and the Nullstellensatz give a linear relation between `φ` and the linear forms. Nakayama's lemma gives an element of the ideal of values of linear forms that acts as the identity on `V`, and writing it through linear forms produces `b`. See reading note 6 |
| (Ex6) | `Langlands.Renard.AlgebraicFamily.SupercuspidalFamilyEndomorphismStatement` in [RenardSupercuspidalFamilyEndomorphismStatement](../../Langlands/Representation/Families/RenardSupercuspidalFamilyEndomorphismStatement.md) | Stated, unproved: the Library derives it only from further hypotheses, by `supercuspidalFamilyEndomorphism_of_statements`. For a nonarchimedean local field, a connected reductive group, an actual rational parabolic with rational Levi `M` and geometric unipotent radical, including `P = G`, and an irreducible supercuspidal smooth `σ` of `M(k)`, let `B` be `Plancherel.unramifiedRegularFunctions` of the rational norm characters of `M` and `ρ_B` the universal family `universalUnramifiedRepresentation` on `B ⊗[ℂ] W`. The statement asserts that every `B`-linear endomorphism of `LeviInduced … ρ_B` commuting with `leviInducedRepresentation` is multiplication by some `b : B`. The induction is the general-family construction of row (I). Only the first paragraph of the Example is stated; the consequence for the centre of `M(G)[ρ]`, which recovers VI.4.5, is not. Row (P6) is proved, but the source's route also needs (T5), which is unproved, and an identification of the fibers of `LeviInduced … ρ_B` with the induced twists |

## Source reading notes

These are the readings of the printed text. None of them is checked
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

At Library `ddb0a9c0` these assertions have no published statement:

1. (Sp) as a named construction for general families.
2. The functors on morphisms of (BC), (I) and (J) over a general `B`, and
   base change as a construction from `FamilyModule B G` to
   `FamilyModule C G`. Base change preserves smoothness and flatness, as
   row (BC) records.
3. (Sp-φ); (T5-b) apart from its first claim, the normalizer inputs of
   `Langlands.Aubert.General.RepresentedParabolic.LeviNormalizerWeylGroupStatements` and the single regular unitary twist of `Langlands.Plancherel.RegularUnitaryTwistExistenceStatement`; (T5-c) as
   a step about the family of (T5), of which `Langlands.Plancherel.UnitaryRegularParabolicIrreducibilityReductionStatement` states only a
   square-integrable analogue; and the consequence of (Ex6) for the centre
   of `M(G)[ρ]`.

These were stated but unproved when this note was updated; the present status
follows the items that were checked again:

- (P2) with (VI.8.2.2), and (P3), by `InductionBaseChangeStatement`,
  `JacquetFiniteTypeStatement` and their conjunction `ParabolicStatements`
  of `Langlands.Renard.AlgebraicFamily.ParabolicStatements`. Now proved, as
  `inductionBaseChange` and `jacquetFiniteType`.
- The flatness in (I), (L2) and the flatness in (J), by
  `InductionFlatStatement`, `InductionAdmissibleStatement`,
  `JacquetFlatStatement` and their conjunction `ParabolicFlatnessStatements`
  of `Langlands.Renard.AlgebraicFamily.ParabolicFlatnessStatements`. Now proved, as
  `inductionFlat`, `inductionAdmissible` and `jacquetFlat`.
- (P4) and (T5), by `InducedIrreducibilityOpenStatement` and
  `GenericInducedIrreducibilityStatement` of `Langlands.Renard.AlgebraicFamily.GenericIrreducibilityStatements`. Still
  unproved: the Library derives each only from further hypotheses. The definition `Langlands.Renard.AlgebraicFamily.InducedIrreducibilityOpenAssembly.Inputs`
  reduces (P4) to three statements, two of them unproved (row (P4)).
- The second claim of (T5-a) and the first claim of (T5-b), by
  `SupercuspidalUnitaryCentralCharacterUnitarizableStatement` and
  `LeviInductionUnitarizableStatement` of `Langlands.Aubert.General.RepresentedParabolic.MaximalLeviSupercuspidalUnitarizableConstituentStatement`; and the VI.2.1 input
  `SupercuspidalUnitaryCoefficientCompactSupportStatement` of `Langlands.Aubert.General.RepresentedParabolic.SupercuspidalUnitaryCoefficientCompactSupportStatement`,
  which `Langlands.Aubert.General.RepresentedParabolic.SupercuspidalUnitaryCoefficientCompactSupportReductionStatement` and `Langlands.Aubert.General.RepresentedParabolic.SupercuspidalUnitaryCoefficientCompactSupportStructuralReductionStatement` reduce to structural statements, of which only `JointSpecialCompactBasisExistenceStatement` is unproved. `LeviInductionUnitarizableStatement` is now proved (`leviInductionUnitarizable`); `SupercuspidalUnitaryCentralCharacterUnitarizableStatement` is not.
- (L5), (Ex6) and (Ex-c), by `CentralCharacterSplittingStatement` of
  `Langlands.Renard.AlgebraicFamily.CentralCharacterSplittingStatement`, `SupercuspidalFamilyEndomorphismStatement` of `Langlands.Renard.AlgebraicFamily.SupercuspidalFamilyEndomorphismStatement` and
  `UniversalSpecializationStatement` of `Langlands.Renard.AlgebraicFamily.UniversalSpecializationStatement`.
  (L5) and (Ex-c) are now proved, as `centralCharacterSplitting` and
  `universalSpecialization`; (Ex6) is still unproved (the Library derives it
  only from further hypotheses).
- The helper statements `InducedTwistsUniformDetectionStatement` of
  `Langlands.Renard.AlgebraicFamily.InducedTwistsUniformDetectionStatement`, `RationalLeviInductionOpennessStatement` of `Langlands.Plancherel.RationalLeviInductionOpennessStatement` and
  `UnramifiedUniformGenerationStatement` of `Langlands.Plancherel.UnramifiedUniformGenerationStatement` (row (P4)),
  `LeviNormalizerWeylGroupStatements` of `Langlands.Aubert.General.RepresentedParabolic.LeviNormalizerWeylGroupStatements` (row (T5-b)), and
  `UnitaryRegularParabolicIrreducibilityStatement` of `Langlands.Plancherel.UnitaryRegularParabolicIrreducibilityReductionStatement` and
  `RegularSquareIntegrableJacquetMultiplicityStatement` of `Langlands.Plancherel.RegularSquareIntegrableJacquetMultiplicityStatement`
  (row (T5-c)).

The
conjunction `Statements` of the five statements of `Langlands.Renard.AlgebraicFamily.Statements` is proved by
`Langlands.Renard.AlgebraicFamily.statements` from the proofs `Langlands.Renard.AlgebraicFamily.fixedTensorComparison`, `Langlands.Renard.AlgebraicFamily.flatnessCriterion`, `Langlands.Renard.AlgebraicFamily.localFreeCover`, `Langlands.Renard.AlgebraicFamily.admissibilityCriterion` and
`Langlands.Renard.AlgebraicFamily.specializationAdmissibility` of (P1-iso), (R1), (T4), (P1) and (L1). The RenardFamilyStatements
Markdown refers to this note's earlier numbering, in which the five
assertions were unpublished items 2, 3, 4 and 8. (P6), stated by `Langlands.Renard.AlgebraicFamily.EndomorphismScalarStatement`, is
proved by `Langlands.Renard.AlgebraicFamily.endomorphismScalar`. The three VI.8 statements
`UniversalInducedCoefficientFinitenessStatement`,
`RationalUniversalTensorFinitenessStatement` and
`RationalNormalizedInducedSpecializationStatement` were published together, and all three are proved. Of the
related statements, `Langlands.Plancherel.ConditionalParabolicGenericIrreducibilityStatement` (row (T5)) is proved by `Langlands.Plancherel.conditionalParabolicGenericIrreducibility`, `Langlands.Plancherel.FiniteMatrixIrreducibilityOpennessStatement` (row (P4))
is proved by `Langlands.Plancherel.finiteMatrixIrreducibilityOpenness`, and `Langlands.Plancherel.CompactFixedFamilyOpennessStatement` (row (P4)) is proved by `Langlands.Plancherel.compactFixedFamilyOpenness`.
The reductions stated by `Langlands.Plancherel.ParabolicGenericIrreducibilityReductionStatement` (row (T5)) and by `Langlands.Plancherel.UnitaryRegularParabolicIrreducibilityReductionStatement` and
`Langlands.Plancherel.RegularSquareIntegrableJacquetMultiplicityReductionStatement` (row (T5-c)) are proved in their own modules, and
`RegularUnitaryTwistExistenceStatement` of `Langlands.Plancherel.RegularUnitaryTwistExistenceStatement` (row (T5-b)) is proved.
The definitions `Langlands.Renard.AlgebraicFamily.leviInducedRepresentation`, in its second version, and
`Langlands.Renard.AlgebraicFamily.FamilyModule` carry the constructions of
rows (D), (BC), (I) and (J), and `Langlands.Renard.AlgebraicFamily.MatrixGenerationWitness.wordDeterminant` the determinant witnesses of row
(P4). The fourteen definition modules new at `c0c7eab6` are helpers for rows
(P4), (C2), (L5) and (T5-b); none of them proves a statement of this note.
Of the definition modules new at `ddb0a9c0` other than the second version of `Langlands.Renard.AlgebraicFamily.leviInducedRepresentation`, `Langlands.Renard.AlgebraicFamily.ActualLevi.universalFamily`
and `Langlands.Renard.AlgebraicFamily.InducedIrreducibilityOpenAssembly.Inputs` build the family of row (P4) and its reduction, `Langlands.Plancherel.representedInductionLeviEquiv`
serves row (T5) and `Langlands.Plancherel.schemeCenterToParabolicCenter` row (T5-c); none of them proves a statement
of this note.

## Modules in the Library

All seventy-seven modules are in the Library; the table gives the Library commit
at which each first appeared. Twenty-two modules record qualifications of their
scope, summarized after the table.

| Module | First appeared at Library commit |
| --- | --- |
| VI.8.2 statement (`UniversalInducedCoefficientFinitenessStatement`) | `1eb9a9ee0815224a368f8dc58b7d95f024cfff05` |
| VI.8.1 statement (`RationalUniversalTensorFinitenessStatement`) | `80f702330eab13242c1eb52eee2757a5d07eb1ba` |
| VI.8.2 statement (`RationalNormalizedInducedSpecializationStatement`) | `1eb9a9ee0815224a368f8dc58b7d95f024cfff05` |
| Proof `universalInducedCoefficientFiniteness` | `334440350ec029c1bf78b7801689e1a2b21079c6` |
| Proof `rationalNormalizedInducedSpecialization` | `334440350ec029c1bf78b7801689e1a2b21079c6` |
| Proof `rationalUniversalTensorFiniteness` | `6f182f920309bbe9e9e43bd7181d7e25d5c02acd` |
| VII.1.3 proof, publishing PositiveUnramifiedCentralTwist (`maximalLeviSupercuspidalReducibilityFromInputs`) | `8b3ba080b2e8bcecb1612373f236b9ad96423d12` |
| VI.4.1 comparison proof (`Langlands.CuspidalSupport.rationalUniversalProgeneratorComparison`) | `334440350ec029c1bf78b7801689e1a2b21079c6` |
| Compact quotient proof (`Langlands.Induction.compactQuotientClause_holds`) | `e3c2fa98be720f63c6981efbbdf15cd223329e76` |
| Coefficient algebra (`regularAlgebraLaurentEquiv`) | `80f702330eab13242c1eb52eee2757a5d07eb1ba` |
| Fixed-vector model (`Langlands.Induction.fixedEvaluationEquiv`) | `24243ad1d7d77cd0f3cd88510b523cb2a13a1142` |
| Eigenspace splitting (`Langlands.CentralEigenspaceSplitting.eigenSubrep`) | `bc8de2287e5c24972c55277b2aa9611523dfc5dc` |
| Universal models (`jacquetRepresentation`) | `0d12b7d171600d15516e52ee508d3aaca3e9cf9e` |
| Specialization maps (`jacquetEvaluation`) | `1831431f93603e52c73600a2a900dd42d7f18deb` |
| Admissibility of universal and conjugate induced models (`Langlands.Plancherel.RationalNormalized.conjugateOutputInducedRepresentation`) | `291705a7b40579e0118c8512a32d7f8212883f2e` |
| Generic irreducibility statement (`Langlands.Plancherel.ConditionalParabolicGenericIrreducibilityStatement`) | `291705a7b40579e0118c8512a32d7f8212883f2e` |
| Finite matrix openness statement (`Langlands.Plancherel.FiniteMatrixIrreducibilityOpennessStatement`) | `f73044d93e675a78ed75830ef026b3224514e510` |
| VI.8.1 and VI.8.4 general-family statements (`Langlands.Renard.AlgebraicFamily.Statements`) | `0d9cba336dd98294a5d7f48d772eb708aae40708` |
| Proof `Langlands.Plancherel.finiteMatrixIrreducibilityOpenness` | `ce52163e150fe772fdb773627f006a99df1688af` |
| Compact-fixed family openness statement (`Langlands.Plancherel.CompactFixedFamilyOpennessStatement`) | `0d9cba336dd98294a5d7f48d772eb708aae40708` |
| Unitary nonvanishing (`Langlands.Plancherel.rationalUnitaryRegularRestriction`) | `0d9cba336dd98294a5d7f48d772eb708aae40708` |
| Jacquet multiplicity irreducibility (`Langlands.Aubert.General.jacquetScalarEquiv`) | `ce52163e150fe772fdb773627f006a99df1688af` |
| Square-integrable unitarity (`Langlands.HarishChandraSchwartz.LeftHaarDualForm.positiveForm`) | `f73044d93e675a78ed75830ef026b3224514e510` |
| Compact coefficient unitarity (`Langlands.UnitaryCentralCharacter.compactCoefficientPositiveForm`) | `86cf8f8984679ba48ded6fa152c55ec38b532d97` |
| Norm-kernel restriction unitarity (`Langlands.Aubert.General.RationalPointFamily.rationalNormKernelPositiveForm`) | `c5e0296f115eacde9bd491a7ea70fec6983c1c1c` |
| Normalized induction unitarity (`Langlands.Aubert.General.compactQuotientNormalizedInductionForm`) | `25b91125ea94e88d741b206d633e82eb0d87c3e5` |
| Proof `Langlands.admissibleUnitarySemisimplicity` | `484c26ed207bd2fb5ed2073a5c6b37860c04f67b` |
| VII.1.3 unitary input statements (`Langlands.Aubert.General.RepresentedParabolic.MaximalLeviSupercuspidalUnitarizableConstituentStatement`) | `08e8de28d111b66b088500c8ad1b0bd0f947991d` |
| Coefficient compactness statement (`Langlands.Aubert.General.RepresentedParabolic.SupercuspidalUnitaryCoefficientCompactSupportStatement`) | `86cf8f8984679ba48ded6fa152c55ec38b532d97` |
| Four-premise reduction (`Langlands.Aubert.General.RepresentedParabolic.SupercuspidalUnitaryCoefficientCompactSupportReductionStatement`) | `1eb9a9ee0815224a368f8dc58b7d95f024cfff05` |
| Three-premise reduction (`Langlands.Aubert.General.RepresentedParabolic.SupercuspidalUnitaryCoefficientCompactSupportStructuralReductionStatement`) | `d82893a7de0b168873a15c6c7b0a731deb27aa23` |
| VI.8.6 statement (`Langlands.Renard.AlgebraicFamily.EndomorphismScalarStatement`) | `2816ea5d81e2fb9b0512bd1d8dec2ad7797026fd` |
| VI.8.4 and VI.8.5 statements (`Langlands.Renard.AlgebraicFamily.GenericIrreducibilityStatements`) | `2816ea5d81e2fb9b0512bd1d8dec2ad7797026fd` |
| Proof `Langlands.Plancherel.compactFixedFamilyOpenness` | `2816ea5d81e2fb9b0512bd1d8dec2ad7797026fd` |
| VI.8.2 and VI.8.3 family constructions (`Langlands.Renard.AlgebraicFamily.leviInducedRepresentation`) | `8b14de0b5103d5fc1e615f094904129bf8cfe3a3` |
| VI.8.1 category of `(G, B)`-modules (`Langlands.Renard.AlgebraicFamily.FamilyModule`) | `0de01f0733138058931a79588c434f55c4639cbc` |
| VI.8.2 and VI.8.3 Propositions (`Langlands.Renard.AlgebraicFamily.ParabolicStatements`) | `0de01f0733138058931a79588c434f55c4639cbc` |
| VI.8.2 and VI.8.3 flatness and admissibility (`Langlands.Renard.AlgebraicFamily.ParabolicFlatnessStatements`) | `0de01f0733138058931a79588c434f55c4639cbc` |
| Proof `Langlands.Renard.AlgebraicFamily.localFreeCover` | `0de01f0733138058931a79588c434f55c4639cbc` |
| Proof `Langlands.Renard.AlgebraicFamily.fixedTensorComparison` | `0de01f0733138058931a79588c434f55c4639cbc` |
| Proof `Langlands.Renard.AlgebraicFamily.flatnessCriterion` | `0de01f0733138058931a79588c434f55c4639cbc` |
| Proof `Langlands.Renard.AlgebraicFamily.endomorphismScalar` | `0de01f0733138058931a79588c434f55c4639cbc` |
| Matrix generation witnesses (`Langlands.Renard.AlgebraicFamily.MatrixGenerationWitness.wordDeterminant`) | `0de01f0733138058931a79588c434f55c4639cbc` |
| VI.8.5 Lemma statement (`Langlands.Renard.AlgebraicFamily.CentralCharacterSplittingStatement`) | `a419cc8566081d901325c46ed3d626b2ebb04395` |
| VI.8.6 Example statement (`Langlands.Renard.AlgebraicFamily.SupercuspidalFamilyEndomorphismStatement`) | `a419cc8566081d901325c46ed3d626b2ebb04395` |
| VI.8.1 Example statement (`Langlands.Renard.AlgebraicFamily.UniversalSpecializationStatement`) | `a419cc8566081d901325c46ed3d626b2ebb04395` |
| Proof `Langlands.Renard.AlgebraicFamily.admissibilityCriterion` | `a419cc8566081d901325c46ed3d626b2ebb04395` |
| Proof `Langlands.Renard.AlgebraicFamily.specializationAdmissibility` | `a419cc8566081d901325c46ed3d626b2ebb04395` |
| Central-character splitting (`Langlands.CentralCharacterSplitting.algebraFiltration`) | `a419cc8566081d901325c46ed3d626b2ebb04395` |
| Actual Levi parameters (`Langlands.Renard.AlgebraicFamily.ActualLevi.parameterEquiv`) | `a419cc8566081d901325c46ed3d626b2ebb04395` |
| Uniform detection statement (`Langlands.Renard.AlgebraicFamily.InducedTwistsUniformDetectionStatement`) | `a419cc8566081d901325c46ed3d626b2ebb04395` |
| Localized compression assembly (`Langlands.Renard.AlgebraicFamily.CompactCompressionPrincipalOpen.IsFullSpecialization`) | `a419cc8566081d901325c46ed3d626b2ebb04395` |
| Compression matrices (`Langlands.Renard.AlgebraicFamily.CompactCompressionMatrices.fixedMatrix`) | `a419cc8566081d901325c46ed3d626b2ebb04395` |
| Global coefficient families (`Langlands.Renard.AlgebraicFamily.CompactCompressionPrincipalOpen.IsGlobalCoefficientFamily`) | `a419cc8566081d901325c46ed3d626b2ebb04395` |
| Specialized compression matrices (`Langlands.Renard.AlgebraicFamily.CompactCompressionMatrices.coefficientMatrix`) | `a419cc8566081d901325c46ed3d626b2ebb04395` |
| Localized matrix neighborhoods (`Langlands.Renard.AlgebraicFamily.LocalizedMatrixPrincipalOpen.regularWitness`) | `a419cc8566081d901325c46ed3d626b2ebb04395` |
| Polynomial witnesses (`Langlands.Renard.AlgebraicFamily.UnramifiedPolynomialWitness.rationalRegularPolynomial`) | `a419cc8566081d901325c46ed3d626b2ebb04395` |
| Generic induced specialization (`Langlands.Plancherel.UnramifiedNormalized.inducedSpecializationEquiv`) | `a419cc8566081d901325c46ed3d626b2ebb04395` |
| Levi normalization fixed matrices (`Langlands.Plancherel.RationalNormalized.inducedLeviNormalizationEquiv`) | `a419cc8566081d901325c46ed3d626b2ebb04395` |
| Levi induction openness statement (`Langlands.Plancherel.RationalLeviInductionOpennessStatement`) | `a419cc8566081d901325c46ed3d626b2ebb04395` |
| Uniform generation statement (`Langlands.Plancherel.UnramifiedUniformGenerationStatement`) | `a419cc8566081d901325c46ed3d626b2ebb04395` |
| Dynamic Levi normalizers (`Langlands.GroupScheme.IsRationalLeviSubgroup.normalizerRepresentativesOfDynamicParabolic`) | `a419cc8566081d901325c46ed3d626b2ebb04395` |
| Finite normalizer representatives (`Langlands.GroupScheme.representativeNormalizerPoints`) | `a419cc8566081d901325c46ed3d626b2ebb04395` |
| Levi normalizer bridge (`Langlands.GroupScheme.IsSplitComponent.automorphismRestrictionIso`) | `a419cc8566081d901325c46ed3d626b2ebb04395` |
| Split-component norm rigidity (`Langlands.GroupScheme.IsSplitComponent.automorphismRestriction`) | `a419cc8566081d901325c46ed3d626b2ebb04395` |
| Levi normalizer statements (`Langlands.Aubert.General.RepresentedParabolic.LeviNormalizerWeylGroupStatements`) | `a419cc8566081d901325c46ed3d626b2ebb04395` |
| Proof `Langlands.Renard.AlgebraicFamily.statements` | `3f1412571c4c931abb11fdcd373eaf66fd0c5385` |
| VI.8.4 assembly (`Langlands.Renard.AlgebraicFamily.InducedIrreducibilityOpenAssembly.Inputs`) | `3f1412571c4c931abb11fdcd373eaf66fd0c5385` |
| Actual Levi induced family (`Langlands.Renard.AlgebraicFamily.ActualLevi.universalFamily`) | `3f1412571c4c931abb11fdcd373eaf66fd0c5385` |
| Generic irreducibility reduction (`Langlands.Plancherel.ParabolicGenericIrreducibilityReductionStatement`) | `3f1412571c4c931abb11fdcd373eaf66fd0c5385` |
| Regular unitary twist statement (`Langlands.Plancherel.RegularUnitaryTwistExistenceStatement`) | `3f1412571c4c931abb11fdcd373eaf66fd0c5385` |
| Regular unitary point irreducibility reduction (`Langlands.Plancherel.UnitaryRegularParabolicIrreducibilityReductionStatement`) | `3f1412571c4c931abb11fdcd373eaf66fd0c5385` |
| Jacquet multiplicity reduction (`Langlands.Plancherel.RegularSquareIntegrableJacquetMultiplicityReductionStatement`) | `3f1412571c4c931abb11fdcd373eaf66fd0c5385` |
| Represented induction comparison (`Langlands.Plancherel.representedInductionLeviEquiv`) | `3f1412571c4c931abb11fdcd373eaf66fd0c5385` |
| Square integrability modulo the centre (`Langlands.Plancherel.schemeCenterToParabolicCenter`) | `3f1412571c4c931abb11fdcd373eaf66fd0c5385` |
| VI.8.2 and VI.8.3 family constructions, second version (`Langlands.Renard.AlgebraicFamily.leviInducedRepresentation`) | `3f1412571c4c931abb11fdcd373eaf66fd0c5385` |
| Jacquet multiplicity statement (`Langlands.Plancherel.RegularSquareIntegrableJacquetMultiplicityStatement`) | `a419cc8566081d901325c46ed3d626b2ebb04395` |

The VI.4.1 comparison `Langlands.CuspidalSupport.rationalUniversalProgeneratorComparison` is not a VI.8 result. It is listed because
the prerequisite section of the uniform compression note now cites it. The
statements `Langlands.Plancherel.ConditionalParabolicGenericIrreducibilityStatement`, `Langlands.Plancherel.FiniteMatrixIrreducibilityOpennessStatement` and `Langlands.Plancherel.CompactFixedFamilyOpennessStatement` and the declarations `Langlands.Plancherel.finiteMatrixIrreducibilityOpenness`,
`Langlands.Plancherel.compactFixedFamilyOpenness`, `Langlands.Plancherel.rationalUnitaryRegularRestriction`, `Langlands.Aubert.General.jacquetScalarEquiv` and `Langlands.HarishChandraSchwartz.LeftHaarDualForm.positiveForm` are related to (T5), (P4) and the steps
of (T5) only, as the rows explain. All of them except `Langlands.Plancherel.ConditionalParabolicGenericIrreducibilityStatement` came from
the work on its proof. The statement `Langlands.Aubert.General.RepresentedParabolic.MaximalLeviSupercuspidalUnitarizableConstituentStatement`
states the inputs for the unitary case of VII.1.3; this note uses two of
them. `Langlands.Aubert.General.RepresentedParabolic.SupercuspidalUnitaryCoefficientCompactSupportReductionStatement` and `Langlands.Aubert.General.RepresentedParabolic.SupercuspidalUnitaryCoefficientCompactSupportStructuralReductionStatement` are conditional reductions, not
proofs of the coefficient compactness statement. The
definition `Langlands.Renard.AlgebraicFamily.MatrixGenerationWitness.wordDeterminant` is a helper for (P4) and does not prove it. Of the
twenty-three modules new at `c0c7eab6`, the three statement modules
and the proofs `Langlands.Renard.AlgebraicFamily.admissibilityCriterion` and `Langlands.Renard.AlgebraicFamily.specializationAdmissibility` carry rows (L5), (Ex6), (Ex-c), (P1)
and (L1); `Langlands.Renard.AlgebraicFamily.specializationAdmissibility` also proves the smoothness claim of row (BC). The other eighteen are helpers for rows (P4), (C2), (L5) and
(T5-b), as those rows explain. Of the four statements among them,
`LeviNormalizerWeylGroupStatements` is now proved (`leviNormalizerWeylGroupStatements`); the
other three are unproved. Of
the eleven modules added in this update, the proof `Langlands.Renard.AlgebraicFamily.statements` assembles
`Statements`; `Langlands.Renard.AlgebraicFamily.InducedIrreducibilityOpenAssembly.Inputs` and `Langlands.Renard.AlgebraicFamily.ActualLevi.universalFamily` serve row (P4), `Langlands.Plancherel.ParabolicGenericIrreducibilityReductionStatement` and
`Langlands.Plancherel.representedInductionLeviEquiv` row (T5), `Langlands.Plancherel.RegularUnitaryTwistExistenceStatement` row (T5-b), and `Langlands.Plancherel.UnitaryRegularParabolicIrreducibilityReductionStatement`, `Langlands.Plancherel.RegularSquareIntegrableJacquetMultiplicityStatement`,
`Langlands.Plancherel.RegularSquareIntegrableJacquetMultiplicityReductionStatement` and `Langlands.Plancherel.schemeCenterToParabolicCenter` row (T5-c); the eleventh is the second version of
`Langlands.Renard.AlgebraicFamily.leviInducedRepresentation`. Among their statements, the four reductions and
`RegularUnitaryTwistExistenceStatement` are proved, while
`UnitaryRegularParabolicIrreducibilityStatement` and
`RegularSquareIntegrableJacquetMultiplicityStatement` are not.

Each proof was checked by a Lake build against the exact target, with the
statement and its inputs unchanged; each statement and definition by a Lake
build and a check of the declaration kind.

Qualifications of scope:

- `RationalUniversalTensorFinitenessStatement`: local compactness and nonarchimedeanness of the rational
  points and affineness of the Levi stay explicit structural hypotheses; no
  proof is claimed.
- `RationalNormalizedInducedSpecializationStatement`: this is the specialization case of the source's base-change
  result; the map and its pure-tensor formula are proved, and bijectivity is
  the target. The structural hypotheses stay explicit.
- `rationalUniversalTensorFiniteness`: the module proves the universal tensor prerequisite only; the
  full normalized output-Jacquet finiteness is not proved by it.
- `Langlands.Induction.fixedEvaluationEquiv`: the construction proves neither same-Levi induction
  independence nor the Weyl-conjugacy target for which it was made.
- `Langlands.Induction.compactQuotientClause_holds`: helper lemmas are reproved under new public names;
  intermediate lemmas are stated over a commutative ring, Noetherian for
  admissibility; the proof route is internal, since BZ77 1.9(e) refers to an
  earlier paper that was not consulted.
- `Langlands.Plancherel.RationalNormalized.conjugateOutputInducedRepresentation`: the conjugate Levi, its containment and conjugation formula,
  the continuous semidirect projection and the compact inducing quotient are
  geometric inputs; identifying the orbit Jacquet quotients with these
  induced models, the rational orbit geometry, the Haar-normalization
  comparison, the elimination of proper pieces and the global finiteness
  theorem remain separate obligations.
- `Langlands.Plancherel.ConditionalParabolicGenericIrreducibilityStatement`: this is a `Prop`-valued statement with an elementary
  centrality helper, not a proof; its conclusion gives only a nonempty open
  locus in the character space, and the full Waldspurger IV.2.2, the
  regularity and invertibility of standard intertwiners and orbit descent
  remain open.
- `Langlands.Renard.AlgebraicFamily.Statements`: the admissibility conclusion of `SpecializationAdmissibilityStatement`
  uses `Langlands.IsAdmissible`, a condition on every open subgroup, which in
  a t.d. group is equivalent to the source's compact-open condition; this
  equivalence is not checked in Lean. The fiber is `ℂ ⊗[B] V`, with the
  factors in the opposite order to the source's.
- `Langlands.Aubert.General.RationalPointFamily.rationalNormKernelPositiveForm`: compact smooth-dual coefficients on the norm-kernel
  restriction, the unitary central character, irreducibility, the finite
  index of the central valuation image and the topological hypotheses are
  retained, not derived from cuspidality.
- `Langlands.Aubert.General.compactQuotientNormalizedInductionForm`: compactness of the rational parabolic quotient, rational-point
  unimodularity and the modular-character identity remain geometric
  obligations.
- `Langlands.Aubert.General.RepresentedParabolic.MaximalLeviSupercuspidalUnitarizableConstituentStatement`: none of the input statements is proved here; some are stated
  in the form in which the proof of VII.1.3 applies them; several omit
  properness and maximality of the parabolic, and the supercuspidal
  unitarity input is stated for every connected reductive group.
- `Langlands.Renard.AlgebraicFamily.EndomorphismScalarStatement`: the statement is made for every locally profinite `G`, and
  the source's proof was checked outside Lean to work in this generality;
  Zariski density is encoded through vanishing of elements of `B`; the
  specialization is `ℂ ⊗[B] V`, with the factors in the opposite order to the
  source's.
- `Langlands.Renard.AlgebraicFamily.GenericIrreducibilityStatements`: the VI.8.4 open set is required to contain `ψ₀`, which the
  source proof provides; Zariski open sets of `X(M)` are represented by
  principal open sets of polynomials in the published canonical coordinates,
  a correspondence argued in the Markdown and not checked in Lean; every
  actual rational parabolic, including `P = G`, is allowed.
- `Langlands.Renard.AlgebraicFamily.leviInducedRepresentation` (first version): only objects, defining laws and one comparison lemma are
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
  closed subgroup over a nonarchimedean local field. The error was found after
  the module entered the Library and corrected in the second version. What remains true is that no Library theorem states the
  agreement. The identification of `c_U` with Renard's `δ_P^{-1}` is a
  documented convention conversion, not a Lean statement.
- `Langlands.Renard.AlgebraicFamily.leviInducedRepresentation` (second version): the first, second and fourth qualifications repeat those of
  the first version. The third replaces the inaccurate part: for the radical image
  of a represented parabolic over a nonarchimedean local field, the
  unimodularity hypothesis is the published
  `RepresentedParabolic.isUnimodularModulus_pointImage_radical`, which
  assumes `[ValuativeRel k] [IsNonarchimedeanLocalField k]` beyond the
  module's instances; no Library theorem applies it to `LeviInduced`, and
  agreement of `leviInducedRepresentation` at `B = ℂ` with the published
  complex induction on represented parabolics is not stated in the Library.
- `Langlands.Renard.AlgebraicFamily.FamilyModule`: the definitions need only a commutative ring `B`; Renard's
  standing hypotheses on `B` are not imposed. Admissibility quantifies over
  open subgroups with compact carrier, as in RenardFamilyStatements, not over
  all open subgroups as the published `SmoothRep.IsAdmissible` does. No
  additive or abelian structure and no functor other than the two inclusions
  is defined.
- `Langlands.Renard.AlgebraicFamily.ParabolicStatements`: the scalars are on the left, as in Mathlib's base change, and
  the symmetry of the tensor product over `B` identifies the two orders.
  "`C` soit un `B`-module" is read as a commutative `B`-algebra with
  `IsScalarTower ℂ B C`, and "`B`-modules de type fini" as finite generation
  over the group algebra; both readings are this note's. Naturality in `E`
  is not stated; the pure-tensor formula (VI.8.2.2) determines the
  isomorphism. Only the normalized Jacquet module is stated.
- `Langlands.Renard.AlgebraicFamily.ParabolicFlatnessStatements`: (I) states only flatness, since the other conditions hold by
  construction; (L2) states only finite generation of the compact-open fixed
  modules; (J) has no Levi binders, which is formally more general than the
  source, a reading made in this note; the functors on morphisms are not
  bundled.
- `Langlands.Renard.AlgebraicFamily.CentralCharacterSplittingStatement`: the statement takes any group, any field, any representation
  and any central subgroup `Z`, which contains the source's case
  `Z = Z(G)`, a reading made in this note; the distinct central characters
  are given characters `χ_i`, pairwise distinct, with no continuity; the
  direct sum is the coproduct in `Rep k G`, and compatibility with the
  filtration is not stated.
- `Langlands.Renard.AlgebraicFamily.SupercuspidalFamilyEndomorphismStatement`: `B` is the published algebra of evaluation functions on `X(M)`,
  not the group algebra of `Λ(M)`; only the first paragraph of the Example is
  stated, not the consequence for the centre of `M(G)[ρ]`; the universal
  family is `B ⊗ W` rather than `W ⊗ B`, and the instance settings do not
  change the meaning.
- `Langlands.Renard.AlgebraicFamily.UniversalSpecializationStatement`: the statement is made for any group with a topology, any
  family of norm characters and any representation, smoothness not being
  needed; `B` is the algebra of evaluation functions rather than `ℂ[Λ(G)]`;
  the tensor orders are those of the published models, the fiber uses
  `ℂ` with `B` acting through `χ` rather than `B/I_χ`, and `π ⊗ χ` is the twist
  on `V` itself; only the last paragraph of the Example is stated.
- `Langlands.Aubert.General.RepresentedParabolic.LeviNormalizerWeylGroupStatements`: the statements are made over nonarchimedean local fields only,
  as in the source, and involve no topology on rational points; the
  faithfulness statement reformulates V.3.5 through norms on the centre of
  `M(F)`.

The Lean and Markdown files of the modules below were checked at
Libraries `d82893a7`, `2816ea5d`, `568f1cff`, `c0c7eab6` and `ddb0a9c0`. The six files of `Langlands.Renard.AlgebraicFamily.EndomorphismScalarStatement`, `Langlands.Renard.AlgebraicFamily.GenericIrreducibilityStatements` and `Langlands.Plancherel.compactFixedFamilyOpenness` are new
at `2816ea5d`. The RenardFamilyParabolicFunctors pair of `Langlands.Renard.AlgebraicFamily.leviInducedRepresentation` is new at
`8b14de0b`, and the sixteen files of the eight modules added after it in an
earlier update are new at `0de01f07`. The forty-eight files of the
twenty-four modules added in the previous update are new at `c0c7eab6`; their
modules first appeared in the Library at `a419cc85`. Of the ten modules added in this update,
RegularJacquetMultiplicityStatement, the pair of `Langlands.Plancherel.RegularSquareIntegrableJacquetMultiplicityStatement`, is also new at
`c0c7eab6` and was published at `a419cc85`; the eighteen files of the other
nine are new at `ddb0a9c0`, and their modules were published at `3f141257`.
Between `d82893a7` and `c0c7eab6` every other file is unchanged. Between
`c0c7eab6` and `ddb0a9c0` four files of the table changed: the
ParabolicGenericIrreducibilityStatement pair, RationalUnitaryNonvanishing.lean
and RenardFamilyParabolicFunctors.md, as described below. The table gives the
hashes at `ddb0a9c0`. Each file in the workspace equals the Library. Some
frozen bundles differ from the Library:

- `RationalNormalizedInducedSpecializationStatement` also froze an earlier RationalUniversalTensorFinitenessStatement
  Markdown file; its own pair equals the Library.
- `Langlands.CentralEigenspaceSplitting.eigenSubrep` also froze unrelated filtration Markdown files that changed
  later; its own pair equals the Library.
- `Langlands.Induction.compactQuotientClause_holds` froze a wide snapshot. In it, CompactQuotientProof.md differs
  from the Library at line 70 by one sentence, "is not an input of any
  theorem" against "is not an additional input of the closing theorem". No
  publication record names this change. `Induction/Definitions.lean` also
  changed later.
- The Library UnramifiedRationalNormalizedModels pair differs from the copy
  frozen by `jacquetRepresentation`, through a later build-speed refactor that introduced
  reducible `Prop` abbreviations such as `UniversalSmoothness` and rewrote
  theorem types. The definitions cited here are unchanged. The originating
  module of the newer copy was not identified.
- The Library RationalUniversalProgeneratorComparisonProof pair differs from
  the copy frozen by `Langlands.CuspidalSupport.rationalUniversalProgeneratorComparison`. The later definition module
  "Actual norm-kernel generator fixed
  vectors and dynamic compression stability", published at
  `291705a7b40579e0118c8512a32d7f8212883f2e`, named its two local instances
  `rationalUniversalProgeneratorComparisonProofPointTopology` and
  `rationalUniversalProgeneratorComparisonProofTopologicalGroup`, and added
  one Markdown paragraph saying that the naming changes no topology,
  representation, predicate or proof.
- `Langlands.Plancherel.RationalNormalized.conjugateOutputInducedRepresentation` and `Langlands.Plancherel.ConditionalParabolicGenericIrreducibilityStatement` froze wide snapshots, many of whose unrelated
  files changed later. The own pair of `Langlands.Plancherel.RationalNormalized.conjugateOutputInducedRepresentation` equals the Library. The own
  pair of `Langlands.Plancherel.ConditionalParabolicGenericIrreducibilityStatement`, ParabolicGenericIrreducibilityStatement, equals the
  Library at `c0c7eab6` but not at `ddb0a9c0`: integration named its two
  anonymous local topology instances
  `parabolicGenericIrreducibilityPointTopology` and
  `parabolicGenericIrreducibilityStatementTopologicalSpace`, and added one
  Markdown paragraph saying that their types, values and local scopes are
  unchanged.
- `Langlands.Plancherel.CompactFixedFamilyOpennessStatement` also froze the FiniteMatrixOpennessProof pair, `Langlands.Plancherel.rationalUnitaryRegularRestriction` the
  JacquetMultiplicityIrreducibility pair, and `Langlands.Aubert.General.RationalPointFamily.rationalNormKernelPositiveForm` the
  RationalUnitaryInductionIrreducibility pair; all equal the Library. In the
  own pair of `Langlands.Plancherel.rationalUnitaryRegularRestriction`, RationalUnitaryNonvanishing.lean equals the Library
  at `c0c7eab6` but not at `ddb0a9c0`: the bundles of `Langlands.Plancherel.ParabolicGenericIrreducibilityReductionStatement` and
  `Langlands.Plancherel.RegularUnitaryTwistExistenceStatement` name its anonymous local topology instance
  `rationalUnitaryNonvanishingPointTopology`, with type and value unchanged,
  and that version is the Library's.
- `Langlands.Aubert.General.compactQuotientNormalizedInductionForm` also froze the SemisimpleInductionIrreducibility pair, equal to
  the Library, and the Exponents/SmoothContragredientCentralSpectrum pair,
  which changed later; its own pair equals the Library.
- `Langlands.Aubert.General.RepresentedParabolic.MaximalLeviSupercuspidalUnitarizableConstituentStatement` also froze the MaximalLeviReducibilityReductionStatements pair,
  whose Lean file changed later; its own pair equals the Library.
- `Langlands.Aubert.General.RepresentedParabolic.SupercuspidalUnitaryCoefficientCompactSupportReductionStatement` came with five pairs: its SupercuspidalCoefficientCompactSupportReduction
  pair and the Aubert/General pairs CartanCentralSupport,
  RationalCartanCentralSupport, RationalCuspidalCoefficientCompactSupport and
  RepresentedStandardCuspidality. `Langlands.Aubert.General.RepresentedParabolic.SupercuspidalUnitaryCoefficientCompactSupportStructuralReductionStatement` later changed all of them except
  CartanCentralSupport. It added the three-premise statement and theorem,
  kept the four-premise ones with their signatures, and named two local
  topology instances. The four changed pairs equal the copies frozen by
  `Langlands.Aubert.General.RepresentedParabolic.SupercuspidalUnitaryCoefficientCompactSupportStructuralReductionStatement`.
- `Langlands.Renard.AlgebraicFamily.GenericIrreducibilityStatements` also froze the RenardFamilyEndomorphismStatement pair, equal to
  the Library. The own pairs of `Langlands.Renard.AlgebraicFamily.EndomorphismScalarStatement`, `Langlands.Renard.AlgebraicFamily.GenericIrreducibilityStatements` and `Langlands.Plancherel.compactFixedFamilyOpenness` equal
  the Library.
- The own pair of the first version of `Langlands.Renard.AlgebraicFamily.leviInducedRepresentation` and the copy frozen by `Langlands.Renard.AlgebraicFamily.FamilyModule` contain the
  first version of RenardFamilyParabolicFunctors.md. The Library has the
  corrected Markdown of its second version; the Lean file is unchanged.
- `Langlands.Renard.AlgebraicFamily.FamilyModule` also froze an earlier version of this note, equal to the
  Library at `568f1cff`, and `notes/renard/coverage.md` and `wiki/README.md`,
  which differ from the Library. `Langlands.Renard.AlgebraicFamily.ParabolicStatements` and `Langlands.Renard.AlgebraicFamily.ParabolicFlatnessStatements` each froze both of their statement
  pairs and the RenardFamilyCategory pair, all equal to the Library.
  `Langlands.Renard.AlgebraicFamily.flatnessCriterion` also froze the RenardFamilyFixedTensorProof pair, equal to the
  Library. The own pairs of the eight modules new at `0de01f07` equal the
  Library.
- `Langlands.Aubert.General.RepresentedParabolic.LeviNormalizerWeylGroupStatements` froze a LeviNormalizerQuotientStatements Markdown file that
  differs from the Library at line 46: the frozen copy writes
  `w = g j * l(p(m))`, the Library copy `w = g j * p(l(m))`. The frozen
  expression is a harmless composition-order typo. Every other file frozen by the twenty-three modules added in the
  previous update equals the Library. Besides their own pairs, they froze the pairs of
  other new modules, the RenardFamilyCategory, RenardFamilyParabolicStatements,
  RenardFamilyParabolicFlatnessStatements, RenardFamilyFixedTensorProof,
  RenardFamilyFlatnessProof and MatrixGenerationWitness pairs, and, for
  `Langlands.Plancherel.RationalNormalized.inducedLeviNormalizationEquiv`, `Langlands.Plancherel.RationalLeviInductionOpennessStatement` and `Langlands.Plancherel.UnramifiedUniformGenerationStatement`, the
  RationalContinuousFixedBasesStatement and UnramifiedRationalFixedMatrices
  pairs. The InducedIrreducibilityOpenReduction pair is part of the bundle of
  `Langlands.Renard.AlgebraicFamily.CompactCompressionPrincipalOpen.IsGlobalCoefficientFamily`, and the DynamicLeviNormalizer pair is the own pair of
  `Langlands.GroupScheme.IsRationalLeviSubgroup.normalizerRepresentativesOfDynamicParabolic`.
- The own pairs of the eleven modules added in this update equal the Library.
  `Langlands.Plancherel.ParabolicGenericIrreducibilityReductionStatement`, `Langlands.Plancherel.RegularUnitaryTwistExistenceStatement`, `Langlands.Plancherel.UnitaryRegularParabolicIrreducibilityReductionStatement`, `Langlands.Plancherel.RegularSquareIntegrableJacquetMultiplicityReductionStatement` and `Langlands.Plancherel.schemeCenterToParabolicCenter` froze the
  same copies of three supporting pairs, which differ from the Library only
  by integration naming of local topology instances, each with one added
  Markdown paragraph saying the naming changes nothing else. In the
  ParabolicRepresentedComparison and ParabolicJacquetUnitaryRestriction pairs,
  equal to the Library at `c0c7eab6`, two anonymous instances became
  `parabolicRepresentedComparisonTopologicalSpace`,
  `parabolicRepresentedComparisonTopologicalSpace2`,
  `parabolicJacquetUnitaryRestrictionTopologicalSpace` and
  `parabolicJacquetUnitaryRestrictionTopologicalSpace2`. In the
  SelfUnitaryPieceMultiplicity pair, new at `ddb0a9c0`,
  `selfPieceAmbientPointTopology` became
  `selfUnitaryPieceAmbientPointTopology`. The second version of `Langlands.Renard.AlgebraicFamily.leviInducedRepresentation` also froze the previous
  version of this note and `notes/renard/coverage.md`, equal to the Library
  at `c0c7eab6`, and a `wiki/README.md` that differs from the Library. Every
  other file frozen by these eleven modules equals the Library.

| File under `Langlands/` | SHA256 at Library `ddb0a9c0` |
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
| `Representation/Plancherel/ParabolicGenericIrreducibilityStatement.lean` | `baaaba1b7df1943357e2a62c687bb62dfae14228a1f8471168f3b66f46716c5e` |
| `Representation/Plancherel/ParabolicGenericIrreducibilityStatement.md` | `39b1a8ac71e0c1786a345fd92ab44b7847f4d52819f93a6bce8cf3b20c7c8886` |
| `Representation/Plancherel/FiniteMatrixOpennessStatement.lean` | `8f176d39dd2583f0352028c8b36d1fc39c8f87ffb5d2eee612c86caf9a23d400` |
| `Representation/Plancherel/FiniteMatrixOpennessStatement.md` | `d1249f681edf5ccaf0c8390310421ba5ffe44377bb3b555c27955dd3dd41a173` |
| `Representation/Families/RenardFamilyStatements.lean` | `08b1db42e951221c2f706b1742d6bb08e09255e719fcb3258beebae4364b62c3` |
| `Representation/Families/RenardFamilyStatements.md` | `535b20f35c867381ddfe42fe17764dc4c376da9aedc6c3617deaa943d72a3b7d` |
| `Representation/Plancherel/FiniteMatrixOpennessProof.lean` | `49b9ed3820d9d82c94d88ee3b685e04f15656ee8e9a9c8fcbc884f55b99fe1dc` |
| `Representation/Plancherel/FiniteMatrixOpennessProof.md` | `505a18ee2aebcdb1b2c23d28785fa461f7bfeef5cf42788606c776f1d1de9a93` |
| `Representation/Plancherel/CompactFixedFamilyOpennessStatement.lean` | `eddf3aa377151464051fbc7b6dd994f943950bc7ebb219cffc8b2d7e4cbaaa2a` |
| `Representation/Plancherel/CompactFixedFamilyOpennessStatement.md` | `a7e41eff126b828502f617e87ff7090b9a5238a50c6768240a83ffe13b4b3526` |
| `Representation/Plancherel/RationalUnitaryNonvanishing.lean` | `04b0d62ff7b4a8f1052afad0e677f728703e5b691896b2445f2bdce91e7dc0c0` |
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
| `Representation/Families/RenardFamilyParabolicFunctors.md` | `d7e9c0e3923d71af8081ba7b05524d18776436de79980282b126c502aad356c2` |
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
| `Representation/Families/RenardFamilyStatementsAggregateProof.lean` | `1f5799ddf40cace389d6fcd0cb6bdd3a3c7730f7755f084e7ff3daaa6f4a089e` |
| `Representation/Families/RenardFamilyStatementsAggregateProof.md` | `12e22897b7e8d9b1359f81bafc199c65b4453ac141c661b6a0788dc69de95093` |
| `Representation/Families/InducedIrreducibilityOpenAssembly.lean` | `754d1d1e0194d8f1672f7cd741bff56b3209475496e4d1b38c116b5968859407` |
| `Representation/Families/InducedIrreducibilityOpenAssembly.md` | `90e8a2636d91a17250fac80cc525bd51e435f4c9abe77ab3536a1ad4254a392b` |
| `Representation/Families/ActualLeviUnramifiedInducedFamily.lean` | `99d6e8d283bb4d177bee588a4400b354b4463f3000acbea18baf23d664042e2c` |
| `Representation/Families/ActualLeviUnramifiedInducedFamily.md` | `08a78e622a1d6414c9e46e167bd2bda3a153956da99abd7cc91ffbe74ef65a19` |
| `Representation/Plancherel/ParabolicGenericIrreducibilityReduction.lean` | `29b1e7c242eab989573688a601550c8b30404ee6de0d7813561cdcaa4f8b6ca9` |
| `Representation/Plancherel/ParabolicGenericIrreducibilityReduction.md` | `a52ad45c5d9c22ef2da0576acb2faeb725092b5d07f4756c4d7bbdd5898edc40` |
| `Representation/Plancherel/ParabolicRegularUnitaryTwist.lean` | `3575e6a44d3cf85b978ba27aba536d2bb1bf3f378f60e2b206f21ddae47836a6` |
| `Representation/Plancherel/ParabolicRegularUnitaryTwist.md` | `2497923294a901ef94b623812bd09c98b34b6f499a8eb42ca9684d258f6344be` |
| `Representation/Plancherel/ParabolicUnitaryPointIrreducibility.lean` | `dc310d63b24181146cdd5c3822158e28b6c36ceb1eef31d233acfdd4fb142b2d` |
| `Representation/Plancherel/ParabolicUnitaryPointIrreducibility.md` | `5851cf6f1da716458ac88ded7a3fec980be5e5f38017d03fa0dc83d3ff2f02db` |
| `Representation/Plancherel/RegularJacquetMultiplicityStatement.lean` | `ae27dd27dbf29fdcca5cdb1d28a0cb47f04bc80e7fe0b09bcf37cbf26c6d51d0` |
| `Representation/Plancherel/RegularJacquetMultiplicityStatement.md` | `a9aa4429fe0f0ba42bce8f7b0b867a273a51456bf9581c20fd5335933bdb1383` |
| `Representation/Plancherel/RegularSquareIntegrableJacquetMultiplicityReduction.lean` | `b70052b9202a3150639ed9e06d98e1c63312a42d722cfae3065dc72d02b54c9f` |
| `Representation/Plancherel/RegularSquareIntegrableJacquetMultiplicityReduction.md` | `f732c4139f82924d22b591f22a33642619dd7ff9251bd99059e2747869bd972d` |
| `Representation/Plancherel/RepresentedInductionComparison.lean` | `315c1d8a88804deb2505f3028672855a91271d113db188100c7023f4bd471505` |
| `Representation/Plancherel/RepresentedInductionComparison.md` | `df22e195b9a11f60e9511064211290388747a2ca3335f6cf0cd241b1d83a4267` |
| `Representation/Plancherel/ParabolicSquareIntegrableModCenter.lean` | `b6869368390b746ad25d1135f59bcacf3c3a29aa144a0b65246e6b7472dba732` |
| `Representation/Plancherel/ParabolicSquareIntegrableModCenter.md` | `2290bd0c69d777d9b643ad8986271193ff45dbea11b7635dfc7ef578f1fe4caf` |

## Scope

This note covers VI.8 only. The Theorem that ends VI.7, on PDF p.193, and
VI.9 are outside it. The unpublished assertions are part of the whole-book
[coverage](coverage.md). This note declares no section, chapter or book completion.
