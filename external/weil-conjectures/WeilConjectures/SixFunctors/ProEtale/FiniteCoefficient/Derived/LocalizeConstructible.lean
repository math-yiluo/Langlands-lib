/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ClosedImmersionStages
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Localization
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Stability

/-!
# The closed-support triangle on bounded constructible pro-étale complexes

Let `k` be a field, `X` a scheme of finite type over `k`, `i : Z ⟶ X` a closed immersion and
`j : U ⟶ X` the complementary (quasi-compact) open immersion, and let `Λ` be a finite ring
killed by an integer invertible in `k`: the finite coefficient stage `A_{E,n}` of blueprint
`lemma-local-cohomology-right-adjoint--2`. This file proves clauses (1)–(4) of that proposition at
the finite stage, on the bounded constructible pro-étale complexes `Dᵇc_proét(-, Λ)`:

1. `Rj_*` carries `Dᵇc_proét(U, Λ)` into `Dᵇc_proét(X, Λ)`
   (`ProEtale.boundedConstructible_rightDerivedFunctor_lowerStar_of_isOpenImmersion`);
2. the right adjoint `Ri^!` of `Ri_*` on the ambient categories
   (`AlgebraicGeometry.ProEtale.derivedLowerStarClosedUpperShriekAdjunction`) carries
   `Dᵇc_proét(X, Λ)` into `Dᵇc_proét(Z, Λ)`
   (`AlgebraicGeometry.ProEtale.boundedConstructible_closedUpperShriek_rightDerivedFunctor_obj`),
   so `i_* : Dᵇc_proét(Z, Λ) ⥤ Dᵇc_proét(X, Λ)` has a right adjoint
   (`AlgebraicGeometry.ProEtale.boundedConstructibleClosedUpperShriekAdjunction`);
3. for `K ∈ Dᵇc_proét(X, Λ)` the closed-support triangle
   `i_* Ri^! K ⟶ K ⟶ Rj_* j^* K ⟶` has its three vertices in `Dᵇc_proét`
   (`AlgebraicGeometry.ProEtale.boundedConstructible_closedSupportTriangle_obj`); its existence,
   the uniqueness of its third arrow and its functoriality hold for all `K`
   (`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Localization`);
4. `Ri^! Rj_* = 0`, and the unit `Q ⟶ Ri^! i_* Q` is an isomorphism
   (`AlgebraicGeometry.ProEtale.isIso_boundedConstructibleClosedUpperShriekAdjunction_unit_app`).

The direct images of bounded constructible complexes are bounded constructible by blueprint
`proposition-open-direct-image-preserves-finite`
(`AlgebraicGeometry.ProEtale.boundedConstructible_rightDerivedLowerStar`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

variable {Λ : Type (u + 1)} [CommRing Λ] {Z U X : Scheme.{u}}

/-- The pullback `D(g^*)` of pro-étale complexes preserves bounded constructibility: a bounded
constructible complex is `ν^* K'` for a bounded constructible étale complex `K'`, `ν^*`
commutes with the pullbacks (`AlgebraicGeometry.ProEtale.comparisonUpperStarCompUpperStarIso`),
and the étale pullback preserves bounded constructibility. -/
lemma DerivedCategory.boundedConstructible.mapDerivedCategory_upperStar {Y : Scheme.{u}}
    (g : Y ⟶ X) {K : _root_.DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
      (D((g)^*[ModuleCat.{u + 1} Λ]).obj K) := by
  obtain ⟨K', hK', ⟨e⟩⟩ := hK
  exact ⟨_, hK'.mapDerivedCategory_upperStar g,
    ⟨((Etale.upperStar _ g).mapDerivedCategoryCompIso _).app K' ≪≫
      (Functor.mapDerivedCategoryNatIso
        (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) g).symm).app K' ≪≫
      ((comparisonUpperStar _ X).mapDerivedCategoryCompIso _).symm.app K' ≪≫
      D((g)^*[ModuleCat.{u + 1} Λ]).mapIso e⟩⟩

variable (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]

/-- For a closed immersion `i` with quasi-compact open complement `j`, `Ri^! K` is the pullback
`D(i^*)` of `Ri_* Ri^! K`: `Ri_*` is `D(i_*)`, `i_*` being exact, and the counit
`i^* i_* ⟶ 𝟭` is an isomorphism. -/
noncomputable def closedUpperShriekIsoMapDerivedCategoryUpperStar
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (M : _root_.DerivedCategory (Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} Λ))) :
    M ≅ D((i)^*[ModuleCat.{u + 1} Λ]).obj (R((i)_*[ModuleCat.{u + 1} Λ]).obj M) :=
  have := preservesFiniteColimits_lowerStar_of_isCompl (R := Λ) i j hij
  have : IsIso (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).counit :=
    isIso_upperStarLowerStarAdjunction_counit (ModuleCat.{u + 1} Λ) i
  (asIso (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryAdjunction
    ).counit.app M)).symm ≪≫ D((i)^*[ModuleCat.{u + 1} Λ]).mapIso
      (((i)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorIsoMapDerivedCategory.app M).symm

section Finite

variable [Finite Λ] {k : Type u} [Field k] (N : ℕ) (hN : (N : k) ≠ 0) (hΛ : (N : Λ) = 0)
  (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s] [QuasiCompact s]

omit [IsClosedImmersion i] [QuasiCompact j] [Finite Λ] in
/-- The integer `N` kills every `Λ`-module. -/
lemma nsmul_id_eq_zero (hΛ : (N : Λ) = 0) (M : ModuleCat.{u + 1} Λ) : N • 𝟙 M = 0 := by
  ext x
  change N • x = 0
  rw [← Nat.cast_smul_eq_nsmul Λ, hΛ, zero_smul]

include hN hΛ s

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`, clause (1) at the finite stage `A_{E,n}`:
for an open immersion `j : U ⟶ X` into a scheme of finite type over `k` and a finite ring `Λ` killed
by an integer invertible in `k`, `Rj_*` carries `Dᵇc_proét(U, Λ)` into `Dᵇc_proét(X, Λ)`. This is
the case of an open immersion of
`AlgebraicGeometry.ProEtale.boundedConstructible_rightDerivedLowerStar`
(blueprint `proposition-open-direct-image-preserves-finite`). -/
theorem boundedConstructible_rightDerivedFunctor_lowerStar_of_isOpenImmersion
    {G : _root_.DerivedCategory (Sheaf (ProEt.topology U) (ModuleCat.{u + 1} Λ))}
    (hG : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) U G) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
      (R((j)_*[ModuleCat.{u + 1} Λ]).obj G) :=
  boundedConstructible_rightDerivedLowerStar Λ N hN (nsmul_id_eq_zero N hΛ)
    s j hG

omit [QuasiCompact j] in
/-- The direct image `Ri_*` along a closed immersion carries `Dᵇc_proét(Z, Λ)` into
`Dᵇc_proét(X, Λ)` (`AlgebraicGeometry.ProEtale.boundedConstructible_rightDerivedLowerStar`). -/
theorem boundedConstructible_rightDerivedFunctor_lowerStar_of_isClosedImmersion
    {M : _root_.DerivedCategory (Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} Λ))}
    (hM : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Z M) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
      (R((i)_*[ModuleCat.{u + 1} Λ]).obj M) :=
  boundedConstructible_rightDerivedLowerStar Λ N hN (nsmul_id_eq_zero N hΛ)
    s i hM

omit hN hΛ s [Finite Λ] in
/-- The pullback `Lj^*` preserves bounded constructibility of pro-étale complexes. -/
lemma boundedConstructible_leftDerivedFunctor_upperStar_obj {Y : Scheme.{u}} (g : Y ⟶ X)
    {K : _root_.DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Y
      (L((g)^*[ModuleCat.{u + 1} Λ]).obj K) :=
  (DerivedCategory.boundedConstructible _ Y).prop_of_iso
    ((leftDerivedUpperStarIsoMapDerivedCategory _ g).app K).symm
    (hK.mapDerivedCategory_upperStar g)

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`, clause (3) at the finite stage `A_{E,n}`:
for `K ∈ Dᵇc_proét(X, Λ)`, the first vertex `Ri_* Ri^! K` of the closed-support triangle is bounded
constructible. The other two vertices `K` and `Rj_* j^* K` are
(`ProEtale.boundedConstructible_rightDerivedFunctor_lowerStar_of_isOpenImmersion`),
and bounded constructible complexes form a triangulated subcategory
(`AlgebraicGeometry.ProEtale.DerivedCategory.isTriangulated_boundedConstructible`). -/
theorem boundedConstructible_rightDerivedFunctor_lowerStar_obj_closedUpperShriek
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    {K : _root_.DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
      (R((i)_*[ModuleCat.{u + 1} Λ]).obj
        ((closedUpperShriek (ModuleCat.{u + 1} Λ) i j).rightDerivedFunctor.obj K)) := by
  obtain ⟨w, hw⟩ := exists_distTriang_derivedLowerStarClosedUpperShriekAdjunction_counit i j hij K
  exact (DerivedCategory.boundedConstructible _ X).ext_of_isTriangulatedClosed₁ _ hw hK
    (boundedConstructible_rightDerivedFunctor_lowerStar_of_isOpenImmersion j N hN hΛ s
      (boundedConstructible_leftDerivedFunctor_upperStar_obj j hK))

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`, clause (2) at the finite stage `A_{E,n}`:
the right adjoint `Ri^!` of `Ri_*` on the ambient categories
(`AlgebraicGeometry.ProEtale.derivedLowerStarClosedUpperShriekAdjunction`, blueprint
`lemma-local-cohomology-right-adjoint--1`) carries `Dᵇc_proét(X, Λ)` into `Dᵇc_proét(Z, Λ)`: in the
closed-support triangle the outer vertices `K` and `Rj_* j^* K` are bounded constructible, hence
so is `Ri_* Ri^! K`, and `Ri^! K ≅ i^* Ri_* Ri^! K`. -/
theorem boundedConstructible_closedUpperShriek_rightDerivedFunctor_obj
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    {K : _root_.DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Z
      ((closedUpperShriek (ModuleCat.{u + 1} Λ) i j).rightDerivedFunctor.obj K) :=
  (DerivedCategory.boundedConstructible _ Z).prop_of_iso
    (closedUpperShriekIsoMapDerivedCategoryUpperStar i j hij _).symm
    ((boundedConstructible_rightDerivedFunctor_lowerStar_obj_closedUpperShriek i j N hN hΛ s hij
      hK).mapDerivedCategory_upperStar i)

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`, clause (3) at the finite stage `A_{E,n}`:
for `K ∈ Dᵇc_proét(X, Λ)` all three vertices of the closed-support triangle
`Ri_* Ri^! K ⟶ K ⟶ Rj_* Lj^* K ⟶` (`AlgebraicGeometry.ProEtale.closedSupportTriangle`) are
bounded constructible. The triangle is distinguished for a unique third arrow, and functorial in
`K` (`AlgebraicGeometry.ProEtale.existsUnique_distTriang_closedSupportTriangle`,
`AlgebraicGeometry.ProEtale.existsUnique_triangleHom_closedSupportTriangle`). -/
theorem boundedConstructible_closedSupportTriangle_obj
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    {K : _root_.DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) (w) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
        (closedSupportTriangle i j hij K w).obj₁ ∧
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
        (closedSupportTriangle i j hij K w).obj₂ ∧
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
        (closedSupportTriangle i j hij K w).obj₃ :=
  ⟨boundedConstructible_rightDerivedFunctor_lowerStar_obj_closedUpperShriek i j N hN hΛ s hij hK,
    hK, boundedConstructible_rightDerivedFunctor_lowerStar_of_isOpenImmersion j N hN hΛ s
      (boundedConstructible_leftDerivedFunctor_upperStar_obj j hK)⟩

/-- The direct image `i_* : Dᵇc_proét(Z, Λ) ⥤ Dᵇc_proét(X, Λ)` along a closed immersion. -/
noncomputable def boundedConstructibleRightDerivedLowerStar :
    (DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Z).FullSubcategory ⥤
      (DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X).FullSubcategory :=
  (DerivedCategory.boundedConstructible _ X).lift
    ((DerivedCategory.boundedConstructible _ Z).ι ⋙ R((i)_*[ModuleCat.{u + 1} Λ]))
    (fun M ↦ boundedConstructible_rightDerivedFunctor_lowerStar_of_isClosedImmersion i N hN hΛ s
      M.2)

/-- The exceptional inverse image `Ri^! : Dᵇc_proét(X, Λ) ⥤ Dᵇc_proét(Z, Λ)` along a closed
immersion: the restriction of the right derived functor of the sheaves with support
(`AlgebraicGeometry.ProEtale.boundedConstructible_closedUpperShriek_rightDerivedFunctor_obj`). -/
noncomputable def boundedConstructibleClosedUpperShriek
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) :
    (DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X).FullSubcategory ⥤
      (DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Z).FullSubcategory :=
  (DerivedCategory.boundedConstructible _ Z).lift
    ((DerivedCategory.boundedConstructible _ X).ι ⋙
      (closedUpperShriek (ModuleCat.{u + 1} Λ) i j).rightDerivedFunctor)
    (fun K ↦ boundedConstructible_closedUpperShriek_rightDerivedFunctor_obj i j N hN hΛ s hij K.2)

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`, clause (2) at the finite stage `A_{E,n}`:
the direct image `i_* : Dᵇc_proét(Z, Λ) ⥤ Dᵇc_proét(X, Λ)` along a closed immersion has the right
adjoint `Ri^!`, the restriction of the ambient adjunction
`AlgebraicGeometry.ProEtale.derivedLowerStarClosedUpperShriekAdjunction`. -/
noncomputable def boundedConstructibleClosedUpperShriekAdjunction
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) :
    boundedConstructibleRightDerivedLowerStar i N hN hΛ s ⊣
      boundedConstructibleClosedUpperShriek i j N hN hΛ s hij :=
  (derivedLowerStarClosedUpperShriekAdjunction i j hij).restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _) (Iso.refl _)
    (Iso.refl _)

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`, clause (4) at the finite stage `A_{E,n}`:
the unit `Q ⟶ Ri^! i_* Q` of the adjunction on `Dᵇc_proét`
(`AlgebraicGeometry.ProEtale.boundedConstructibleClosedUpperShriekAdjunction`) is an
isomorphism, `i_*` being fully faithful (blueprint `lemma-local-cohomology-right-adjoint--1`,
`AlgebraicGeometry.ProEtale.isIso_unit_app_boundedConstructible`). -/
theorem isIso_boundedConstructibleClosedUpperShriekAdjunction_unit_app
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (Q : (DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Z).FullSubcategory) :
    IsIso ((boundedConstructibleClosedUpperShriekAdjunction i j N hN hΛ s hij).unit.app Q) :=
  isIso_unit_app_boundedConstructible i _ _ Q

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`, clause (4) at the finite stage `A_{E,n}`:
`Ri^! Rj_* G = 0` for `G ∈ Dᵇc_proét(U, Λ)`; this holds for every `G ∈ D(U_proét, Λ)`
(`ProEtale.isZero_closedUpperShriek_rightDerivedFunctor_obj_rightDerivedFunctor_lowerStar`). -/
theorem isZero_boundedConstructibleClosedUpperShriek_obj
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    {G : _root_.DerivedCategory (Sheaf (ProEt.topology U) (ModuleCat.{u + 1} Λ))}
    (hG : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) U G) :
    IsZero ((boundedConstructibleClosedUpperShriek i j N hN hΛ s hij).obj
      ⟨_, boundedConstructible_rightDerivedFunctor_lowerStar_of_isOpenImmersion j N hN hΛ s hG⟩) :=
  IsZero.of_full_of_faithful_of_isZero (DerivedCategory.boundedConstructible _ Z).ι _
    (isZero_closedUpperShriek_rightDerivedFunctor_obj_rightDerivedFunctor_lowerStar i j hij G)

omit hN hΛ s in
/-- The bijection `Hom(P, Ri^! K) ≃ Hom(P, Rᵉˣi^! K)` between maps into the right adjoint of
`Ri_*` (`AlgebraicGeometry.ProEtale.derivedLowerStarClosedUpperShriekAdjunction`) and maps into
the exceptional inverse image `Rᵉˣi^!` of blueprint `theorem-f-shriek-ell-adic-coefficients--4` (vi)
(`AlgebraicGeometry.ProEtale.rightDerivedUpperShriek`), for `P` bounded below of étale origin and
`K` bounded below: both are `Hom(Ri_! P, K)`, as `Ri_! = Ri_*` for a closed immersion
(`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar`). -/
noncomputable def closedUpperShriekHomEquivRightDerivedUpperShriek [HasCompactification i]
    [CompactSpace X]
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    {P : _root_.DerivedCategory (Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} Λ))}
    (hP : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) Z P)
    {K : _root_.DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : _root_.DerivedCategory.TStructure.t.plus K) :
    (P ⟶ (closedUpperShriek (ModuleCat.{u + 1} Λ) i j).rightDerivedFunctor.obj K) ≃
      (P ⟶ (R(i)^![Λ]).obj K) :=
  ((derivedLowerStarClosedUpperShriekAdjunction i j hij).homEquiv P K).symm.trans <|
    ((rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar _ i).app P).homFromEquiv.symm.trans
      (rightDerivedUpperShriekHomEquiv i hP hK)

omit hN hΛ s in
lemma closedUpperShriekHomEquivRightDerivedUpperShriek_naturality [HasCompactification i]
    [CompactSpace X]
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    {P P' : _root_.DerivedCategory (Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} Λ))}
    (hP : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) Z P)
    (hP' : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) Z P')
    {K : _root_.DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : _root_.DerivedCategory.TStructure.t.plus K) (φ : P ⟶ P')
    (x : P' ⟶ (closedUpperShriek (ModuleCat.{u + 1} Λ) i j).rightDerivedFunctor.obj K) :
    closedUpperShriekHomEquivRightDerivedUpperShriek i j hij hP hK (φ ≫ x) =
      φ ≫ closedUpperShriekHomEquivRightDerivedUpperShriek i j hij hP' hK x := by
  simp only [closedUpperShriekHomEquivRightDerivedUpperShriek, Equiv.trans_apply,
    Iso.homFromEquiv_symm_apply, Adjunction.homEquiv_naturality_left_symm]
  rw [← rightDerivedUpperShriekHomEquiv_naturality_left i hP hP' hK]
  have hθ := ((rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
    (ModuleCat.{u + 1} Λ) i).hom.naturality φ)
  simp only [Iso.app_hom]
  rw [← reassoc_of% hθ]

/-- Blueprint `lemma-local-cohomology-right-adjoint--2`, clause (2) at the finite stage `A_{E,n}`:
on `Dᵇc_proét(X, Λ)` the right adjoint `Ri^!` of `Ri_*` is the exceptional inverse image of
blueprint `theorem-f-shriek-finite-coefficients` (`theorem-f-shriek-ell-adic-coefficients--4` (vi),
`AlgebraicGeometry.ProEtale.rightDerivedUpperShriek`), by uniqueness of right adjoints: both
represent `P ↦ Hom(Ri_* P, K)` on the complexes `P` bounded below of étale origin
(`AlgebraicGeometry.ProEtale.closedUpperShriekHomEquivRightDerivedUpperShriek`), and both objects
are of this kind. -/
theorem nonempty_iso_closedUpperShriek_rightDerivedFunctor_obj_rightDerivedUpperShriek_obj
    [HasCompactification i] [CompactSpace X]
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    {K : _root_.DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K) :
    Nonempty ((closedUpperShriek (ModuleCat.{u + 1} Λ) i j).rightDerivedFunctor.obj K ≅
      (R(i)^![Λ]).obj K) := by
  have hE := (boundedConstructible_closedUpperShriek_rightDerivedFunctor_obj i j N hN hΛ s hij
    hK).plusEtaleOrigin
  have hE' := plusEtaleOrigin_rightDerivedUpperShriek_obj i hK.plusEtaleOrigin.plus
  set e := fun {P} (hP : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) Z P) ↦
    closedUpperShriekHomEquivRightDerivedUpperShriek i j hij hP hK.plusEtaleOrigin.plus
  refine ⟨⟨e hE (𝟙 _), (e hE').symm (𝟙 _), (e hE).injective ?_, ?_⟩⟩
  · rw [closedUpperShriekHomEquivRightDerivedUpperShriek_naturality i j hij hE hE',
      Equiv.apply_symm_apply, Category.comp_id]
  · rw [← closedUpperShriekHomEquivRightDerivedUpperShriek_naturality i j hij hE' hE,
      Category.comp_id]
    exact Equiv.apply_symm_apply (e hE') _

end Finite

end ProEtale

end AlgebraicGeometry
