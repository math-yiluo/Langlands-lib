/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DerivedDirectImageOpenCoherenceData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ModuleOpenPasting.ModuleDirectImageOpenPasting
import WeilConjectures.AlgebraicGeometry.Derived.DerivedExchangeModuleTermwiseSupplement

/-! Source: blueprint composition isomorphism and its canonicity and associativity. -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors Functor.rightDerivedFunctorObjQIso
  Functor.rightDerivedFunctorUnitQ

namespace AlgebraicGeometry.ProEtale.CondensedRing
attribute [local irreducible] upperStar lowerStar upperStarLowerStarAdjunction
  upperStarComp directImageOpenRestriction derivedDirectImageOpenRestriction
  openCoherencePullbackSquare

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

private theorem canonical_comparison
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {j : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {i : X' ⟶ X} (sq : IsPullback i f' f j) :
    (mateEquiv (upperStarLowerStarAdjunction Λ f)
      (upperStarLowerStarAdjunction Λ f')
      (TwoSquare.mk _ _ _ _
        (((upperStarComp Λ i f).symm ≪≫ upperStarCongr Λ sq.w ≪≫
          upperStarComp Λ f' j).inv))) =
      directImageOpenRestriction Λ sq.toCommSq := by
  simp only [directImageOpenRestriction, openCoherencePullbackSquare,
    Iso.trans_inv, Iso.symm_inv, upperStarCongr,
    eqToIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]

private theorem coprojection_eq
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (V : X.ProEt) :
    openCoherenceSectionCoprojection Λ j M V = ModuleOpenPasting.coprojection Λ j M V := by
  rfl

private theorem sectionArrow_eq
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {j : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {i : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion i]
    (sq : IsPullback i f' f j) (V : Y'.ProEt) :
    openCoherenceSectionArrow sq.toCommSq V = ModuleOpenPasting.sectionArrow f j f' i sq V := by
  rfl

private theorem sectionwise_normalization
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {j : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {i : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion i]
    (sq : IsPullback i f' f j) (β : ModuleOpenPasting.Comparisons Λ)
    (hsec : ModuleOpenPasting.Sectionwise Λ β)
    (hb : (β f j f' i sq).hom = directImageOpenRestriction Λ sq.toCommSq) :
    OpenCoherenceSectionwise Λ sq.toCommSq := by
  refine ⟨?_, ?_, ?_⟩
  · intro M V
    rw [coprojection_eq]
    exact hsec.1 j M V
  · intro M V
    rw [coprojection_eq]
    exact hsec.1 i M V
  · intro M V s
    rw [coprojection_eq, coprojection_eq, sectionArrow_eq, ← hb]
    exact hsec.2 f j f' i sq M V s

private theorem underived_normalization
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {j : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {i : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion i]
    (sq : IsPullback i f' f j) :
    IsIso (directImageOpenRestriction Λ sq.toCommSq) ∧
      OpenCoherenceSectionwise Λ sq.toCommSq := by
  obtain ⟨β, hsec, _, _, _, _, _, hcan⟩ :=
    ModuleOpenPasting.moduleDirectImageOpenPasting_canonical Λ
  have hb : (β f j f' i sq).hom = directImageOpenRestriction Λ sq.toCommSq :=
    (hcan f j f' i sq).trans (canonical_comparison Λ sq)
  have hi : IsIso (directImageOpenRestriction Λ sq.toCommSq) := by
    rw [← hb]
    infer_instance
  exact ⟨hi, sectionwise_normalization Λ sq β hsec hb⟩

private theorem cancel_evaluations
    {C : Type*} [Category C] {A B D E : C} (e : A ≅ B) (d : D ≅ E)
    {a : A ⟶ D} {b : B ⟶ E} (h : e.inv ≫ a = b ≫ d.inv) :
    a ≫ d.hom = e.hom ≫ b := by
  apply (cancel_epi e.inv).mp
  rw [reassoc_of% h]
  simp only [Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]

private theorem normalized_mate
    {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
    [HasDerivedCategory C₁] [HasDerivedCategory C₂]
    [HasDerivedCategory C₃] [HasDerivedCategory C₄]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C₁]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C₃]
    {L : C₂ ⥤ C₁} {R : C₁ ⥤ C₂} {L' : C₄ ⥤ C₃} {R' : C₃ ⥤ C₄}
    {G : C₂ ⥤ C₄} {H : C₁ ⥤ C₃}
    [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [G.Additive] [H.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits L]
    [CategoryTheory.Limits.PreservesFiniteColimits L]
    [CategoryTheory.Limits.PreservesFiniteLimits L']
    [CategoryTheory.Limits.PreservesFiniteColimits L']
    [CategoryTheory.Limits.PreservesFiniteLimits G]
    [CategoryTheory.Limits.PreservesFiniteColimits G]
    [CategoryTheory.Limits.PreservesFiniteLimits H]
    [CategoryTheory.Limits.PreservesFiniteColimits H]
    (adj : L ⊣ R) (adj' : L' ⊣ R') (e : G ⋙ L' ≅ L ⋙ H)
    (I : CochainComplex C₁ ℤ) [I.IsKInjective]
    [H.PreservesKInjectiveComplexes] :
    (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
      adj'.mapDerivedCategoryRightDerivedAdjunction
      (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategoryCompIso G L' ≪≫
        Functor.mapDerivedCategoryNatIso e ≪≫
        (Functor.mapDerivedCategoryCompIso L H).symm).hom)).app
        (DerivedCategory.Q.obj I) ≫
      R'.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app I) =
    G.mapDerivedCategory.map (R.rightDerivedFunctorObjQIso I).hom ≫
      G.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ e.hom)) (.up ℤ)).app I) ≫
      (R'.rightDerivedFunctorObjQIso ((H.mapHomologicalComplex (.up ℤ)).obj I)).inv := by
  have h := AlgebraicGeometry.Etale.derivedExchangeUnitQ adj adj' e I
  rw [Functor.rightDerivedFunctorUnitQ_eq, Functor.rightDerivedFunctorUnitQ_eq] at h
  apply cancel_evaluations
    (G.mapDerivedCategory.mapIso (R.rightDerivedFunctorObjQIso I))
    (R'.rightDerivedFunctor.mapIso (H.mapDerivedCategoryFactors.app I))
  simpa only [CategoryTheory.Functor.mapIso_inv, Iso.app_inv, Category.assoc] using h

private theorem normalized_mate_maps
    {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
    [HasDerivedCategory C₁] [HasDerivedCategory C₂]
    [HasDerivedCategory C₃] [HasDerivedCategory C₄]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C₁]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C₃]
    {L : C₂ ⥤ C₁} {R : C₁ ⥤ C₂} {L' : C₄ ⥤ C₃} {R' : C₃ ⥤ C₄}
    {G : C₂ ⥤ C₄} {H : C₁ ⥤ C₃}
    [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [G.Additive] [H.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits L]
    [CategoryTheory.Limits.PreservesFiniteColimits L]
    [CategoryTheory.Limits.PreservesFiniteLimits L']
    [CategoryTheory.Limits.PreservesFiniteColimits L']
    [CategoryTheory.Limits.PreservesFiniteLimits G]
    [CategoryTheory.Limits.PreservesFiniteColimits G]
    [CategoryTheory.Limits.PreservesFiniteLimits H]
    [CategoryTheory.Limits.PreservesFiniteColimits H]
    (adj : L ⊣ R) (adj' : L' ⊣ R') (e : G ⋙ L' ≅ L ⋙ H)
    (β : R ⋙ G ⟶ H ⋙ R')
    (ρ : R.rightDerivedFunctor ⋙ G.mapDerivedCategory ⟶
      H.mapDerivedCategory ⋙ R'.rightDerivedFunctor)
    (hβ : β = (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ e.hom)))
    (hρ : ρ = (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
      adj'.mapDerivedCategoryRightDerivedAdjunction
      (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategoryCompIso G L' ≪≫
        Functor.mapDerivedCategoryNatIso e ≪≫
        (Functor.mapDerivedCategoryCompIso L H).symm).hom)))
    (I : CochainComplex C₁ ℤ) [I.IsKInjective]
    [H.PreservesKInjectiveComplexes] :
    ρ.app (DerivedCategory.Q.obj I) ≫
      R'.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app I) =
    G.mapDerivedCategory.map (R.rightDerivedFunctorObjQIso I).hom ≫
      G.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex β (.up ℤ)).app I) ≫
      (R'.rightDerivedFunctorObjQIso ((H.mapHomologicalComplex (.up ℤ)).obj I)).inv := by
  subst β ρ
  exact normalized_mate adj adj' e I

private theorem normalized_mate_isIso
    {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
    [HasDerivedCategory C₁] [HasDerivedCategory C₂]
    [HasDerivedCategory C₃] [HasDerivedCategory C₄]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C₁]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C₃]
    {L : C₂ ⥤ C₁} {R : C₁ ⥤ C₂} {L' : C₄ ⥤ C₃} {R' : C₃ ⥤ C₄}
    {G : C₂ ⥤ C₄} {H : C₁ ⥤ C₃}
    [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [G.Additive] [H.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits L]
    [CategoryTheory.Limits.PreservesFiniteColimits L]
    [CategoryTheory.Limits.PreservesFiniteLimits L']
    [CategoryTheory.Limits.PreservesFiniteColimits L']
    [CategoryTheory.Limits.PreservesFiniteLimits G]
    [CategoryTheory.Limits.PreservesFiniteColimits G]
    [CategoryTheory.Limits.PreservesFiniteLimits H]
    [CategoryTheory.Limits.PreservesFiniteColimits H]
    (adj : L ⊣ R) (adj' : L' ⊣ R') (e : G ⋙ L' ≅ L ⋙ H)
    (β : R ⋙ G ⟶ H ⋙ R')
    (ρ : R.rightDerivedFunctor ⋙ G.mapDerivedCategory ⟶
      H.mapDerivedCategory ⋙ R'.rightDerivedFunctor)
    (hβ : β = (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ e.hom)))
    (hρ : ρ = (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
      adj'.mapDerivedCategoryRightDerivedAdjunction
      (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategoryCompIso G L' ≪≫
        Functor.mapDerivedCategoryNatIso e ≪≫
        (Functor.mapDerivedCategoryCompIso L H).symm).hom)))
    [H.PreservesKInjectiveComplexes] [IsIso β] : IsIso ρ := by
  apply (NatTrans.isIso_iff_isIso_app ρ).mpr
  intro K
  obtain ⟨I, hI, ⟨s⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective K
  have h := normalized_mate_maps adj adj' e β ρ hβ hρ I
  have : IsIso ((NatTrans.mapHomologicalComplex β (.up ℤ)).app I) :=
    ((NatIso.mapHomologicalComplex (asIso β) (.up ℤ)).app I).isIso_hom
  have : IsIso (ρ.app (DerivedCategory.Q.obj I) ≫
      R'.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app I)) := by
    rw [h]
    infer_instance
  have : IsIso (ρ.app (DerivedCategory.Q.obj I)) :=
    IsIso.of_isIso_comp_right _
      (R'.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app I))
  exact (NatTrans.isIso_app_iff_of_iso ρ s).mpr this

attribute [local semireducible] directImageOpenRestriction derivedDirectImageOpenRestriction
  openCoherencePullbackSquare

-- Instance search must find the same `EssentiallySmall` proof as `normalized_mate_maps` does;
-- otherwise the kernel check of the instantiated equation times out.
attribute [-instance] InternalAbelianSheafModule.comparison_essentiallySmall in
private theorem representative_normalization
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {j : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {i : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion i]
    (sq : IsPullback i f' f j) :
    letI : Preadditive
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
      (Mod.instAbelian (condensedRingObj Λ X)).toPreadditive
    letI : Preadditive
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :=
      (Mod.instAbelian (condensedRingObj Λ Y)).toPreadditive
    letI : Preadditive
      (Mod (Sheaf (Scheme.ProEt.topology X') Ab.{u + 1}) (condensedRingObj Λ X')) :=
      (Mod.instAbelian (condensedRingObj Λ X')).toPreadditive
    letI : Preadditive
      (Mod (Sheaf (Scheme.ProEt.topology Y') Ab.{u + 1}) (condensedRingObj Λ Y')) :=
      (Mod.instAbelian (condensedRingObj Λ Y')).toPreadditive
    ∀ (I : CochainComplex
    (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ)
    [I.IsKInjective],
    (derivedDirectImageOpenRestriction Λ sq.toCommSq).app (DerivedCategory.Q.obj I) ≫
        (lowerStar Λ f').rightDerivedFunctor.map
        ((upperStar Λ i).mapDerivedCategoryFactors.hom.app I) =
      (upperStar Λ j).mapDerivedCategory.map
        ((lowerStar Λ f).rightDerivedFunctorObjQIso I).hom ≫
        (upperStar Λ j).mapDerivedCategoryFactors.hom.app
        (((lowerStar Λ f).mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex
          (directImageOpenRestriction Λ sq.toCommSq) (.up ℤ)).app I) ≫
        ((lowerStar Λ f').rightDerivedFunctorObjQIso
        (((upperStar Λ i).mapHomologicalComplex (.up ℤ)).obj I)).inv := by
  intro I hI
  have h := normalized_mate_maps (upperStarLowerStarAdjunction Λ f)
    (upperStarLowerStarAdjunction Λ f') (openCoherencePullbackSquare Λ sq.toCommSq)
    (directImageOpenRestriction Λ sq.toCommSq)
    (derivedDirectImageOpenRestriction Λ sq.toCommSq) rfl rfl I
  exact h

private theorem derived_invertible
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {j : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {i : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion i]
    (sq : IsPullback i f' f j) :
    IsIso (derivedDirectImageOpenRestriction Λ sq.toCommSq) := by
  obtain ⟨hi, _⟩ := underived_normalization Λ sq
  have := hi
  exact normalized_mate_isIso (upperStarLowerStarAdjunction Λ f)
    (upperStarLowerStarAdjunction Λ f') (openCoherencePullbackSquare Λ sq.toCommSq)
    (directImageOpenRestriction Λ sq.toCommSq)
    (derivedDirectImageOpenRestriction Λ sq.toCommSq) rfl rfl

/-- Canonical derived open restriction and its representative normalization.
Source: blueprint composition isomorphism; Canonicity and associativity;
Stacks Tags 08BJ, 070I, 070Y and 0D6E.
(blueprint: lem-sfb-derived-open-restriction-normalization).

Proof: The module open-pasting construction betaMap is the mate of the canonical pullback
square: betaMap_formalism and formalism_sqIso identify it with directImageOpenRestriction.
Its section formula gives exactly the coprojections and fibre-product arrow in
OpenCoherenceSectionwise; its inverse follows from the open-slice equivalence. For a
K-injective I, restriction along i is K-injective because it has exact extension by zero
as left adjoint. Apply derivedExchangeUnitQ to the two exact-left adjunctions and the
canonical upperStar square. Replace each right-derived unit on a K-injective by the
inverse evaluation isomorphism and cancel these isomorphisms. This yields the stated
representative formula. Its right-hand side is a composite of isomorphisms, so cancellation
proves invertibility at Q(I). Every derived object is isomorphic to a K-injective
representative; naturality transports invertibility to all objects.
The coprojections and section formula include empty opens and identity morphisms.
-/
theorem derivedOpenRestrictionNormalization
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {j : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {i : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion i]
    (sq : IsPullback i f' f j) : DirectImageRestrictionNormalized Λ sq.toCommSq := by
  obtain ⟨hi, hs⟩ := underived_normalization Λ sq
  exact ⟨derived_invertible Λ sq, hi, hs, representative_normalization Λ sq⟩

end AlgebraicGeometry.ProEtale.CondensedRing
