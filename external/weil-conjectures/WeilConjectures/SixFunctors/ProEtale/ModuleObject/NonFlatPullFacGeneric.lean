/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.CompExact
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.NonFlatPullFacConjugate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralDerivedIso

/-!
# Compatibility of isomorphisms of left derived functors with the counits

This file shows that several isomorphisms between total left derived functors are compatible
with the counits `Qh ⋙ L(G) ⟶ G ⋙ Qh`:

* `CategoryTheory.Functor.leftDerivedFunctorCompMapDerivedCategoryIso_hom_app_Qh`, for
  `L(F ⋙ G) ≅ D(F) ⋙ L(G)` with `F` exact preserving K-flat complexes;
* `CategoryTheory.Functor.leftDerivedFunctorCompMapDerivedCategoryRightIso_hom_app_Qh`, for
  `L(G ⋙ F') ≅ L(G) ⋙ D(F')` with `F'` exact;
* `CategoryTheory.Functor.leftDerivedFunctorIsoOfIso_hom_app_Qh`, for `L(G) ≅ L(G')` induced by
  `G ≅ G'`;
* `CategoryTheory.Mod.derivedExtendScalarsCompIso_inv_app_Qh_comp_counit`, for the transitivity
  isomorphism of the derived extensions of scalars of module objects, an instance of
  `CategoryTheory.Adjunction.conjugateIsoEquiv_symm_inv_app_comp_counit`.
-/

@[expose] public section

universe wC wD wE vC vD vE uC uD uE v u

open CategoryTheory Limits MonoidalCategory MonObj

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [IsGrothendieckAbelian.{v} C]
  [Abelian.HasFunctorialFlatResolution C]
  {R S T : C} [MonObj R] [MonObj S] [MonObj T] [IsCommMonObj R] [IsCommMonObj S]
  [IsCommMonObj T] (φ : R ⟶ S) [IsMonHom φ] (ψ : S ⟶ T) [IsMonHom ψ]

omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] [IsCommMonObj T] in
/-- The unit of the adjunction `Ext_{φ ≫ ψ} ⊣ comap (φ ≫ ψ)`, followed by the composition
isomorphism of restrictions of scalars, is the unit of the composite adjunction followed by the
composition isomorphism of extensions of scalars. -/
lemma extendRestrictAdjunction_comp_unit_app (M : Mod C R) :
    (extendRestrictAdjunction (φ ≫ ψ)).unit.app M ≫
        ((comapCongr (rfl : φ ≫ ψ = φ ≫ ψ)).inv ≫ (comapComp φ ψ).hom).app
          ((extendScalars (φ ≫ ψ)).obj M) =
      (extendRestrictAdjunction φ).unit.app M ≫
        (comap φ).map ((extendRestrictAdjunction ψ).unit.app ((extendScalars φ).obj M) ≫
          (comap ψ).map ((extendScalarsComp φ ψ).inv.app M)) := by
  have h₁ := Adjunction.unit_leftAdjointUniq_hom_app
    (((extendRestrictAdjunction φ).comp (extendRestrictAdjunction ψ)).ofNatIsoRight
      (comapComp φ ψ).symm) (extendRestrictAdjunction (φ ≫ ψ)) M
  have h₂ : ((comapCongr (rfl : φ ≫ ψ = φ ≫ ψ)).inv ≫ (comapComp φ ψ).hom) =
      (comapComp φ ψ).hom := by
    ext N : 2
    apply Mod.hom_ext
    simp [comapCongr]
  rw [h₂, extendScalarsComp, Adjunction.leftAdjointUniq_inv_app, ← h₁, Category.assoc,
    (comapComp φ ψ).hom.naturality]
  have h₃ : (((extendRestrictAdjunction φ).comp (extendRestrictAdjunction ψ)).ofNatIsoRight
      (comapComp φ ψ).symm).unit.app M ≫ (comapComp φ ψ).hom.app _ =
      ((extendRestrictAdjunction φ).comp (extendRestrictAdjunction ψ)).unit.app M := by
    rw [← Adjunction.homEquiv_id, Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_id]
    simp
  erw [reassoc_of% h₃]
  simp [Adjunction.comp_unit_app]

omit [Abelian.HasFunctorialFlatResolution C] [IsCommMonObj T] in
/-- `Mod.extendRestrictAdjunction_comp_unit_app` on the homotopy categories. -/
lemma mapHomotopyCategory_extendRestrictAdjunction_comp_unit_app
    (M : HomotopyCategory (Mod C R) (.up ℤ)) :
    ((extendRestrictAdjunction (φ ≫ ψ)).mapHomotopyCategory (.up ℤ)).unit.app M ≫
        (NatTrans.mapHomotopyCategory ((comapCongr (rfl : φ ≫ ψ = φ ≫ ψ)).inv ≫
          (comapComp φ ψ).hom) (.up ℤ)).app
          (((extendScalars (φ ≫ ψ)).mapHomotopyCategory (.up ℤ)).obj M) =
      ((extendRestrictAdjunction φ).mapHomotopyCategory (.up ℤ)).unit.app M ≫
        ((comap φ).mapHomotopyCategory (.up ℤ)).map
          (((extendRestrictAdjunction ψ).mapHomotopyCategory (.up ℤ)).unit.app
            (((extendScalars φ).mapHomotopyCategory (.up ℤ)).obj M) ≫
          ((comap ψ).mapHomotopyCategory (.up ℤ)).map
            ((NatTrans.mapHomotopyCategory (extendScalarsComp φ ψ).inv (.up ℤ)).app M)) := by
  obtain ⟨M, rfl⟩ := HomotopyCategory.quotient_obj_surjective M
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient,
    Adjunction.mapHomotopyCategory_unit_app_quotient]
  erw [Adjunction.mapHomotopyCategory_unit_app_quotient]
  erw [NatTrans.mapHomotopyCategory_app, NatTrans.mapHomotopyCategory_app,
    Functor.mapHomotopyCategory_map, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext n : 1
  have := extendRestrictAdjunction_comp_unit_app φ ψ (M.X n)
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f, Adjunction.mapHomologicalComplex_unit_app_f,
    Functor.map_comp] at this ⊢
  exact this

omit [SymmetricCategory C] [Abelian.HasFunctorialFlatResolution C] [IsCommMonObj R] [IsCommMonObj S]
  [IsCommMonObj T] in
/-- The isomorphism `Mod.mapDerivedCategoryComapCompIso` on the image of a complex. -/
lemma mapDerivedCategoryFactorsh_inv_app_comp_mapDerivedCategoryComapCompIso_inv_app
    (N : HomotopyCategory (Mod C T) (.up ℤ)) :
    (comap (φ ≫ ψ)).mapDerivedCategoryFactorsh.inv.app N ≫
        (mapDerivedCategoryComapCompIso φ ψ (φ ≫ ψ) rfl).inv.app (DerivedCategory.Qh.obj N) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory
          ((comapCongr (rfl : φ ≫ ψ = φ ≫ ψ)).inv ≫ (comapComp φ ψ).hom) (.up ℤ)).app N) ≫
        (comap φ).mapDerivedCategoryFactorsh.inv.app
          (((comap ψ).mapHomotopyCategory (.up ℤ)).obj N) ≫
        (comap φ).mapDerivedCategory.map ((comap ψ).mapDerivedCategoryFactorsh.inv.app N) := by
  have e₁ := Functor.mapDerivedCategoryNatIso_fach
    ((comapComp φ ψ).symm ≪≫ comapCongr (rfl : φ ≫ ψ = φ ≫ ψ)).symm N
  have e₂ := Functor.mapDerivedCategoryCompIso_fach (comap ψ) (comap φ) N
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app] at e₂
  erw [DerivedCategory.Qh.map_id, Category.comp_id] at e₂
  have e₃ : (Functor.mapDerivedCategoryNatIso
      ((comapComp φ ψ).symm ≪≫ comapCongr (rfl : φ ≫ ψ = φ ≫ ψ))).inv =
      (Functor.mapDerivedCategoryNatIso
        ((comapComp φ ψ).symm ≪≫ comapCongr (rfl : φ ≫ ψ = φ ≫ ψ)).symm).hom := rfl
  have e₁' : (comap (φ ≫ ψ)).mapDerivedCategoryFactorsh.inv.app N ≫
      (Functor.mapDerivedCategoryNatIso
        ((comapComp φ ψ).symm ≪≫ comapCongr (rfl : φ ≫ ψ = φ ≫ ψ)).symm).hom.app
          (DerivedCategory.Qh.obj N) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory
          ((comapCongr (rfl : φ ≫ ψ = φ ≫ ψ)).inv ≫ (comapComp φ ψ).hom) (.up ℤ)).app N) ≫
        (comap ψ ⋙ comap φ).mapDerivedCategoryFactorsh.inv.app N := by
    rw [← cancel_epi ((comap (φ ≫ ψ)).mapDerivedCategoryFactorsh.hom.app N),
      Iso.hom_inv_id_app_assoc, ← cancel_mono
        ((comap ψ ⋙ comap φ).mapDerivedCategoryFactorsh.hom.app N), Category.assoc, e₁]
    simp
  have e₂' : (comap ψ ⋙ comap φ).mapDerivedCategoryFactorsh.inv.app N ≫
      (Functor.mapDerivedCategoryCompIso (comap ψ) (comap φ)).inv.app (DerivedCategory.Qh.obj N) =
      (comap φ).mapDerivedCategoryFactorsh.inv.app
          (((comap ψ).mapHomotopyCategory (.up ℤ)).obj N) ≫
        (comap φ).mapDerivedCategory.map ((comap ψ).mapDerivedCategoryFactorsh.inv.app N) := by
    rw [← cancel_epi ((comap ψ ⋙ comap φ).mapDerivedCategoryFactorsh.hom.app N),
      Iso.hom_inv_id_app_assoc, ← e₂]
    simp [← Functor.map_comp]
  simp only [mapDerivedCategoryComapCompIso, Iso.trans_inv, NatTrans.comp_app, e₃]
  rw [reassoc_of% e₁', e₂']

/-- The transitivity isomorphism `L(Ext_{φ ≫ ψ}) ≅ L(Ext_φ) ⋙ L(Ext_ψ)` of the derived extensions
of scalars is compatible with the counits: on the image of a complex `M`, through the counits it
is the transitivity isomorphism `Mod.extendScalarsComp` of the extensions of scalars. -/
lemma derivedExtendScalarsCompIso_inv_app_Qh_comp_counit
    (M : HomotopyCategory (Mod C R) (.up ℤ)) :
    (derivedExtendScalarsCompIso φ ψ (φ ≫ ψ) rfl).inv.app (DerivedCategory.Qh.obj M) ≫
        (extendScalars (φ ≫ ψ)).leftDerivedFunctorCounit.app M =
      (extendScalars ψ).leftDerivedFunctor.map
          ((extendScalars φ).leftDerivedFunctorCounit.app M) ≫
        (extendScalars ψ).leftDerivedFunctorCounit.app
          (((extendScalars φ).mapHomotopyCategory (.up ℤ)).obj M) ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory (extendScalarsComp φ ψ).inv (.up ℤ)).app M) :=
  Adjunction.conjugateIsoEquiv_symm_inv_app_comp_counit
    ((extendRestrictAdjunction φ).mapHomotopyCategory (.up ℤ))
    ((extendRestrictAdjunction ψ).mapHomotopyCategory (.up ℤ))
    ((extendRestrictAdjunction (φ ≫ ψ)).mapHomotopyCategory (.up ℤ))
    (derivedExtendMapDerivedCategoryAdjunction φ) (derivedExtendMapDerivedCategoryAdjunction ψ)
    (derivedExtendMapDerivedCategoryAdjunction (φ ≫ ψ))
    (extendScalars φ).leftDerivedFunctorCounit (extendScalars ψ).leftDerivedFunctorCounit
    (extendScalars (φ ≫ ψ)).leftDerivedFunctorCounit
    (comap φ).mapDerivedCategoryFactorsh (comap ψ).mapDerivedCategoryFactorsh
    (comap (φ ≫ ψ)).mapDerivedCategoryFactorsh (mapDerivedCategoryComapCompIso φ ψ (φ ≫ ψ) rfl)
    (fun N ↦ (NatTrans.mapHomotopyCategory
      ((comapCongr (rfl : φ ≫ ψ = φ ≫ ψ)).inv ≫ (comapComp φ ψ).hom) (.up ℤ)).app N)
    (fun M ↦ (NatTrans.mapHomotopyCategory (extendScalarsComp φ ψ).inv (.up ℤ)).app M)
    (derivedExtendMapDerivedCategoryAdjunction_unit_app_Qh φ)
    (derivedExtendMapDerivedCategoryAdjunction_unit_app_Qh ψ)
    (derivedExtendMapDerivedCategoryAdjunction_unit_app_Qh (φ ≫ ψ))
    (mapDerivedCategoryFactorsh_inv_app_comp_mapDerivedCategoryComapCompIso_inv_app φ ψ)
    (mapHomotopyCategory_extendRestrictAdjunction_comp_unit_app φ ψ) M

end CategoryTheory.Mod

namespace CategoryTheory.Functor

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D] [Abelian C] [Abelian D]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]

/-- The isomorphism `L(G) ≅ L(G')` induced by `e : G ≅ G'` is compatible with the counits. -/
@[reassoc]
lemma leftDerivedFunctorIsoOfIso_hom_app_Qh {G G' : C ⥤ D} [G.Additive] [G'.Additive]
    [G.PreservesKFlatQuasiIso] [G'.PreservesKFlatQuasiIso] (e : G ≅ G')
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    (leftDerivedFunctorIsoOfIso e).hom.app (DerivedCategory.Qh.obj K) ≫
        G'.leftDerivedFunctorCounit.app K =
      G.leftDerivedFunctorCounit.app K ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app K) :=
  leftDerivedNatTrans_app _ _ _ _ (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) _ K

/-- `L(G ⋙ F') ≅ L(G) ⋙ D(F')`, for an exact functor `F'`, is compatible with the counits. -/
@[reassoc]
lemma leftDerivedFunctorCompMapDerivedCategoryRightIso_hom_app_Qh {E : Type uE} [Category.{vE} E]
    [Abelian E] [HasDerivedCategory.{wE} E] (G : C ⥤ D) [G.Additive] [G.PreservesKFlatQuasiIso]
    (F' : D ⥤ E) [F'.Additive] [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    (leftDerivedFunctorCompMapDerivedCategoryRightIso G F').hom.app (DerivedCategory.Qh.obj K) ≫
        F'.mapDerivedCategory.map (G.leftDerivedFunctorCounit.app K) ≫
        F'.mapDerivedCategoryFactorsh.hom.app ((G.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) =
      (G ⋙ F').leftDerivedFunctorCounit.app K := by
  have h : (leftDerivedFunctorCompMapDerivedCategoryRightIso G F').hom.app
      (DerivedCategory.Qh.obj K) ≫
        (leftDerivedFunctorCompMapDerivedCategoryRightCounit G F').app K =
      (G ⋙ F').leftDerivedFunctorCounit.app K ≫ 𝟙 _ :=
    leftDerivedNatTrans_app _ _ _ _ (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) _ K
  rw [Category.comp_id] at h
  rw [← h]
  simp [leftDerivedFunctorCompMapDerivedCategoryRightCounit,
    mapHomotopyCategoryCompIso_refl_hom_app]

/-- For an exact functor `F`, the inverse of `L(F) ≅ D(F)` followed by the counit of `L(F)` is
the comparison `F.mapDerivedCategoryFactorsh`. -/
@[reassoc]
lemma leftDerivedFunctorIsoMapDerivedCategory_inv_app_Qh (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    F.leftDerivedFunctorIsoMapDerivedCategory.inv.app (DerivedCategory.Qh.obj K) ≫
        F.leftDerivedFunctorCounit.app K = F.mapDerivedCategoryFactorsh.hom.app K := by
  rw [← F.leftDerivedFunctorIsoMapDerivedCategory_hom_fac, NatTrans.comp_app, whiskerLeft_app,
    Iso.inv_hom_id_app_assoc]

/-- For an exact functor `F` and `g : N ⟶ Qh K`, the inverse of `L(F) ≅ D(F)` followed by
`L(F)(g)` and the counit of `L(F)` is `D(F)(g)` followed by `F.mapDerivedCategoryFactorsh`. -/
@[reassoc]
lemma leftDerivedFunctorIsoMapDerivedCategory_inv_app_comp_map_comp_counit (F : C ⥤ D)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] {N : DerivedCategory C}
    (K : HomotopyCategory C (ComplexShape.up ℤ)) (g : N ⟶ DerivedCategory.Qh.obj K) :
    F.leftDerivedFunctorIsoMapDerivedCategory.inv.app N ≫ F.leftDerivedFunctor.map g ≫
        F.leftDerivedFunctorCounit.app K =
      F.mapDerivedCategory.map g ≫ F.mapDerivedCategoryFactorsh.hom.app K := by
  rw [← Category.assoc, ← F.leftDerivedFunctorIsoMapDerivedCategory.inv.naturality g,
    Category.assoc, leftDerivedFunctorIsoMapDerivedCategory_inv_app_Qh]

section CompositionKFlat

variable {E : Type uE} [Category.{vE} E] [Abelian E] [HasDerivedCategory.{wE} E]
  [MonoidalCategory D] [MonoidalPreadditive D]
  [HasCountableCoproducts D]
  [HasColimitsOfShape ℤ D] [HasExactColimitsOfShape ℤ D]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).obj X)]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesKFlatComplexes] (G : D ⥤ E) [G.Additive] [G.PreservesKFlatQuasiIso]

/-- `L(F ⋙ G) ≅ D(F) ⋙ L(G)`, for an exact functor `F` preserving K-flat complexes, is
compatible with the counits. -/
@[reassoc]
lemma leftDerivedFunctorCompMapDerivedCategoryIso_hom_app_Qh
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    (leftDerivedFunctorCompMapDerivedCategoryIso F G).hom.app (DerivedCategory.Qh.obj K) ≫
        G.leftDerivedFunctor.map (F.mapDerivedCategoryFactorsh.hom.app K) ≫
        G.leftDerivedFunctorCounit.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) =
      (F ⋙ G).leftDerivedFunctorCounit.app K := by
  have h : (leftDerivedFunctorCompMapDerivedCategoryIso F G).hom.app
      (DerivedCategory.Qh.obj K) ≫ (leftDerivedFunctorCompMapDerivedCategoryCounit F G).app K =
      (F ⋙ G).leftDerivedFunctorCounit.app K ≫ 𝟙 _ :=
    leftDerivedNatTrans_app _ _ _ _ (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) _ K
  rw [Category.comp_id] at h
  rw [← h]
  simp [leftDerivedFunctorCompMapDerivedCategoryCounit, mapHomotopyCategoryCompIso_refl_hom_app]

/-- The inverse form of `Functor.leftDerivedFunctorCompMapDerivedCategoryIso_hom_app_Qh`. -/
@[reassoc]
lemma leftDerivedFunctorCompMapDerivedCategoryIso_inv_app_Qh
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    (leftDerivedFunctorCompMapDerivedCategoryIso F G).inv.app (DerivedCategory.Qh.obj K) ≫
        (F ⋙ G).leftDerivedFunctorCounit.app K =
      G.leftDerivedFunctor.map (F.mapDerivedCategoryFactorsh.hom.app K) ≫
        G.leftDerivedFunctorCounit.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) := by
  rw [← leftDerivedFunctorCompMapDerivedCategoryIso_hom_app_Qh, Iso.inv_hom_id_app_assoc]

end CompositionKFlat

end CategoryTheory.Functor
