/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
public import WeilConjectures.AlgebraicGeometry.Etale.Hom.EtaleHomComparisonModels

/-! # Normalization of the ordinary scalar tensor comparison
Source: blueprint lemma-change-coefficients-internal-hom--1, evaluation paragraph
(blueprint: lem-coef-finite-hom-scalar-tensor-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u a b c d
open CategoryTheory AlgebraicGeometry CategoryTheory.MonoidalCategory Opposite
namespace WeilConjectures

attribute [local implicit_reducible] CategoryTheory.uniformProd
  Etale.sheafMonoidalCategory Etale.sheafBraidedCategory
  ModuleCat.MonoidalCategory.instBraidedCategory

attribute [local irreducible]
  DerivedCategory.monoidalClosed_of_hasFunctorialFlatResolution

private theorem tensorNatural₁
    {C D : Type*} [Category C] [Category D]
    (T : C ⥤ C ⥤ C) (U : D ⥤ D ⥤ D) (F : C ⥤ D)
    (δ : Functor.uncurry.obj T ⋙ F ≅ F.prod F ⋙ Functor.uncurry.obj U)
    {K K' : C} (f : K ⟶ K') (L : C) :
    (U.map (F.map f)).app (F.obj L) ≫ (δ.app (K', L)).inv =
      (δ.app (K, L)).inv ≫ F.map ((T.map f).app L) := by
  have h := δ.inv.naturality (show (K, L) ⟶ (K', L) from (f, 𝟙 L))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.prod_obj,
    Functor.uncurry_obj_map] at h
  simpa only [_root_.CategoryTheory.Functor.map_id, Functor.comp_obj, Functor.uncurry_obj_obj,
    Functor.prod_obj, Iso.app_inv, Category.comp_id] using h

private theorem tensorNatural₂
    {C D : Type*} [Category C] [Category D]
    (T : C ⥤ C ⥤ C) (U : D ⥤ D ⥤ D) (F : C ⥤ D)
    (δ : Functor.uncurry.obj T ⋙ F ≅ F.prod F ⋙ Functor.uncurry.obj U)
    (K : C) {L L' : C} (f : L ⟶ L') :
    (U.obj (F.obj K)).map (F.map f) ≫ (δ.app (K, L')).inv =
      (δ.app (K, L)).inv ≫ F.map ((T.obj K).map f) := by
  have h := δ.inv.naturality (show (K, L) ⟶ (K, L') from (𝟙 K, f))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.prod_obj,
    Functor.uncurry_obj_map] at h
  simpa only [_root_.CategoryTheory.Functor.map_id, Functor.comp_obj, Functor.uncurry_obj_obj,
    Functor.prod_obj, Iso.app_inv, NatTrans.id_app, Category.id_comp] using h

private theorem tensorNormalization_flat_onSite
    (C : Type a) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [SymmetricCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    (D : Type b) [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [SymmetricCategory D]
    [Abelian.HasFunctorialFlatResolution D] (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology C ⥤ Sheaf X.smallEtaleTopology D)
    [F.Additive] [F.OplaxMonoidal] [F.IsLeftAdjoint]
    (S : DerivedCategory (Sheaf X.smallEtaleTopology C) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology D))
    (r : ∀ P : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ,
      S.obj (DerivedCategory.Q.obj P) ⟶
        DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (δ : Functor.uncurry.obj (Etale.derivedTensor C X) ⋙ S ≅
      S.prod S ⋙ Functor.uncurry.obj (Etale.derivedTensor D X))
    (hn : Etale.ExceptionalCoefficients.SiteTensorNormalizationAux C D X F S r δ) :
    Etale.EtaleHomTensorModelNormalization C D X F S r
      (fun K L ↦ (δ.app (K, L)).symm) := by
  intro P Q _ _ _ _
  exact (hn P Q).symm

/-- The inverse exceptional tensorator is the ordinary scalar tensor comparison.
Source: Stacks 07A4 and blueprint lemma-change-coefficients-internal-hom--1, evaluation paragraph
(blueprint: lem-coef-finite-hom-scalar-tensor-normalization).

Proof: inverse naturality gives both tensor naturality equations. The exceptional
normalization is the ordinary tensor model normalization. The unique canonical
tensor comparison therefore identifies every component with the ordinary one. -/
theorem finiteHom_scalar_tensor_normalization {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) (K L : Etale.DerivedCategoryModule A X) :
    (Etale.ExceptionalCoefficients.tensorIso φ X).inv.app (K, L) =
      (Etale.etaleHomTensorComparison X φ K L).hom := by
  let δ := Etale.ExceptionalCoefficients.tensorIso φ X
  have hn : Etale.ExceptionalCoefficients.TensorNormalization φ X δ := by
    have he : δ = (Etale.ExceptionalCoefficients.tensorIso_existsUnique φ X).choose := by
      change (Etale.ExceptionalCoefficients.siteTensorIso_existsUnique φ X).choose = _
      exact eq_of_heq (Etale.ExceptionalCoefficients.siteTensorIso_existsUnique φ X).choose_spec.1
    rw [he]
    exact (Etale.ExceptionalCoefficients.tensorIso_existsUnique φ X).choose_spec.1
  have hc : Etale.IsEtaleHomTensorCanonical X φ (fun P Q ↦ (δ.app (P, Q)).symm) := by
    refine ⟨tensorNatural₁ _ _ _ δ, tensorNatural₂ _ _ _ δ, ?_⟩
    exact tensorNormalization_flat_onSite (ModuleCat.{u + 1} A) (ModuleCat.{u + 1} B)
      X (AlgebraicGeometry.ProEtale.etaleSheafExtendScalars φ X)
      (Etale.scalarExtension φ X) (Etale.scalarExtensionRepresentative φ X) δ hn
  have he := (Etale.etaleHomTensorComparison_existsUnique X φ).unique hc
    (Etale.etaleHomTensorComparison_existsUnique X φ).choose_spec.1
  unfold Etale.etaleHomTensorComparison
  exact congrArg Iso.hom (congrFun (congrFun he K) L)

end WeilConjectures
