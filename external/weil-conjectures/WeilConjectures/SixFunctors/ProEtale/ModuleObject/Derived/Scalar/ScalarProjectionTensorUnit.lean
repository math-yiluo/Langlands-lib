/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarProjectionTransformation
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances

/-! The tensor-unit component of the scalar-first native projection map.
(blueprint: lem-sfb-scalar-projection-tensor-unit)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
namespace AlgebraicGeometry.ProEtale.CondensedRing

private abbrev scalarProjectionGeneric
    {C D : Type*} [Category* C] [Category* D]
    [mc : MonoidalCategory C] [md : MonoidalCategory D] {L : D ⥤ C} {R : C ⥤ D}
    (adj : L ⊣ R)
    (δ : (Functor.postcompose₂.obj L).obj (curriedTensor D) ⟶
      (((Functor.whiskeringLeft₂ C).obj L).obj L).obj (curriedTensor C)) (K : C) :
    tensorRight (R.obj K) ⟶ (L ⋙ tensorRight K) ⋙ R :=
  (adj.rightAdjointProjectionMap
    (T_C := (curriedTensor C).flip) (T_D := (curriedTensor D).flip)
    ((flipFunctor _ _ _).map δ)).app K

private theorem scalarProjectionGeneric_leftUnitality
    {C D : Type*} [Category* C] [Category* D]
    [mc : MonoidalCategory C] [md : MonoidalCategory D] {L : D ⥤ C} {R : C ⥤ D}
    (adj : L ⊣ R)
    (δ : (Functor.postcompose₂.obj L).obj (curriedTensor D) ⟶
      (((Functor.whiskeringLeft₂ C).obj L).obj L).obj (curriedTensor C))
    (η : L.obj (𝟙_ D) ⟶ 𝟙_ C)
    (hη : ∀ B : D, (δ.app (𝟙_ D)).app B ≫ η ▷ L.obj B ≫
      (λ_ (L.obj B)).hom = L.map (λ_ B).hom) (K : C) :
    (scalarProjectionGeneric adj δ K).app (𝟙_ D) ≫
      R.map (η ▷ K) ≫ R.map (λ_ K).hom = (λ_ (R.obj K)).hom := by
  apply (adj.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    adj.counit_naturality]
  erw [adj.counit_naturality_assoc,
    Adjunction.map_rightAdjointProjectionMap_app_app_comp_counit_assoc]
  change (δ.app (𝟙_ D)).app (R.obj K) ≫
    (L.obj (𝟙_ D) ◁ adj.counit.app K) ≫ η ▷ K ≫ (λ_ K).hom = _
  erw [whisker_exchange_assoc η (adj.counit.app K),
    leftUnitor_naturality, reassoc_of% (hη (R.obj K))]

private theorem scalarProjectionGeneric_unit
    {C D : Type*} [Category* C] [Category* D]
    [mc : MonoidalCategory C] [md : MonoidalCategory D] {L : D ⥤ C} {R : C ⥤ D}
    (adj : L ⊣ R)
    (δ : (Functor.postcompose₂.obj L).obj (curriedTensor D) ⟶
      (((Functor.whiskeringLeft₂ C).obj L).obj L).obj (curriedTensor C))
    (η : L.obj (𝟙_ D) ⟶ 𝟙_ C) [IsIso η]
    (hη : ∀ B : D, (δ.app (𝟙_ D)).app B ≫ η ▷ L.obj B ≫
      (λ_ (L.obj B)).hom = L.map (λ_ B).hom) (K : C) :
    IsIso ((scalarProjectionGeneric adj δ K).app (𝟙_ D)) := by
  have h := scalarProjectionGeneric_leftUnitality adj δ η hη K
  have : IsIso ((scalarProjectionGeneric adj δ K).app (𝟙_ D) ≫
      R.map (η ▷ K) ≫ R.map (λ_ K).hom) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (R.map (η ▷ K) ≫ R.map (λ_ K).hom)

private theorem scalarProjectionNative_delta
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A B : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    @Functor.OplaxMonoidal.δ _ _ _ _ _ _
        (CondensedRing.upperStar Λ f).leftDerivedFunctor
        (leftDerivedUpperStarOplaxMonoidal Λ f) A B =
      ((leftDerivedUpperStarTensor Λ f).app A).app B := rfl

/-- The scalar-first projection is invertible at the tensor unit.
Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-scalar-six/det-prop-scalar-six-direct-image.proof.md, finite-free paragraph.
Transpose the projection under the derived adjunction. Counit naturality and tensor
interchange identify its composite with the image of the pullback-unit comparison
and the left unitor with the left unitor of the pushforward. Oplax left unitality
proves this identity; both subsequent maps are invertible, hence so is the projection.
(blueprint: lem-sfb-scalar-projection-tensor-unit)
-/
theorem scalarProjection_tensorUnit_isIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    IsIso ((scalarFirstProjection Λ f K).app (𝟙_ _)) := by
  unfold scalarFirstProjection
  let _ := upperStar_preservesFlat Λ f
  rw [← leftDerivedUpperStarTensor_eq_leftDerivedTensorComparison Λ f]
  let L := (CondensedRing.upperStar Λ f).leftDerivedFunctor
  let η := @Functor.OplaxMonoidal.η _ _ _ _ _ _ L
    (leftDerivedUpperStarOplaxMonoidal Λ f)
  have : IsIso η := by
    dsimp only [η]
    rw [leftDerivedUpperStarOplaxMonoidal_η]
    infer_instance
  apply scalarProjectionGeneric_unit _ _ η
  intro B
  have h := @Functor.OplaxMonoidal.left_unitality_hom _ _ _ _ _ _ L
    (leftDerivedUpperStarOplaxMonoidal Λ f) B
  rw [scalarProjectionNative_delta] at h
  dsimp only [η, L, Functor.postcompose₂, Functor.whiskeringLeft₂,
    Functor.whiskeringRight, Functor.whiskeringLeft, Functor.comp_obj, curriedTensor,
    leftDerivedUpperStarTensorLeft, leftDerivedUpperStarTensorRight] at h ⊢
  apply h

end AlgebraicGeometry.ProEtale.CondensedRing
