/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalCompDerived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Braided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionMapShift
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure

/-!
# The derived pullback of module objects is braided

The comparison `f^* A ⊗ f^* B ⟶ f^* (A ⊗ B)` of complexes of module objects commutes with the
Koszul braidings of the tensor products of complexes
(`ProEtale.CondensedRing.upperStarTensorComplexHom_braiding`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- `δ_upperStar_braiding` in terms of the tensorators. -/
@[reassoc]
lemma μ_upperStar_braiding
    (A B : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    Functor.LaxMonoidal.μ (f)^*⟦Λ⟧ A B ≫ (f)^*⟦Λ⟧.map (β_ A B).hom =
      (β_ ((f)^*⟦Λ⟧.obj A) ((f)^*⟦Λ⟧.obj B)).hom ≫ Functor.LaxMonoidal.μ (f)^*⟦Λ⟧ B A := by
  rw [← cancel_epi (Functor.OplaxMonoidal.δ (f)^*⟦Λ⟧ A B), Functor.Monoidal.δ_μ_assoc,
    δ_upperStar_braiding_assoc, Functor.Monoidal.δ_μ, Category.comp_id]

/-- On complexes, the comparison `f^* A ⊗ f^* B ⟶ f^* (A ⊗ B)` commutes with the Koszul
braidings: it is inverse to the comonoidal comparison (`upperStarTensorComplexHom_δ`), which
commutes with them
(`Functor.OplaxMonoidal.mapHomologicalComplex_map_braiding_hom_comp_δNatTrans`). -/
lemma upperStarTensorComplexHom_braiding
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) :
    upperStarTensorComplexHom Λ f A B ≫
        ((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).map (β_ A B).hom =
      (β_ (((f)^*⟦Λ⟧.mapHomologicalComplex _).obj A)
          (((f)^*⟦Λ⟧.mapHomologicalComplex _).obj B)).hom ≫
        upperStarTensorComplexHom Λ f B A := by
  have hδ := Functor.OplaxMonoidal.mapHomologicalComplex_map_braiding_hom_comp_δNatTrans
    (f)^*⟦Λ⟧ (fun X Y ↦ (δ_upperStar_braiding Λ f X Y).symm) A B
  exact (IsIso.mono_of_iso _).right_cancellation _ _ <|
    (Category.assoc _ _ _).trans <| (congrArg (upperStarTensorComplexHom Λ f A B ≫ ·) hδ).trans <|
      ((reassoc_of% (upperStarTensorComplexHom_δ Λ f A B)) _).trans <|
        (Category.comp_id _).symm.trans <|
          (congrArg (_ ≫ ·) (upperStarTensorComplexHom_δ Λ f B A).symm).trans
            (Category.assoc _ _ _).symm

/-- `upperStarTensorComplexHom_braiding` in the homotopy category. -/
lemma quotient_map_upperStarTensorComplexHom_braiding
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) :
    (HomotopyCategory.quotient _ _).map (upperStarTensorComplexHom Λ f A B) ≫
        ((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).map
          (β_ ((HomotopyCategory.quotient _ _).obj A) ((HomotopyCategory.quotient _ _).obj B)).hom =
      (β_ (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj A))
          (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj
            ((HomotopyCategory.quotient _ _).obj B))).hom ≫
        (HomotopyCategory.quotient _ _).map (upperStarTensorComplexHom Λ f B A) := by
  have h := (HomotopyCategory.quotient _ (.up ℤ)).congr_map
    (upperStarTensorComplexHom_braiding Λ f A B)
  simp only [Functor.map_comp] at h
  exact h

/-- The comparison `upperStarTensorComplexHom` on objects of the homotopy category. -/
noncomputable def upperStarTensorHomotopyHom
    (P Q : HomotopyCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) (.up ℤ)) :
    ((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj P ⊗ ((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj Q ⟶
      ((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj (P ⊗ Q) :=
  (HomotopyCategory.quotient _ _).map (upperStarTensorComplexHom Λ f P.as Q.as)

/-- `quotient_map_upperStarTensorComplexHom_braiding` in terms of `upperStarTensorHomotopyHom`. -/
lemma upperStarTensorHomotopyHom_braiding
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) :
    upperStarTensorHomotopyHom Λ f ((HomotopyCategory.quotient _ _).obj A)
          ((HomotopyCategory.quotient _ _).obj B) ≫
        ((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).map
          (β_ ((HomotopyCategory.quotient _ _).obj A) ((HomotopyCategory.quotient _ _).obj B)).hom =
      (β_ (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj A))
          (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj
            ((HomotopyCategory.quotient _ _).obj B))).hom ≫
        upperStarTensorHomotopyHom Λ f ((HomotopyCategory.quotient _ _).obj B)
          ((HomotopyCategory.quotient _ _).obj A) :=
  quotient_map_upperStarTensorComplexHom_braiding Λ f A B

set_option maxHeartbeats 1000000 in
-- the module objects of the homotopy category are unfolded
/-- The comparison `upperStarTensorHomotopyHom` is an isomorphism on images of complexes. -/
instance isIso_upperStarTensorHomotopyHom
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) :
    IsIso (upperStarTensorHomotopyHom Λ f ((HomotopyCategory.quotient _ (.up ℤ)).obj A)
      ((HomotopyCategory.quotient _ (.up ℤ)).obj B)) := by
  have h := upperStarTensorComplexHom_δ Λ f A B
  have : IsIso (upperStarTensorComplexHom Λ f A B ≫
      ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ)
        (f)^*⟦Λ⟧).app A).app B) := by
    rw [h]
    infer_instance
  have : IsIso (upperStarTensorComplexHom Λ f A B) := IsIso.of_isIso_comp_right _
    (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) (f)^*⟦Λ⟧).app A).app B)
  exact Functor.map_isIso (HomotopyCategory.quotient _ (.up ℤ))
    (upperStarTensorComplexHom Λ f A B)

open DerivedCategory Functor Functor.LaxMonoidal

attribute [local instance] DerivedCategory.braidedCategory'

/-- The derived braiding of module objects on objects `Qh K`, `Qh M`:
`β_{Qh K, Qh M} ≫ μ_{M, K} = μ_{K, M} ≫ Qh β_{K, M}`. -/
lemma derivedBraiding_hom_μ_Qh {Z : Scheme.{u}}
    (K M : HomotopyCategory
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) (.up ℤ)) :
    (β_ (Qh.obj K) (Qh.obj M)).hom ≫ μ Qh M K = μ Qh K M ≫ Qh.map (β_ K M).hom :=
  DerivedMonoidal.braiding_hom_μ Qh (HomotopyCategory.quasiIso _ _) K M

/-- The tensor comparison of `Lf^*` commutes with the derived braidings at images of K-flat
complexes. -/
lemma leftDerivedUpperStarTensor_braiding_Qh
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ)
    (hA : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat A)
    (hB : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat B) :
    L((f)^*⟦Λ⟧).map (β_ (Qh.obj ((HomotopyCategory.quotient _ _).obj A))
        (Qh.obj ((HomotopyCategory.quotient _ _).obj B))).hom ≫
        ((leftDerivedUpperStarTensor Λ f).app _).app _ =
      ((leftDerivedUpperStarTensor Λ f).app _).app _ ≫
        (β_ (L((f)^*⟦Λ⟧).obj (Qh.obj ((HomotopyCategory.quotient _ _).obj A)))
          (L((f)^*⟦Λ⟧).obj (Qh.obj ((HomotopyCategory.quotient _ _).obj B)))).hom := by
  have := CachedModInstances.cached_hasTensor₄ObjExt Λ
  have := CachedModInstances.cached_hasGoodTensor₁₂Tensor Λ
  have := CachedModInstances.cached_hasGoodTensorTensor₂₃ Λ
  have := CachedModInstances.cached_hasColimitsOfShape_int Λ
  have := CachedModInstances.cached_hasExactColimitsOfShape_int Λ
  have := CachedModInstances.cached_hasCountableCoproducts Λ
  have := CachedModInstances.cached_preservesColimitsOfShape_int_tensorLeft Λ
  have := CachedModInstances.cached_preservesColimitsOfShape_int_tensorRight Λ
  have := CachedModInstances.cached_hasFunctorialFlatResolution Λ
  have := CachedModInstances.cached_hasTensor Λ
  have := CachedModInstances.cached_preservesColimit_empty_tensorLeft Λ
  have := CachedModInstances.cached_preservesColimit_empty_tensorRight Λ
  have := CachedModInstances.cached_preservesZeroMorphisms_tensorLeft Λ
  have := CachedModInstances.cached_preservesZeroMorphisms_tensorRight Λ
  have hA' := (HomotopyCategory.kFlat_quotient_obj_iff A).2 hA
  have hB' := (HomotopyCategory.kFlat_quotient_obj_iff B).2 hB
  have : IsIso ((f)^*⟦Λ⟧.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj A)) :=
    (f)^*⟦Λ⟧.isIso_leftDerivedFunctorCounit_app_of_kFlat' _ hA'
  have : IsIso ((f)^*⟦Λ⟧.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj B)) :=
    (f)^*⟦Λ⟧.isIso_leftDerivedFunctorCounit_app_of_kFlat' _ hB'
  have : IsIso (μ Qh (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj
      ((HomotopyCategory.quotient _ _).obj B))
      (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj A))) :=
    isIso_μNatTrans_Qh_app_app_of_kFlat _ _ (kFlat_upperStar_mapHomotopyCategory_obj Λ f hA)
  exact derived_map_braiding_aux (QY := Qh) (QX := Qh)
    (Fh := (f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)) (L := L((f)^*⟦Λ⟧))
    (f)^*⟦Λ⟧.leftDerivedFunctorCounit
    (fun K M ↦ ((leftDerivedUpperStarTensor Λ f).app K).app M)
    ((HomotopyCategory.quotient _ _).obj A) ((HomotopyCategory.quotient _ _).obj B)
    (upperStarTensorHomotopyHom Λ f) (leftDerivedUpperStarTensor_app_app_comp Λ f)
    (derivedBraiding_hom_μ_Qh Λ _ _) (derivedBraiding_hom_μ_Qh Λ _ _)
    (upperStarTensorHomotopyHom_braiding Λ f A B)

/-- **The derived pullback of module objects is braided**: the tensor comparison
`m : Lf^* (K ⊗ᴸ M) ⟶ Lf^* K ⊗ᴸ Lf^* M` commutes with the derived braidings,
`Lf^* β_{K, M} ≫ m_{M, K} = m_{K, M} ≫ β_{Lf^* K, Lf^* M}`. -/
theorem leftDerivedUpperStarTensor_braiding
    (K M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    L((f)^*⟦Λ⟧).map (β_ K M).hom ≫ ((leftDerivedUpperStarTensor Λ f).app M).app K =
      ((leftDerivedUpperStarTensor Λ f).app K).app M ≫
        (β_ (L((f)^*⟦Λ⟧).obj K) (L((f)^*⟦Λ⟧).obj M)).hom := by
  have := CachedModInstances.cached_hasTensor₄ObjExt Λ
  have := CachedModInstances.cached_hasGoodTensor₁₂Tensor Λ
  have := CachedModInstances.cached_hasGoodTensorTensor₂₃ Λ
  have := CachedModInstances.cached_hasColimitsOfShape_int Λ
  have := CachedModInstances.cached_hasExactColimitsOfShape_int Λ
  have := CachedModInstances.cached_hasCountableCoproducts Λ
  have := CachedModInstances.cached_preservesColimitsOfShape_int_tensorLeft Λ
  have := CachedModInstances.cached_preservesColimitsOfShape_int_tensorRight Λ
  have := CachedModInstances.cached_hasFunctorialFlatResolution Λ
  have := CachedModInstances.cached_hasTensor Λ
  have := CachedModInstances.cached_preservesColimit_empty_tensorLeft Λ
  have := CachedModInstances.cached_preservesColimit_empty_tensorRight Λ
  have := CachedModInstances.cached_preservesZeroMorphisms_tensorLeft Λ
  have := CachedModInstances.cached_preservesZeroMorphisms_tensorRight Λ
  obtain ⟨P, hP, ⟨eP⟩⟩ := exists_kFlat_iso_Qh_obj Λ K
  obtain ⟨Q, hQ, ⟨eQ⟩⟩ := exists_kFlat_iso_Qh_obj Λ M
  have key := leftDerivedUpperStarTensor_braiding_Qh Λ f P.as Q.as
    ((HomotopyCategory.kFlat_quotient_obj_iff P.as).1 hP)
    ((HomotopyCategory.kFlat_quotient_obj_iff Q.as).1 hQ)
  exact map_braiding_comp_of_iso (fun K M ↦ ((leftDerivedUpperStarTensor Λ f).app K).app M)
    (leftDerivedUpperStarTensor_naturality Λ f) eP eQ key

end AlgebraicGeometry.ProEtale.CondensedRing
