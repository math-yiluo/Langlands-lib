/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
import WeilConjectures.CategoryTheory.SignedCoconeShift.SignedMappingCoconeShift
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

/-! # Ordinary-limit comparison with the full Roos complex

Source: Stacks 08TC and 0941; the normalization of
`pullbackTensorRoosModel_existsUnique`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
attribute [local implicit_reducible] integralOperationsRoos integralOperationsTowerStep
  pullbackTensorOrdinaryLimit pullbackTensorConstantLimit pullbackTensorTowerQ
  coefficientConstantTowerLimit
attribute [local irreducible] HasDerivedCategory.standard
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/- The elementary two-coordinate identity avoids importing the tensor theory.
Source: Mathlib mappingCocone.id_X. -/
private theorem mappingCocone_hom_ext {A : Type*} [Category A] [Abelian A]
    {K L M : CochainComplex A ℤ} (φ : K ⟶ L)
    {f g : M ⟶ CochainComplex.mappingCocone φ}
    (hfst : f ≫ CochainComplex.mappingCocone.fst φ =
      g ≫ CochainComplex.mappingCocone.fst φ)
    (hsnd : ∀ i : ℤ, f.f i ≫
      (CochainComplex.mappingCocone.snd φ).v i (i - 1) (by omega) =
      g.f i ≫ (CochainComplex.mappingCocone.snd φ).v i (i - 1) (by omega)) : f = g := by
  apply HomologicalComplex.hom_ext
  intro i
  have h := congrArg (fun a ↦ a.f i) hfst
  have he := CochainComplex.mappingCocone.id_X φ i (i - 1) (by omega)
  calc
    f.f i = f.f i ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = f.f i ≫ ((CochainComplex.mappingCocone.fst φ).f i ≫
        (CochainComplex.mappingCocone.inl φ).v i i (add_zero i) +
      (CochainComplex.mappingCocone.snd φ).v i (i - 1) (by omega) ≫
        (CochainComplex.mappingCocone.inr φ).1.v (i - 1) i (by omega)) := by rw [he]
    _ = g.f i ≫ ((CochainComplex.mappingCocone.fst φ).f i ≫
        (CochainComplex.mappingCocone.inl φ).v i i (add_zero i) +
      (CochainComplex.mappingCocone.snd φ).v i (i - 1) (by omega) ≫
        (CochainComplex.mappingCocone.inr φ).1.v (i - 1) i (by omega)) := by
      simp only [Preadditive.comp_add, ← Category.assoc]
      rw [show f.f i ≫ (CochainComplex.mappingCocone.fst φ).f i =
        g.f i ≫ (CochainComplex.mappingCocone.fst φ).f i from h, hsnd i]
    _ = g.f i := by rw [he, Category.comp_id]

private theorem roosMap_fst {A : Type*} [Category A] [Abelian A]
    [HasCountableProducts A] {C D : ℕᵒᵖ ⥤ CochainComplex A ℤ} (f : C ⟶ D) :
    integralOperationsRoosMap f ≫ CochainComplex.mappingCocone.fst
        (towerTransitionEndomorphism (K := fun n ↦ D.obj (op n))
          (integralOperationsTowerStep D)) =
      CochainComplex.mappingCocone.fst
        (towerTransitionEndomorphism (K := fun n ↦ C.obj (op n))
          (integralOperationsTowerStep C)) ≫
          Limits.Pi.map (fun n ↦ f.app (op n)) := by
  apply HomologicalComplex.hom_ext
  intro i
  apply CategoryTheory.SignedCoconeShift.cocone_ext_from _ i
  · simp only [HomologicalComplex.comp_f, integralOperationsRoosMap,
      ← Category.assoc]
    erw [CategoryTheory.SignedCoconeShift.coconeMap_inl_assoc]
    simp
  · simp only [HomologicalComplex.comp_f, integralOperationsRoosMap,
      ← Category.assoc]
    erw [CategoryTheory.SignedCoconeShift.coconeMap_inr_assoc]
    simp

private theorem roosMap_snd {A : Type*} [Category A] [Abelian A]
    [HasCountableProducts A] {C D : ℕᵒᵖ ⥤ CochainComplex A ℤ} (f : C ⟶ D) (i : ℤ) :
    (integralOperationsRoosMap f).f i ≫ (CochainComplex.mappingCocone.snd
        (towerTransitionEndomorphism (K := fun n ↦ D.obj (op n))
          (integralOperationsTowerStep D))).v
          i (i - 1) (by omega) =
      (CochainComplex.mappingCocone.snd
        (towerTransitionEndomorphism (K := fun n ↦ C.obj (op n))
          (integralOperationsTowerStep C))).v
          i (i - 1) (by omega) ≫ (Limits.Pi.map (fun n ↦ f.app (op n))).f (i - 1) := by
  apply CategoryTheory.SignedCoconeShift.cocone_ext_from _ i
  · simp only [integralOperationsRoosMap, ← Category.assoc]
    erw [CategoryTheory.SignedCoconeShift.coconeMap_inl]
    simp
  · simp only [integralOperationsRoosMap, ← Category.assoc]
    erw [CategoryTheory.SignedCoconeShift.coconeMap_inr]
    simp

private theorem roosUnit_natural (W : Scheme.{u})
    {C D : CochainComplex (ℕᵒᵖ ⥤ integralTowerModules l E W) ℤ} (f : C ⟶ D) :
    ((pullbackTensorConstantLimit l E W).mapHomologicalComplex (.up ℤ)).map f ≫
        pullbackTensorRoosUnit l E W D =
      pullbackTensorRoosUnit l E W C ≫ integralOperationsRoosMap
        (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f) := by
  apply mappingCocone_hom_ext
  · simp only [Category.assoc]
    erw [roosMap_fst]
    simp only [pullbackTensorRoosUnit, CochainComplex.mappingCocone.lift_fst,
      CochainComplex.mappingCocone.lift_fst_assoc]
    apply Limits.Pi.hom_ext
    intro n
    dsimp only [pullbackTensorRoosAugmentation]
    simp only [Category.assoc, Limits.Pi.map_π]
    erw [Limits.Pi.lift_comp_π, Limits.Pi.lift_comp_π_assoc]
    exact (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).naturality f
  · intro i
    erw [HomologicalComplex.comp_f, Category.assoc]
    simp only [pullbackTensorRoosUnit, CochainComplex.mappingCocone.lift_f_snd_v,
      CochainComplex.HomComplex.Cochain.zero_v, comp_zero]
    erw [HomologicalComplex.comp_f, Category.assoc, roosMap_snd, ← Category.assoc]
    simp only [CochainComplex.mappingCocone.lift_f_snd_v,
      CochainComplex.HomComplex.Cochain.zero_v, zero_comp]

private theorem unitQ_eq (W : Scheme.{u})
    (C : CochainComplex (ℕᵒᵖ ⥤ integralTowerModules l E W) ℤ) :
    (pullbackTensorConstantLimit l E W).rightDerivedFunctorUnitQ C =
      (DerivedCategory.quotientCompQhIso (integralTowerModules l E W)).inv.app
          (((pullbackTensorConstantLimit l E W).mapHomologicalComplex (.up ℤ)).obj C) ≫
        (pullbackTensorConstantLimit l E W).rightDerivedFunctorUnit.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj C) ≫
        (pullbackTensorConstantLimit l E W).rightDerivedFunctor.map
          ((DerivedCategory.quotientCompQhIso (ℕᵒᵖ ⥤ integralTowerModules l E W)).hom.app C) :=
  rfl

private theorem towerLimitUnit_roos (W : Scheme.{u})
    (C : CochainComplex (ℕᵒᵖ ⥤ integralTowerModules l E W) ℤ) :
    (pullbackTensorConstantLimit l E W).rightDerivedFunctorUnitQ C ≫
        (pullbackTensorRoosModel l E W).hom.app C =
      DerivedCategory.Q.map (pullbackTensorRoosUnit l E W C) := by
  obtain ⟨I, hI, q, _, hq⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective C
  have : I.IsKInjective := hI
  have : QuasiIso q := hq
  let R : CochainComplex (ℕᵒᵖ ⥤ integralTowerModules l E W) ℤ ⥤
      DerivedCategory (integralTowerModules l E W) :=
    HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
    integralOperationsRoosFunctor ⋙ DerivedCategory.Q
  have hi : IsIso (R.map q) := by
    apply (NatIso.isIso_map_iff (pullbackTensorRoosModel l E W) q).mp
    change IsIso ((coefficientConstantTowerLimit l E W).map (DerivedCategory.Q.map q))
    infer_instance
  apply (cancel_mono (R.map q)).mp
  erw [Category.assoc, ← (pullbackTensorRoosModel l E W).hom.naturality]
  change _ ≫ ((coefficientConstantTowerLimit l E W).map (DerivedCategory.Q.map q) ≫
    (pullbackTensorRoosModel l E W).hom.app I) = _
  erw [← Category.assoc, ← Functor.rightDerivedFunctorUnitQ_naturality]
  erw [Category.assoc, Functor.rightDerivedFunctorUnitQ_eq]
  have hnorm := (pullbackTensorRoosModel_existsUnique l E W).exists.choose_spec I
  change (pullbackTensorRoosModel l E W).hom.app I = _ at hnorm
  erw [hnorm, Iso.inv_hom_id_assoc, ← DerivedCategory.Q.map_comp]
  change DerivedCategory.Q.map _ = DerivedCategory.Q.map _ ≫
    DerivedCategory.Q.map (integralOperationsRoosMap
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q))
  rw [← DerivedCategory.Q.map_comp]
  exact congrArg DerivedCategory.Q.map (roosUnit_natural l E W q)

/-- The universal ordinary-to-derived limit map is the zero-homotopy Roos lift,
after the prescribed comparison. This assertion is about an arbitrary strict
system complex and does not involve tensor or any flatness hypothesis.

Source: Stacks 08TC, 0941; normalization of the right-derived limit comparison.
Proof: resolve the restricted tower by a K-injective tower. On that tower the
right-derived comparison is the inverse ordinary-limit identification, so the
normalization of pullbackTensorRoosModel cancels it and leaves exactly the
(limit projections, zero) lift. Naturality of the universal derived-limit map,
the Roos comparison and this chain lift transports the equality back to the
original tower. The Roos image of the resolution is invertible because the
published Roos model is an isomorphism of functors and derived localization
inverts the resolution. Finally insert the complex-composition comparison for
restriction followed by ordinary limit.
(blueprint: lem-coef-limit-unit-roos-normalization). -/
theorem pullbackTensorLimitUnit_roos (W : Scheme.{u})
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ) :
    pullbackTensorLimitUnit l E W C ≫ (pullbackTensorLimitRoos l E W C).hom =
      DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso
          (Iso.refl (coefficientSequenceRestriction l E W ⋙
            pullbackTensorConstantLimit l E W)) (.up ℤ)).inv.app C) ≫
      DerivedCategory.Q.map (pullbackTensorRoosUnit l E W
        (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj C)) := by
  calc
    _ = (DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso
            (Iso.refl (coefficientSequenceRestriction l E W ⋙
              pullbackTensorConstantLimit l E W)) (.up ℤ)).inv.app C) ≫
          (pullbackTensorConstantLimit l E W).rightDerivedFunctorUnitQ
            (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj C) ≫
          (coefficientConstantTowerLimit l E W).map
            ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv.app C)) ≫
        ((coefficientConstantTowerLimit l E W).map
            ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.hom.app C) ≫
          (pullbackTensorRoosModel l E W).hom.app
            (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj C)) := by
      unfold pullbackTensorLimitUnit pullbackTensorLimitRoos
      erw [unitQ_eq]
      rfl
    _ = DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso
            (Iso.refl (coefficientSequenceRestriction l E W ⋙
              pullbackTensorConstantLimit l E W)) (.up ℤ)).inv.app C) ≫
        ((pullbackTensorConstantLimit l E W).rightDerivedFunctorUnitQ
            (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj C) ≫
          (pullbackTensorRoosModel l E W).hom.app
            (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj C)) := by
      simp only [Category.assoc]
      congr 2
      erw [← Functor.map_comp_assoc, Iso.inv_hom_id_app,
        (coefficientConstantTowerLimit l E W).map_id, Category.id_comp]
    _ = _ := by
      rw [towerLimitUnit_roos]
      rfl

end WeilConjectures
