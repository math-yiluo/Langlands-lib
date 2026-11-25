/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodCompletedTensorReindex.PodCompletionTensorModels
public import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingReductionTensorSquare
import all WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTensorModelNormalization
import WeilConjectures.SmoothPurity.Supporting.Tensor.ReferenceTensorModelFactors

/-! # Derived reduction of the strict Roos normalization

The coherent tensor comparison of `podReindexingLimitTensorComparisonHom` is reduced, on
good representatives, to two strict statements: a system-level identification of the
coherent system tensor comparison with an actual chain map `σ`, and an equation of
strict tensor towers.

Source: blueprint dual-Tate compatibility, Steps 2 and 4; Stacks 07A4, 08TC, 0941
(blueprint: stage3-pod-reindexing-coherent-tensor-roos).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Every Roos model of the total limit gives the reference total-limit/Roos comparison.
Source: Stacks 08TC, 0941 (blueprint: stage3-pod-reindexing-coherent-tensor-roos). -/
theorem podLimitRoos_eq_pullbackTensorLimitRoos (W : Scheme.{u})
    (ρ : IntegralComparisonRoosModel l E W)
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ) :
    podLimitRoos l E ρ C = pullbackTensorLimitRoos l E W C := by
  exact (ScalarExtensionTower.roosBridge_eq l E W ρ C).symm

/-- On good representatives, the tensor realization is the defining comparison followed
by the inverse reference Roos model.
Source: Stacks 07A4, 0941 (blueprint: stage3-pod-reindexing-coherent-tensor-roos). -/
theorem podReindexingTensorModel_hom_app_good (W : Scheme.{u})
    (P Q : (integralOperationsGoodComplex l E W).FullSubcategory) :
    (podReindexingTensorModel l E W).hom.app
        (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) =
      (integralCompletedTensorComparison l E W).hom.app (P, Q) ≫
        (pullbackTensorReferenceTensorModel l E W P Q).inv := by
  have h := (pullbackTensorIntegralTensorModel_existsUnique l E W).exists.choose_spec
  unfold pullbackTensorIntegralTensorNormalization at h
  have hPQ := congrArg Iso.hom (h P Q)
  unfold podReindexingTensorModel pullbackTensorIntegralTensorModel
  exact hPQ

/-- The categorical pasting behind `podReindexing_tensor_roos_of_strict`.
Source: Stacks 07A4, 08TC, 0941 (blueprint: stage3-pod-reindexing-coherent-tensor-roos). -/
theorem coherentTensorRoos_paste {DY DX SY SX TW : Type*} [Category* DY] [Category* DX]
    [Category* SY] [Category* SX] [Category* TW]
    (F : DY ⥤ DX) (LY : SY ⥤ DY) (LX : SX ⥤ DX) (G : SY ⥤ SX) (δ : LY ⋙ F ⟶ G ⋙ LX)
    (H : TW ⥤ DX)
    {C₀ C₁ M₁ : DY} {U S₁ S : SY} {A₁ A₂ A₃ A₄ A₅ A₆ : SX}
    {Z₀ Z₁ Z₄ Z₅ : DX} {T₀ T₁ Tr Ts T₂ : TW}
    (cY : C₀ ⟶ C₁) (dYh : C₀ ⟶ LY.obj U) (refY : LY.obj U ≅ C₁)
    (k₁ : U ⟶ S₁) (k₂ : S₁ ⟶ S) (kinv₁ : S ⟶ S₁) (kinv₂ : S₁ ⟶ U)
    (limY : LY.obj S ⟶ M₁) (ttY : M₁ ⟶ C₁)
    (w₁ : G.obj U ⟶ A₁) (w₂ : A₁ ⟶ A₂) (tRf : A₂ ⟶ A₃) (k'₁ : A₃ ⟶ A₆) (k'₂ : A₆ ⟶ A₄)
    (wAll : A₁ ⟶ A₆) (Ifac : G.obj S ⟶ A₅) (qσ : A₅ ⟶ A₄)
    (dXi : LX.obj A₂ ⟶ Z₀) (Tf : Z₀ ⟶ Z₁) (dXi' : LX.obj A₃ ⟶ Z₁) (cX : Z₁ ⟶ H.obj T₂)
    (refX : LX.obj A₃ ≅ H.obj T₂)
    (limXS : LX.obj A₄ ⟶ H.obj Ts) (limXI : LX.obj A₅ ⟶ H.obj Tr)
    (fac : F.obj C₁ ⟶ Z₄) (fac' : F.obj M₁ ⟶ Z₅) (isoTT : Z₅ ⟶ Z₄) (roos : Z₄ ⟶ H.obj T₁)
    (roos' : Z₅ ⟶ H.obj T₀)
    (ttRhom : T₀ ⟶ T₁) (ttRinv : T₁ ⟶ T₀) (resT : T₀ ⟶ Tr) (σT : Tr ⟶ Ts) (ttXT : Ts ⟶ T₂)
    (τT : T₁ ⟶ T₂)
    (hY : dYh = cY ≫ refY.inv)
    (hXn : LX.map tRf ≫ dXi' = dXi ≫ Tf)
    (hXi : dXi' ≫ cX = refX.hom)
    (hrefX : refX.hom = LX.map k'₁ ≫ LX.map k'₂ ≫ limXS ≫ H.map ttXT)
    (hrefY : refY.hom = LY.map k₁ ≫ LY.map k₂ ≫ limY ≫ ttY)
    (hk₁ : k₁ ≫ kinv₂ = 𝟙 U) (hk₂ : k₂ ≫ kinv₁ = 𝟙 S₁)
    (hfac : F.map ttY ≫ fac = fac' ≫ isoTT)
    (hroos : isoTT ≫ roos = roos' ≫ H.map ttRhom)
    (hR : ttRhom ≫ ttRinv = 𝟙 T₀)
    (hτ : ttRinv ≫ resT ≫ σT ≫ ttXT = τT)
    (hlim : F.map limY ≫ fac' ≫ roos' ≫ H.map resT = δ.app S ≫ LX.map Ifac ≫ limXI)
    (hlimnat : limXI ≫ H.map σT = LX.map qσ ≫ limXS)
    (hw : wAll = w₂ ≫ tRf ≫ k'₁)
    (hσ : G.map (kinv₁ ≫ kinv₂) ≫ w₁ ≫ wAll ≫ k'₂ = Ifac ≫ qσ)
    (roosAll : Z₄ ⟶ H.obj T₂) (hsplit : roosAll = roos ≫ H.map τT) :
    F.map dYh ≫ δ.app U ≫ LX.map w₁ ≫ LX.map w₂ ≫ dXi ≫ Tf ≫ cX =
      F.map cY ≫ fac ≫ roosAll := by
  subst hsplit hw hτ
  have hδ := δ.naturality (k₁ ≫ k₂)
  dsimp only [Functor.comp_map] at hδ
  have hσ' : w₁ ≫ w₂ ≫ tRf ≫ k'₁ ≫ k'₂ = G.map (k₁ ≫ k₂) ≫ Ifac ≫ qσ := by
    rw [← hσ, ← G.map_comp_assoc]
    simp only [Category.assoc]
    rw [reassoc_of% hk₂, hk₁, G.map_id, Category.id_comp]
  have hX : dXi ≫ Tf ≫ cX = LX.map tRf ≫ LX.map k'₁ ≫ LX.map k'₂ ≫ limXS ≫ H.map ttXT := by
    rw [← reassoc_of% hXn, hXi, hrefX]
  have hR' : H.map ttRhom ≫ H.map ttRinv ≫ H.map resT ≫ H.map σT ≫ H.map ttXT =
      H.map resT ≫ H.map σT ≫ H.map ttXT := by
    rw [← H.map_comp_assoc, hR, H.map_id, Category.id_comp]
  have hRY : F.map refY.hom ≫ fac ≫ roos ≫ H.map (ttRinv ≫ resT ≫ σT ≫ ttXT) =
      δ.app U ≫ LX.map w₁ ≫ LX.map w₂ ≫ LX.map tRf ≫ LX.map k'₁ ≫ LX.map k'₂ ≫ limXS ≫
        H.map ttXT := by
    rw [hrefY]
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% hfac, reassoc_of% hroos, hR', reassoc_of% hlim, reassoc_of% hlimnat]
    simp only [← Functor.map_comp_assoc]
    rw [← LY.map_comp, reassoc_of% hδ, ← LX.map_comp_assoc, hσ']
  rw [hY, F.map_comp, Category.assoc, hX, ← hRY]
  simp only [← F.map_comp_assoc, Iso.inv_hom_id, F.map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The inverse form of `podReindexingTensorModel_hom_app_good`.
Source: Stacks 07A4, 0941 (blueprint: stage3-pod-reindexing-coherent-tensor-roos). -/
theorem podReindexingTensorModel_inv_app_good (W : Scheme.{u})
    (P Q : (integralOperationsGoodComplex l E W).FullSubcategory) :
    (podReindexingTensorModel l E W).inv.app
        (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
      (integralCompletedTensorComparison l E W).hom.app (P, Q) =
        (pullbackTensorReferenceTensorModel l E W P Q).hom := by
  rw [← Iso.app_inv, Iso.inv_comp_eq, Iso.app_hom, podReindexingTensorModel_hom_app_good,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- The reference total-limit/Roos comparison is natural in the coherent complex.
Source: Stacks 08TC, 0941 (blueprint: stage3-pod-reindexing-coherent-tensor-roos). -/
theorem pullbackTensorLimitRoos_naturality (W : Scheme.{u})
    {C C' : CochainComplex (coefficientSequenceModules l E W) ℤ} (f : C ⟶ C') :
    (pullbackTensorLimitRoos l E W C).hom ≫
        DerivedCategory.Q.map (integralOperationsRoosFunctor.map
          (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).map f))) =
      (coefficientSequenceLimit l E W).map (DerivedCategory.Q.map f) ≫
        (pullbackTensorLimitRoos l E W C').hom := by
  have h₁ := (coefficientSequenceRestriction l E W).mapDerivedCategoryFactors_hom_naturality f
  have h₂ := (pullbackTensorRoosModel l E W).hom.naturality
    (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).map f)
  dsimp only [Functor.comp_map] at h₂
  unfold pullbackTensorLimitRoos coefficientSequenceLimit
  rw [Iso.trans_hom, Iso.trans_hom, Functor.mapIso_hom, Functor.mapIso_hom, Iso.app_hom,
    Iso.app_hom, Iso.app_hom, Iso.app_hom, Category.assoc, ← h₂, ← Functor.map_comp_assoc,
    Functor.comp_map, ← Functor.map_comp_assoc]
  congr 2
  exact h₁.symm

end WeilConjectures
