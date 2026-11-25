/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodCompletedTensorReindex.PodCompletionTensorNormalization

import WeilConjectures.PoincareDuality.PodTensorShiftNormalization.PodTensorShiftPresentedModel

/-! # Proved calculations for tensor-shift path normalization

Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 011G, 07A4, 0941
(blueprint: lem-pod-tensor-shift-target-path-assembly-t5).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option cleanup.letToHave false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.integralCompletedTensor WeilConjectures.sfIntegralConstructible
  WeilConjectures.podReindexCalculus

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PodTensorShiftNormalization

attribute [local irreducible] integralOperationsTensorTowerFunctor
attribute [local implicit_reducible] integralOperationsTensorOnGood
  integralOperationsTensorComplexFunctor integralOperationsGoodLocalization podOrdinaryReindex
  podGoodReindex integralOperationsRoosFunctor podShiftTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem target_cancellation
    {A : Type*} [Category A] (W : A × A ⥤ A)
    {A₁ A₂ B₁ B₂ M N U V Z : A}
    (e : W.obj (A₁, A₂) ≅ U) (e' : W.obj (B₁, B₂) ≅ V)
    (f : A₁ ⟶ B₁) (q : A₂ ⟶ B₂) (pe : B₁ ⟶ M) (qe : B₂ ⟶ N)
    (xp : A₁ ⟶ M) (xq : A₂ ⟶ N) (sx : W.obj (M, N) ⟶ Z)
    (tail : V ⟶ Z) (k : U ⟶ V)
    (hp : xp = f ≫ pe) (hq : xq = q ≫ qe)
    (hc : W.map (Prod.mkHom f q) ≫ e'.hom = e.hom ≫ k)
    (hs : W.map (Prod.mkHom pe qe) ≫ sx = e'.hom ≫ tail) :
    e.inv ≫ W.map (Prod.mkHom xp xq) ≫ sx = k ≫ tail := by
  rw [hp, hq, show Prod.mkHom (f ≫ pe) (q ≫ qe) =
    Prod.mkHom f q ≫ Prod.mkHom pe qe from rfl, W.map_comp]
  rw [Category.assoc, hs, ← Category.assoc _ e'.hom tail, hc]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

section Presentations
variable {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

attribute [local irreducible] integralOperationsRoos

variable [(isoReductionIntegralInverse l E g).Additive]
  [PreservesFiniteLimits (isoReductionIntegralInverse l E g)]
  [PreservesFiniteColimits (isoReductionIntegralInverse l E g)]

-- Share the normalized categorical expressions without unfolding coefficient constructions.
/-- Normalize a target path whose input presentation factors through strict good-complex maps.
Substitute the presented tensor model, factor the product presentation, use the target
model formula and naturality of the tensor comparison, and cancel its inverse.
Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 011G, 07A4, 0941
(blueprint: lem-pod-tensor-shift-target-path-assembly-t5). -/
theorem target_path
    (D : PodCompletionReindex l E g) (T : PodCompletedTensorReindex l E g D)
    (hT : PodCompletedTensorReindex.Laws l E g D T)
    (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (M N : sfIntegralConstructibleCategory l E Y)
    (eP : DerivedCategory.Q.obj P.obj ≅ M.obj)
    (eQ : DerivedCategory.Q.obj Q.obj ≅ N.obj)
    (P' Q' : (integralOperationsGoodComplex l E X).FullSubcategory)
    (f : (podGoodReindex l E g D).obj P ⟶ P')
    (q : (podGoodReindex l E g D).obj Q ⟶ Q')
    (pe : DerivedCategory.Q.obj P'.obj ⟶ (podOrdinaryReindex l E g).obj M.obj)
    (qe : DerivedCategory.Q.obj Q'.obj ⟶ (podOrdinaryReindex l E g).obj N.obj)
    (hp : (isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.inv.app P.obj ≫
      (podOrdinaryReindex l E g).map eP.hom = DerivedCategory.Q.map f.hom ≫ pe)
    (hq : (isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.inv.app Q.obj ≫
      (podOrdinaryReindex l E g).map eQ.hom = DerivedCategory.Q.map q.hom ≫ qe)
    (Z : DerivedCategory (scalarReductionSource l E X))
    (sx : (integralCompletedTensor l E X).obj
      ((podOrdinaryReindex l E g).obj M.obj, (podOrdinaryReindex l E g).obj N.obj) ⟶ Z)
    (B : ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E X) ℤ)
    (t : (integralOperationsTensorTowerFunctor l E X).obj (P'.obj, Q'.obj) ⟶ B)
    (tail : DerivedCategory.Q.obj (integralOperationsRoos B) ⟶ Z)
    (hsx : (integralCompletedTensor l E X).map (Prod.mkHom pe qe) ≫ sx =
      (integralCompletedTensorComparison l E X).hom.app (P', Q') ≫
        DerivedCategory.Q.map (integralOperationsRoosMap t) ≫ tail) :
    (podOrdinaryReindex l E g).map
      ((integralCompletedTensor l E Y).map (Prod.mkHom eP.hom eQ.hom)) ≫
      (T.tensor M N).hom ≫ sx =
    ((podOrdinaryReindex l E g).map
      ((integralCompletedTensorComparison l E Y).hom.app (P, Q)) ≫
      (isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app _ ≫
      DerivedCategory.Q.map (D.roos
        ((integralOperationsTensorTowerFunctor l E Y).obj (P.obj, Q.obj))).hom) ≫
      DerivedCategory.Q.map (integralOperationsRoosMap
        ((T.tower P Q).hom ≫
          (integralOperationsTensorTowerFunctor l E X).map (Prod.mkHom f.hom q.hom) ≫ t)) ≫
      tail := by
  dsimp only [integralOperationsTensorOnGood, integralOperationsTensorComplexFunctor,
    integralOperationsGoodLocalization, podOrdinaryReindex, isoReductionIntegralComplex,
    podGoodReindex, integralOperationsRoosFunctor, Functor.comp_obj, Functor.prod_obj,
    ObjectProperty.ι_obj] at *
  have hm := tensor_model_presented l E g D T hT P Q M N eP eQ
  dsimp only [integralOperationsTensorOnGood, integralOperationsTensorComplexFunctor,
    integralOperationsGoodLocalization, podOrdinaryReindex, isoReductionIntegralComplex,
    podGoodReindex, integralOperationsRoosFunctor, Functor.comp_obj, Functor.prod_obj,
    ObjectProperty.ι_obj] at hm
  have hc := (integralCompletedTensorComparison l E X).hom.naturality (Prod.mkHom f q)
  dsimp only [integralOperationsTensorOnGood, integralOperationsTensorComplexFunctor,
    integralOperationsGoodLocalization, podOrdinaryReindex, isoReductionIntegralComplex,
    podGoodReindex, integralOperationsRoosFunctor, Functor.comp_obj, Functor.prod_obj,
    ObjectProperty.ι_obj] at hc
  change (integralCompletedTensor l E X).map
      (Prod.mkHom (DerivedCategory.Q.map f.hom) (DerivedCategory.Q.map q.hom)) ≫
      (integralCompletedTensorComparison l E X).hom.app (P', Q') =
    (integralCompletedTensorComparison l E X).hom.app
      ((podGoodReindex l E g D).obj P, (podGoodReindex l E g D).obj Q) ≫
      DerivedCategory.Q.map (integralOperationsRoosMap
        ((integralOperationsTensorTowerFunctor l E X).map (Prod.mkHom f.hom q.hom))) at hc
  have ht := target_cancellation (integralCompletedTensor l E X)
    ((integralCompletedTensorComparison l E X).app
      ((podGoodReindex l E g D).obj P, (podGoodReindex l E g D).obj Q))
    ((integralCompletedTensorComparison l E X).app (P', Q'))
    (DerivedCategory.Q.map f.hom) (DerivedCategory.Q.map q.hom) pe qe _ _ sx
    (DerivedCategory.Q.map (integralOperationsRoosMap t) ≫ tail)
    (DerivedCategory.Q.map (integralOperationsRoosMap
      ((integralOperationsTensorTowerFunctor l E X).map (Prod.mkHom f.hom q.hom))))
    hp hq hc (by simpa only [Iso.app_hom, integralOperationsGoodLocalization,
      Functor.comp_obj, ObjectProperty.ι_obj, Category.assoc] using hsx)
  have h₁ := congrArg (fun k ↦ k ≫ sx) hm
  have h₂ := congrArg (fun k ↦
    (podOrdinaryReindex l E g).map
      ((integralCompletedTensorComparison l E Y).hom.app (P, Q)) ≫
      (isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app _ ≫
      DerivedCategory.Q.map (D.roos
        ((integralOperationsTensorTowerFunctor l E Y).obj (P.obj, Q.obj))).hom ≫
      DerivedCategory.Q.map (integralOperationsRoosMap (T.tower P Q).hom) ≫ k) ht
  dsimp only [integralOperationsTensorOnGood, integralOperationsTensorComplexFunctor,
    integralOperationsGoodLocalization, podOrdinaryReindex, isoReductionIntegralComplex,
    podGoodReindex, integralOperationsRoosFunctor, Functor.comp_obj, Functor.prod_obj,
    ObjectProperty.ι_obj] at h₂
  simp only [Iso.app_inv, Category.assoc] at h₁ h₂
  simpa only [integralOperationsRoosMap_comp, Functor.map_comp, Category.assoc]
    using h₁.trans h₂

end Presentations
end WeilConjectures.PodTensorShiftNormalization
