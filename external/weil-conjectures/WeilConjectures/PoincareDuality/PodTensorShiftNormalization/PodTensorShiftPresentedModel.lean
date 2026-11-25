/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodCompletedTensorReindex.PodCompletionTensorNormalization

import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated

/-! # Proved calculations for tensor-shift path normalization

Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 011G, 07A4, 0941
(blueprint: lem-pod-tensor-shift-presented-model-t5).
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

section Presentations
variable {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

variable [(isoReductionIntegralInverse l E g).Additive]
  [PreservesFiniteLimits (isoReductionIntegralInverse l E g)]
  [PreservesFiniteColimits (isoReductionIntegralInverse l E g)]

attribute [local irreducible] integralOperationsRoos

-- Share the normalized categorical expressions without unfolding coefficient constructions.
/-- The normalized tensor model holds for arbitrary constructible presentations.
Transport constructibility along the presentations, apply Model and Naturality, and cancel
the adjacent tensor and exact-derived comparison isomorphisms.
Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 011G, 07A4, 0941
(blueprint: lem-pod-tensor-shift-presented-model-t5). -/
theorem tensor_model_presented
    (D : PodCompletionReindex l E g) (T : PodCompletedTensorReindex l E g D)
    (hT : PodCompletedTensorReindex.Laws l E g D T)
    (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (M N : sfIntegralConstructibleCategory l E Y)
    (eP : DerivedCategory.Q.obj P.obj ≅ M.obj)
    (eQ : DerivedCategory.Q.obj Q.obj ≅ N.obj) :
    let F := podOrdinaryReindex l E g
    let W := integralCompletedTensor l E X
    let φ := (isoReductionIntegralInverse l E g).mapDerivedCategoryFactors
    F.map ((integralCompletedTensor l E Y).map (Prod.mkHom eP.hom eQ.hom)) ≫
        (T.tensor M N).hom =
      F.map ((integralCompletedTensorComparison l E Y).hom.app (P, Q)) ≫
        φ.hom.app _ ≫ DerivedCategory.Q.map (D.roos
          ((integralOperationsTensorTowerFunctor l E Y).obj (P.obj, Q.obj))).hom ≫
        DerivedCategory.Q.map (integralOperationsRoosMap (T.tower P Q).hom) ≫
        (integralCompletedTensorComparison l E X).inv.app
          ((podGoodReindex l E g D).obj P, (podGoodReindex l E g D).obj Q) ≫
        W.map (Prod.mkHom (φ.inv.app P.obj ≫ F.map eP.hom)
          (φ.inv.app Q.obj ≫ F.map eQ.hom)) := by
  dsimp only [integralOperationsTensorOnGood, integralOperationsTensorComplexFunctor,
    integralOperationsGoodLocalization, podOrdinaryReindex, isoReductionIntegralComplex,
    podGoodReindex, integralOperationsRoosFunctor, Functor.comp_obj, Functor.prod_obj,
    ObjectProperty.ι_obj] at *
  have hP := (sfIntegralConstructible l E Y).prop_of_iso eP.symm M.property
  have hQ := (sfIntegralConstructible l E Y).prop_of_iso eQ.symm N.property
  have hm := eq_of_heq (hT.2.2.2.2.1 P Q hP hQ)
  have hn := hT.2.2.2.1 ⟨_, hP⟩ ⟨_, hQ⟩ M N
    ⟨eP.hom⟩ ⟨eQ.hom⟩
  dsimp only [integralOperationsTensorOnGood, integralOperationsTensorComplexFunctor,
    integralOperationsGoodLocalization, podOrdinaryReindex, isoReductionIntegralComplex,
    podGoodReindex, integralOperationsRoosFunctor, Functor.comp_obj, Functor.prod_obj,
    ObjectProperty.ι_obj] at hn hm
  have hm' := congrArg (fun k ↦ k ≫
    (integralCompletedTensorComparison l E X).inv.app
      ((podGoodReindex l E g D).obj P, (podGoodReindex l E g D).obj Q) ≫
    (integralCompletedTensor l E X).map (Prod.mkHom
      ((isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.inv.app P.obj ≫
        (podOrdinaryReindex l E g).map eP.hom)
      ((isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.inv.app Q.obj ≫
        (podOrdinaryReindex l E g).map eQ.hom))) hm
  dsimp only [integralOperationsTensorOnGood, integralOperationsTensorComplexFunctor,
    integralOperationsGoodLocalization, podOrdinaryReindex, isoReductionIntegralComplex,
    podGoodReindex, integralOperationsRoosFunctor, Functor.comp_obj, Functor.prod_obj,
    ObjectProperty.ι_obj] at hm'
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc] at hm'
  simp only [← Functor.map_comp, prod_comp] at hm'
  simp only [Iso.hom_inv_id_app_assoc] at hm'
  simpa only [Functor.map_comp, Category.assoc] using hn.trans hm'.symm

end Presentations
end WeilConjectures.PodTensorShiftNormalization
