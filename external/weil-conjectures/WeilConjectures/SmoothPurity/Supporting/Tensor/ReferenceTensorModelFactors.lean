/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations

/-! # The defining factors of the reference completed tensor model

Source: Stacks 07A4 and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.coefficientSequenceEssentiallySmall

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory
  pullbackTensorCalculus coefficientTotalTensor

attribute [local irreducible] pullbackTensorReductionModel pullbackTensorSystemModel
  pullbackTensorLimitRoos pullbackTensorTensorTower in
/-- The hom component of the fixed reference tensor model is its four defining factors.
Source: Stacks 07A4 and 0941; the definition of the reference tensor realization
(blueprint: lem-pur-reference-tensor-model-factors).

Proof: expand the four composed isomorphisms, the two functor images and the
product isomorphism. Their hom components are exactly the four displayed maps.
No inverse-limit or derived-faithfulness argument is used. -/
theorem pullbackTensorReferenceTensorModel_hom (W : Scheme.{u})
    (P Q : (integralOperationsGoodComplex l E W).FullSubcategory) :
    let T := pullbackTensorCalculus l E W
    let R := (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
    (pullbackTensorReferenceTensorModel l E W P Q).hom =
      (coefficientSequenceLimit l E W).map
        (T.systemClosed.tensor.map
          (Prod.mkHom ((pullbackTensorReductionModel l E W).hom.app P)
            ((pullbackTensorReductionModel l E W).hom.app Q))) ≫
      (coefficientSequenceLimit l E W).map
        (pullbackTensorSystemModel l E W (R.obj P.obj) (R.obj Q.obj)
          (pullbackTensorReductionGood l E W P) (pullbackTensorReductionGood l E W Q)).inv ≫
      (pullbackTensorLimitRoos l E W
        ((coefficientTotalTensor.{u, u + 1, u}
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)).obj (R.obj P.obj, R.obj Q.obj))).hom ≫
      DerivedCategory.Q.map (integralOperationsRoosFunctor.map
        (pullbackTensorTensorTower l E W P.obj Q.obj).hom) := by
  dsimp only
  simp only [pullbackTensorReferenceTensorModel, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.prod_hom, Iso.app_hom]

end WeilConjectures
