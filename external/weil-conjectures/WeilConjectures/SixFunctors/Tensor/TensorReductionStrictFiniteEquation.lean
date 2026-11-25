/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Tensor.TensorReductionStrictComparison

/-! # Assembling the ordinary coherent reduction tensor comparison

Source: Stacks 07A4 and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  completedIntegralCommRingSheafUnrestricted completedIntegralCoefficientSheafUnrestricted
  coefficientTotalTensor CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory pullbackTensorCalculus
attribute [local irreducible] pullbackTensorReductionEvaluationComplex
  coefficientScalarTensorIso coefficientEvaluationTensorIso
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem cancel_tensor_comparisons
    {C D : Type*} [Category C] [Category D] (F : C × C ⥤ D)
    {A A' B B' : C} (a : A ≅ A') (b : B ≅ B') {X Z Y : D}
    (f : X ⟶ Z) (g : Z ⟶ F.obj (A, B)) (e : Y ≅ F.obj (A', B')) :
    (f ≫ g ≫ F.map (Prod.mkHom a.hom b.hom) ≫ e.inv) ≫ e.hom ≫
      F.map (Prod.mkHom a.inv b.inv) = f ≫ g := by
  have h : Prod.mkHom a.hom b.hom ≫ Prod.mkHom a.inv b.inv = 𝟙 (A, B) := by
    apply Prod.ext <;> simp
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← F.map_comp, h, F.map_id, Category.comp_id]

/-- The strict map satisfies the scalar tensor equation before localization.
Source: Stacks 07A4 (blueprint: lem-coef-tensor-reduction-strict-finite-equation). -/
theorem tensorReductionStrictMap_finite (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) :
    let T := (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)
    let G := (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
    ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map
        (tensorReductionStrictMap l E W P Q) ≫
      (coefficientEvaluationTensorIso l E W n (G.obj P) (G.obj Q)).hom ≫
      (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)).map
        (Prod.mkHom ((pullbackTensorReductionEvaluationComplex l E W n).inv.app P)
          ((pullbackTensorReductionEvaluationComplex l E W n).inv.app Q)) =
      (pullbackTensorReductionEvaluationComplex l E W n).inv.app T ≫
        (coefficientScalarTensorIso l E W n P Q).hom := by
  dsimp only
  rw [tensorReductionStrictMap_component]
  exact cancel_tensor_comparisons
    (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n))
    ((pullbackTensorReductionEvaluationComplex l E W n).app P)
    ((pullbackTensorReductionEvaluationComplex l E W n).app Q)
    ((pullbackTensorReductionEvaluationComplex l E W n).inv.app _)
    (coefficientScalarTensorIso l E W n P Q).hom
    (coefficientEvaluationTensorIso l E W n _ _)

end WeilConjectures
