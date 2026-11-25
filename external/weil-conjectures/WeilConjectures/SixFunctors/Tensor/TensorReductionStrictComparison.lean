/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Tensor.TensorReductionFiniteComponents
import WeilConjectures.Algebra.Homology.SixFunctors.SequenceComplexHomAssembly
import WeilConjectures.SixFunctors.Tensor.TensorReductionFiniteComponentEquation

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

/-- The compatible finite maps determine one strict coherent chain map.
Source: Stacks 0941 (blueprint: lem-coef-tensor-reduction-strict-assembly). -/
theorem tensorReductionStrictMap_existsUnique (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) :
    let T := (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)
    let G := (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
    let B := (coefficientTotalTensor.{u, u + 1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)).obj (G.obj P, G.obj Q)
    ∃! ψ : G.obj T ⟶ B, ∀ n : ℕ,
      ((SheafOfModules.systemSequenceEvaluation.{u + 1, u, u + 1}
        (coefficientSequenceCommRingSystem l E W) n).mapHomologicalComplex (.up ℤ)).map ψ =
        tensorReductionSystemFiniteComponent l E W P Q n := by
  let : EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  exact SheafOfModules.sequenceComplexHom_existsUnique _ _ _
    (tensorReductionSystemFiniteComponent l E W P Q)
    (tensorReductionFiniteComponents_compatible l E W P Q)

/-- The strict map is selected from its unique finite-component characterization.
Source: Stacks 07A4, 0941 (blueprint: lem-coef-tensor-reduction-strict-assembly). -/
def tensorReductionStrictMap (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) :
    let T := (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)
    let G := (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
    let B := (coefficientTotalTensor.{u, u + 1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)).obj (G.obj P, G.obj Q)
    G.obj T ⟶ B :=
  (tensorReductionStrictMap_existsUnique l E W P Q).choose

private theorem eq_of_map_conjugate
    {C D : Type*} [Category C] [Category D] {F G : C ⥤ D} (e : F ≅ G)
    {X Y : C} (f : X ⟶ Y) (g : F.obj X ⟶ F.obj Y)
    (h : G.map f = e.inv.app X ≫ g ≫ e.hom.app Y) : F.map f = g := by
  apply (cancel_mono (e.hom.app Y)).1
  rw [e.hom.naturality, h]
  simp only [Iso.hom_inv_id_app_assoc]

/-- In the original evaluation convention the strict map has the prescribed component.
Source: Stacks 0941 (blueprint: lem-coef-tensor-reduction-strict-assembly). -/
theorem tensorReductionStrictMap_component (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) :
    ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).map
      (tensorReductionStrictMap l E W P Q) = tensorReductionFiniteComponent l E W P Q n := by
  have h := (tensorReductionStrictMap_existsUnique l E W P Q).choose_spec.1 n
  rw [tensorReductionSystemFiniteComponent_eq] at h
  exact eq_of_map_conjugate (tensorReductionEvaluationComplexIso l E W n)
    (tensorReductionStrictMap l E W P Q) _ h

end WeilConjectures
