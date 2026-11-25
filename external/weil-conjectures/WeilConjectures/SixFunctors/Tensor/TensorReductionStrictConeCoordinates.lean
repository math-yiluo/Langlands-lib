/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerCore
public import WeilConjectures.SixFunctors.Tensor.TensorReductionEvaluationIdentification
public import WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels
import WeilConjectures.PoincareDuality.StrictTensorAugmentation.StrictTensorAugmentation

/-! # Strict tensor cone coordinates

The ordinary quotient augmentation forms a strict cone whose finite coordinates
are the normalized scalar tensor transposes. Source: Stacks 03EK and 07A4.
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
  CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory pullbackTensorCalculus
attribute [local irreducible] coefficientScalarTensorIso coefficientEvaluationTensorIso
  constantSheaf
attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  coefficientSequenceCommRingSheaf coefficientSequenceCommRingPresheaf
  coefficientSequenceCommRingSystem SheafOfModules.systemSequenceRing
  SheafOfModules.systemSequenceRingPresheaf
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local implicit_reducible] IntegralOnSlice.ring IntegralOnSlice.restrict
  IntegralOnSlice.topology IntegralOnSlice.Site IntegralOnSlice.siteCategory
  IntegralAmbient.tensorTower pullbackTensorRestrictedTower
  integralOperationsTensorComplexFunctor integralOperationsRoosFunctor
  unrestrictedIntegralReductionFunctor
  integralOperationsRoos integralOperationsTensorTowerFunctor
  integralOperationsTensorLevel integralOperationsTensorComposite integralOperationsFiniteMonoidal
  pullbackTensorOrdinaryLimit

attribute [local irreducible] coefficientSequenceRestriction
  pullbackTensorOrdinaryAdjunction

/-- The quotient augmentation followed by the normalized strict tensor comparison.
Source: Stacks 03EK and 07A4
(blueprint: lem-coef-tensor-reduction-strict-cone-coordinates). -/
def tensorReductionStrictConeMap (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) :
    (Functor.const ℕᵒᵖ).obj
      ((coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)) ⟶
      (integralOperationsTensorTowerFunctor l E W).obj (P, Q) :=
  (IntegralOnSlice.augmentation l E W none).app _ ≫
    (IntegralAmbient.tensorTowerIso l E W).hom.app (P, Q)

attribute [local irreducible] tensorReductionStrictConeMap

/-- A strict cone with vertex the integral total tensor.
Source: Stacks 03EK and 07A4
(blueprint: lem-coef-tensor-reduction-strict-cone-coordinates). -/
def tensorReductionStrictCone (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) :
    Cone ((integralOperationsTensorTowerFunctor l E W).obj (P, Q)) where
  pt := (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)
  π := tensorReductionStrictConeMap l E W P Q

attribute [local implicit_reducible] tensorReductionStrictCone

private theorem scalar_unit_section (W : Scheme.{u}) (n : ℕ)
    (M : integralTowerModules l E W) (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
    coefficientIntegralScalarUnitSection l E W n M U x =
      unrestrictedIntegralTensorSection l E W n M U 1 x := by
  have h := (scalarReductionExtension_adjunction l E W n).choose_spec M U x
  change ((scalarReductionExtension_adjunction l E W n).choose.unit.app M).val.app U x = _
  rw [h]
  rfl

/-- The finite scalar transpose is the corresponding strict cone coordinate.
Source: Stacks 03EK and 07A4. On homogeneous pure tensors both maps insert the
quotient unit in each factor. The quotient augmentation and tensor comparison
have these prescribed formulas; tensor generators and total-summand injections
determine the map in every degree. No flatness or boundedness is needed.
(blueprint: lem-coef-tensor-reduction-strict-cone-coordinates). -/
theorem tensorReductionStrictCone_finiteTranspose (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) :
    let T := (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)
    let D := (integralOperationsTensorTowerFunctor l E W).obj (P, Q)
    @Eq (T ⟶ D.obj (op n))
      (((pullbackTensorFiniteAdjunction l E W n).mapHomologicalComplex (.up ℤ)).homEquiv T
        ((coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
          (integralCoefficientCommRingSheaf l E W n)).obj
          (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P,
            ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q))
        (coefficientScalarTensorIso l E W n P Q).hom)
      ((tensorReductionStrictCone l E W P Q).π.app (op n)) := by
  dsimp only
  apply HomologicalComplex.hom_ext
  intro k
  apply StrictTensorAugmentation.total_hom_ext l E W P Q k
  intro p q hpq U x y
  subst k
  let T := (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)
  let z := coefficientTensorGenerator.{u, u + 1, u} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W) P Q p q (p + q) rfl U x y
  have hs := (coefficientScalarTensorIso_exists l E W n P Q).choose_spec.1
    p q (p + q) rfl U x y
  have hu := (IntegralOnSlice.augmentation_existsUnique l E W none).exists.choose_spec
    T n (p + q) U z
  have ht := (IntegralAmbient.tensorTowerModel l E W).exists.choose_spec P Q n p q U 1 x y
  unfold tensorReductionStrictCone tensorReductionStrictConeMap
  change ((coefficientScalarTensorIso l E W n P Q).hom.f (p + q)).val.app U
      (coefficientIntegralScalarUnitSection l E W n _ U z) =
    ((((IntegralAmbient.tensorTowerIso l E W).hom.app (P, Q)).app (op n)).f
      (p + q)).val.app U
      (((((IntegralOnSlice.augmentation l E W none).app T).app (op n)).f
        (p + q)).val.app U z)
  unfold coefficientScalarTensorIso coefficientUniqueComparisonChoice
  simp only [scalar_unit_section] at hs ⊢
  exact hs.trans ((congrArg
    (((((IntegralAmbient.tensorTowerIso l E W).hom.app (P, Q)).app (op n)).f
      (p + q)).val.app U) hu).trans ht).symm

end WeilConjectures
