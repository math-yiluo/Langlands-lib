/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerCore
public import WeilConjectures.PoincareDuality.StrictTensorAugmentation.StrictTensorAugmentationConstruction
import WeilConjectures.PoincareDuality.StrictTensorAugmentation.StrictTensorAugmentation

/-! # Finite tensor transpose coordinates

The finite adjunction unit identifies the normalized tensor comparison with the
product coordinate of the strict Roos augmentation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option cleanup.letToHave false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  completedIntegralCommRingSheafUnrestricted completedIntegralCoefficientSheafUnrestricted
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory
attribute [local implicit_reducible] integralOperationsRoos integralOperationsTensorTowerFunctor
  integralOperationsTensorLevel integralOperationsTensorComposite integralOperationsFiniteMonoidal
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem scalar_unit_section (W : Scheme.{u}) (n : ℕ)
    (M : integralTowerModules l E W) (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
    coefficientIntegralScalarUnitSection l E W n M U x =
      unrestrictedIntegralTensorSection l E W n M U 1 x := by
  have h := (scalarReductionExtension_adjunction l E W n).choose_spec M U x
  change ((scalarReductionExtension_adjunction l E W n).choose.unit.app M).val.app U x = _
  rw [h]
  rfl

/-- The finite scalar-adjunction transpose of the normalized tensor comparison is
exactly the corresponding product coordinate of the strict tensor augmentation.

Source: Stacks 03EK, 07A4 and 0941; scalar-extension tensor units and the strict
quotient augmentation. Proof: in each total degree, maps out of the total tensor
are determined by its homogeneous pure tensors. The finite adjunction transpose
first applies the scalar unit. Its underlying section is `1 tensor z`. The defining
generator formula of `coefficientScalarTensorIso` sends the unit of `x tensor y`
to the tensor of the units of `x` and `y`. These are exactly the specified product
coordinates of `StrictTensorAugmentation.map`. Apply tensor-generator extensionality
and then complex hom extensionality. This argument also covers zero complexes and
the first finite coefficient level, since it uses the same universal formulas.
(blueprint: lem-coef-tensor-reduction-finite-transpose-coordinates). -/
theorem tensorReduction_finiteTransposeCoordinates (W : Scheme.{u})
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
      ((StrictTensorAugmentation.map l E W).app (P, Q) ≫
        CochainComplex.mappingCocone.fst
          (towerTransitionEndomorphism (K := fun j ↦ D.obj (op j))
            (integralOperationsTowerStep D)) ≫ Pi.π (fun j ↦ D.obj (op j)) n) := by
  dsimp only
  apply HomologicalComplex.hom_ext
  intro k
  apply StrictTensorAugmentation.total_hom_ext l E W P Q k
  intro p q hpq U x y
  subst k
  have hs := (coefficientScalarTensorIso_exists l E W n P Q).choose_spec.1
    p q (p + q) rfl U x y
  change ((coefficientScalarTensorIso l E W n P Q).hom.f (p + q)).val.app U
      (coefficientIntegralScalarUnitSection l E W n _ U
        (coefficientTensorGenerator.{u, u + 1, u} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W)
          P Q p q (p + q) rfl U x y)) = _
  simp only [HomologicalComplex.comp_f]
  unfold coefficientScalarTensorIso coefficientUniqueComparisonChoice
  exact hs.trans (by
    simp only [scalar_unit_section]
    exact ((StrictTensorAugmentation.coordinates l E W).1 P Q p q n U x y).symm)

end WeilConjectures
