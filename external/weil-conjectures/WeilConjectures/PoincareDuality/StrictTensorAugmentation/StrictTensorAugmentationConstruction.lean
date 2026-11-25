/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels
public import WeilConjectures.SmoothPurity.Integral.IntegralConstructibleTriangulated
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices

/-! # The strict tensor quotient augmentation

The constructed map retains both coordinates of the strict Roos complex.
Source: Stacks 03EL, 07A4 and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralReductionSiteEssentiallySmall
attribute [local instance 3000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.StrictTensorAugmentation
attribute [local irreducible] completedIntegralCommRingSheafUnrestricted
  completedIntegralCoefficientSheafUnrestricted unrestrictedIntegralReductionExistence
  coefficientTotalTensor
attribute [local implicit_reducible] IntegralOnSlice.ring IntegralOnSlice.restrict
  IntegralOnSlice.topology IntegralOnSlice.Site IntegralOnSlice.roos IntegralAmbient.tensorTower

/-- Naturality of the fixed quotient completion unit.
Source: Stacks 08TC (blueprint: lem-pur-strict-tensor-augmentation-construction).
Proof: the product augmentation is natural and the second coordinate vanishes. -/
theorem unit_naturality (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) {P Q : IntegralOnSlice.Cx.{u, u} l E T none} (f : P ⟶ Q) :
    f ≫ IntegralOnSlice.roosUnit.{u, u} l E T none Q =
      IntegralOnSlice.roosUnit.{u, u} l E T none P ≫
        (IntegralOnSlice.roos.{u, u} l E T none).map f :=
  IntegralOnSlice.sliceRoosUnit_natural.{u, u} l E T none f

/-- The natural quotient completion unit.
Source: Stacks 08TC (blueprint: lem-pur-strict-tensor-augmentation-construction). -/
def unit (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) :
    𝟭 (IntegralOnSlice.Cx.{u, u} l E T none) ⟶ IntegralOnSlice.roos.{u, u} l E T none where
  app := IntegralOnSlice.roosUnit.{u, u} l E T none
  naturality _ _ f := unit_naturality l E T f

/-- The strict ordinary-to-completed tensor map built from the normalized quotient tower.
Source: Stacks 03EL, 07A4 and 0941
(blueprint: lem-pur-strict-tensor-augmentation-construction). -/
def map (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) :
    (@coefficientTotalTensor.{u, u + 1, u} T.ProEt _ (ProEt.topology T)
      (integralOperationsAbSheafify.{u, u} T)
      (integralOperationsAbLocallyBijective.{u, u} T)
      (completedIntegralCommRingSheafUnrestricted.{u, u} l E T)) ⟶
        integralOperationsTensorComplexFunctor.{u, u} l E T :=
  Functor.whiskerLeft
    (@coefficientTotalTensor.{u, u + 1, u} T.ProEt _ (ProEt.topology T)
      (integralOperationsAbSheafify.{u, u} T)
      (integralOperationsAbLocallyBijective.{u, u} T)
      (completedIntegralCommRingSheafUnrestricted.{u, u} l E T)) (unit l E T) ≫
    Functor.whiskerRight (IntegralAmbient.tensorTowerIso.{u, u} l E T).hom
      (integralOperationsRoosFunctor (A := integralTowerModules.{u, u} l E T))

attribute [local irreducible] IntegralOnSlice.roosUnit IntegralAmbient.tensorTowerIso

/-- The constructed transformation has the recorded strict augmentation as each component.
Source: Stacks 03EL and 08TC
(blueprint: lem-pur-strict-tensor-augmentation-construction). -/
theorem map_app (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) (P Q : CochainComplex (integralTowerModules.{u, u} l E T) ℤ) :
    (map l E T).app (P, Q) = IntegralAmbient.tensorOperationUnit.{u, u} l E T P Q := by
  unfold map unit IntegralAmbient.tensorOperationUnit
  rfl

end WeilConjectures.StrictTensorAugmentation
