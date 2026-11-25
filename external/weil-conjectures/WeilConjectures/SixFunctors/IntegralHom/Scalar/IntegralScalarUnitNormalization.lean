/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.PrincipalKoszulStrictReplacement.PrincipalKoszulStrictReplacement
public import WeilConjectures.SixFunctors.Integral.IntegralReductionTowerWellDefinedUnrestricted
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels

/-! # Identifying the two canonical scalar-extension augmentation maps -/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.IntegralHom
attribute [local instance 20000] abSheafify abLocallyBijective
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  HasDerivedCategory.standard scalarReductionExistence scalarReductionDerivedExistence
  unrestrictedIntegralReductionExistence
attribute [local implicit_reducible] completedIntegralCommRingSheafUnrestricted
  CategoryTheory.sheafCompose IntegralOnSlice.Site IntegralOnSlice.siteCategory
  IntegralOnSlice.topology IntegralOnSlice.restrict IntegralOnSlice.ring IntegralOnSlice.finite
  IntegralOnSlice.projection SheafOfModules.restrictScalars
  completedIntegralCommRingProjectionUnrestricted integralCoefficientSheaf
  integralCoefficientCommRingSheaf

/-- The slice augmentation at the empty slice datum is the recorded scalar unit.

Source: the quotient unit in paragraph 1 of the current blueprint
`lem-coef-integral-hom-reduction.proof.md`; Stacks Tag 03EK
(blueprint: lem-sf-integral-scalar-unit-normalization).

Proof: compare chain maps degreewise and compare their sheaf morphisms on every
local section. The defining unique-existence property of the slice augmentation
sends x to the specified sheafified pure tensor x tensor 1. The constructed
unrestricted tower unit has exactly the same formula by its proved condition.
Equality on all sections proves equality of the chain maps. No K-flatness or
boundedness is needed; zero inputs and empty sites satisfy the same formula. -/
theorem integralScalarAugmentation_eq_unrestrictedUnit
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : AlgebraicGeometry.Scheme.{t})
    (P : CochainComplex (PrincipalKoszulStrictReplacement.Modules l E Y) ℤ) (n : ℕ) :
    ((IntegralOnSlice.augmentation l E Y none).app P).app (op n) =
      unrestrictedTowerUnit l E Y P n := by
  ext i U x
  exact (IntegralOnSlice.augmentation_existsUnique l E Y none).exists.choose_spec P n i U x
    |>.trans ((unrestrictedTowerUnit_condition l E Y P n i U x).symm)

end WeilConjectures.IntegralHom
