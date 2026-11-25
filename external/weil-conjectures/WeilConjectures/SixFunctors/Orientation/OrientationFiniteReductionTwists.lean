/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Orientation.OrientationCoefficientTwists
public import WeilConjectures.AlgebraicGeometry.Finite.Tate.FiniteTateSiteDescent
import all WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower
import WeilConjectures.SmoothPurity.Supporting.SignedTwistFirstReduction
import all WeilConjectures.AlgebraicGeometry.Pur.PurInverseImageScalarComparison

/-! Canonical finite quotient and realization of the completed root lines.
Source: definition-tate-twists
(blueprint: def-sf-orientation-finite-reduction-comparisons). -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOfSpec false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct ChangeOfRings
namespace WeilConjectures

section SingleAdjunction

variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]
  (F : A ⥤ B) (R : B ⥤ A) [F.Additive] [R.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  (a : F ⊣ R) (L : DerivedCategory A ⥤ DerivedCategory B)
  (b : L ⊣ R.mapDerivedCategory)

end SingleAdjunction

section ReductionProof

attribute [local irreducible] HasDerivedCategory.standard
  scalarReductionExistence scalarReductionDerivedExistence scalarReductionExtension
  completedIntegralCoefficientSheafUnrestricted SheafOfModules.monoidalCategory
attribute [local implicit_reducible] completedIntegralCommRingSheafUnrestricted
set_option synthInstance.maxSize 4096

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (X : Scheme.{u}) (m : ℕ)

private def finiteFirstComparison :
    SheafOfModules.changeOfRingsOfUniverses.{u, u+1, u+1, u+1}
      (completedIntegralCommRingProjectionUnrestricted l E X m)
        (purTwistIntegralModule X l E) ≅ purTwistFiniteOne X l E m :=
  (signedTwistFirstReduction l E X m).choose

private def finitePowerComparison (d : ℕ) :
    SheafOfModules.changeOfRingsOfUniverses.{u, u+1, u+1, u+1}
      (completedIntegralCommRingProjectionUnrestricted l E X m)
        (integralTwistLine l E X (d : ℤ)) ≅ finiteCoefficientTwist l E X m (d : ℤ) :=
  SheafOfModules.positiveComparison
    (completedIntegralCommRingProjectionUnrestricted l E X m)
    (purTwistIntegralModule X l E) (purTwistFiniteOne X l E m)
    (finiteFirstComparison l E X m) d

private def finiteOrdinaryComparison (d : ℕ) :
    (scalarReductionExtension l E X m).obj (integralTwistLine l E X (d : ℤ)) ≅
      finiteCoefficientTwist l E X m (d : ℤ) :=
  (Adjunction.leftAdjointUniq
    (scalarReductionExtension_adjunction l E X m).choose
    (PurScalar.tensorAdjunction.{u+1, u+1, u}
      (completedIntegralCommRingProjectionUnrestricted l E X m))).app
      (integralTwistLine l E X (d : ℤ)) ≪≫ finitePowerComparison l E X m d

private def finiteQuotient (d : ℕ) :
    integralTwistLine l E X (d : ℤ) ⟶
      (scalarReductionRestriction l E X m).obj (finiteCoefficientTwist l E X m (d : ℤ)) :=
  ((scalarReductionExtension_adjunction l E X m).choose.homEquiv _ _)
    (finiteOrdinaryComparison l E X m d).hom

variable [∀ x : X, Invertible (l : X.residueField x)]

end ReductionProof

/-- Use the published positive-quotient finiteness witness.
Source: coefficient conventions (blueprint: def-sf-orientation-finite-reduction-comparisons). -/
instance sfOrientationQuotientFinite
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (m : ℕ) :
    Finite (Padic.coefficientExtensionRing l E (m + 1)) :=
  Padic.finite_coefficientExtensionRing l E (m + 1) (Nat.succ_le_succ (Nat.zero_le m))

end WeilConjectures
