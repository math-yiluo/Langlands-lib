/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Regular.RegularQuotientCoinduction
public import WeilConjectures.Algebra.Homology.RegularQuotientCone.Augmentation.RegularQuotientConeBoundary
public import Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.DeligneLaumon.PrincipalKoszulStrictReplacement.PrincipalKoszulStrictReplacement
public import Mathlib.CategoryTheory.Localization.Predicate

/-! # The normalized trace for the actual completed coefficient projection

Source: Stacks Tags 06YP, 06YY, 07A6 and 093M; the actual principal Koszul short exact sequence
and the universal derived adjunction.
(blueprint: def-sf-regular-quotient-trace-data). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open SheafOfModules SheafOfModules.RegularQuotientCone
namespace WeilConjectures

attribute [-instance] PrincipalKoszulStrictReplacement.siteSmall
  PrincipalKoszulStrictReplacement.abSheafify PrincipalKoszulStrictReplacement.abLocallyBijective
  integralCoefficientAbSheafify integralCoefficientAbLocallyBijective
  scalarReductionSourceDerived scalarReductionTargetDerived
  GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local instance] HasDerivedCategory.standard
attribute [local irreducible] HasDerivedCategory.standard

private local instance (T : Scheme.{u}) : EssentiallySmall.{u+1} T.ProEt :=
  essentiallySmallSelf.{0,u,u+1} _
private local instance (T : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{u+1} :=
  integralCoefficientAbSheafify.{u,u} T
private local instance (T : Scheme.{u}) :
    (Scheme.ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u+1} :=
  integralCoefficientAbLocallyBijective.{u,u} T
attribute [local instance] scalarReductionRestrictionLimits scalarReductionRestrictionColimits

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n : ℕ)

/-- The derived-category structure recorded by the cone augmentation on the finite
reduction target (auxiliary; not a blueprint node). -/
abbrev regularQuotientTraceTargetDerived :
    HasDerivedCategory (scalarReductionTarget.{u, u} l E T n) :=
  Scheme.reductionModulesHasDerivedCategory T (integralCoefficientCommRingSheaf l E T n)

attribute [local instance high] regularQuotientTraceTargetDerived

/-- The positive uniformizer power, as a section of the actual completed unit module.
Source: Stacks Tags 06YP, 06YY, 07A6 and 093M; the actual principal Koszul short exact sequence
and the universal derived adjunction.
(blueprint: def-sf-regular-quotient-trace-data). -/
def reductionScalarSection :
    (unit (completedIntegralCoefficientSheafUnrestricted l E T)).sections :=
  (unit (completedIntegralCoefficientSheafUnrestricted l E T)).unitHomEquiv
    (PrincipalKoszulStrictReplacement.multiplication l E T n)

private theorem reductionScalar_unit :
    (scalar (completedIntegralCommRingSheafUnrestricted l E T)
      (reductionScalarSection l E T n)).app
        (unit (completedIntegralCoefficientSheafUnrestricted l E T)) =
      PrincipalKoszulStrictReplacement.multiplication l E T n := by
  apply (unit (completedIntegralCoefficientSheafUnrestricted l E T)).unitHomEquiv.injective
  ext U
  let a : (completedIntegralCommRingSheafUnrestricted l E T).obj.obj U :=
    (reductionScalarSection l E T n).val U
  change a * 1 = a
  exact mul_one _

private theorem reductionScalar_ringMap :
    ringMap (completedIntegralCommRingProjectionUnrestricted l E T n) =
      PrincipalKoszulStrictReplacement.projection l E T n := by
  rfl

/-- The actual positive uniformizer scalar followed by the quotient map is zero.
Source: Stacks Tags 06YP, 06YY, 07A6 and 093M; the actual principal Koszul short exact sequence
and the universal derived adjunction.
(blueprint: def-sf-regular-quotient-trace-data). -/
theorem reductionScalar_zero :
    (scalar (completedIntegralCommRingSheafUnrestricted l E T)
      (reductionScalarSection l E T n)).app
        (unit (completedIntegralCoefficientSheafUnrestricted l E T)) ≫
      ringMap (completedIntegralCommRingProjectionUnrestricted l E T n) = 0 := by
  rw [reductionScalar_unit, reductionScalar_ringMap]
  exact PrincipalKoszulStrictReplacement.multiplication_projection l E T n

/-- The normalized regular sequence, in the cone augmentation's coefficient convention.
Source: Stacks Tags 06YP, 06YY, 07A6 and 093M; the actual principal Koszul short exact sequence
and the universal derived adjunction.
(blueprint: def-sf-regular-quotient-trace-data). -/
theorem reductionScalar_shortExact :
    (ShortComplex.mk
      ((scalar (completedIntegralCommRingSheafUnrestricted l E T)
        (reductionScalarSection l E T n)).app
          (unit (completedIntegralCoefficientSheafUnrestricted l E T)))
      (ringMap (completedIntegralCommRingProjectionUnrestricted l E T n))
      (reductionScalar_zero l E T n)).ShortExact := by
  simpa only [reductionScalar_unit, reductionScalar_ringMap] using
    (PrincipalKoszulStrictReplacement.completed_exact l E T n).1

/-- A universal cochain realization of finite reduction, with its canonical counit.
Source: Stacks Tags 06YP, 06YY, 07A6 and 093M; the actual principal Koszul short exact sequence
and the universal derived adjunction.
(blueprint: def-sf-regular-quotient-trace-data). -/
def reductionCochainModel :
    DerivedChangeOfRingsCochainModel.{u+1, u, u+1, u+2, u+2}
      (completedIntegralCommRingProjectionUnrestricted l E T n) :=
  (nonempty_derivedChangeOfRingsCochainModel.{u+1,u,u+1,u+2,u+2}
    (completedIntegralCommRingProjectionUnrestricted l E T n)).some

/-- The normalized principal-cone augmentation for the actual finite reduction.
Source: Stacks Tags 06YP, 06YY, 07A6 and 093M; the actual principal Koszul short exact sequence
and the universal derived adjunction.
(blueprint: def-sf-regular-quotient-trace-data). -/
def reductionAugmentation :
    Augmentation.{u+1,u,u+1,u+2,u+2} (completedIntegralCommRingProjectionUnrestricted l E T n)
      (reductionScalarSection l E T n) (reductionCochainModel l E T n) :=
  (nonempty_augmentation _ _ (reductionScalar_zero l E T n)
    (reductionScalar_shortExact l E T n) (reductionCochainModel l E T n)).some

/-- Its restriction realization is canonically exact derived restriction.
Source: Stacks Tags 06YP, 06YY, 07A6 and 093M; the actual principal Koszul short exact sequence
and the universal derived adjunction.
(blueprint: def-sf-regular-quotient-trace-data). -/
def reductionAugmentationRestrictionIso :
    (reductionAugmentation l E T n).V ≅ scalarReductionDerivedRestriction.{u,u} l E T n :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (scalarReductionTarget.{u,u} l E T n) (.up ℤ))
    (DerivedCategory.Q ⋙ (reductionAugmentation l E T n).V)
    (DerivedCategory.Q ⋙ scalarReductionDerivedRestriction.{u,u} l E T n)
    (reductionAugmentation l E T n).V (scalarReductionDerivedRestriction.{u,u} l E T n)
    ((reductionAugmentation l E T n).restriction_factor ≪≫
      (scalarReductionRestriction.{u,u} l E T n).mapDerivedCategoryFactors.symm)

/-- Coinduction adjunction, expressed using the augmentation's canonical restriction.
Source: Stacks Tags 06YP, 06YY, 07A6 and 093M; the actual principal Koszul short exact sequence
and the universal derived adjunction.
(blueprint: def-sf-regular-quotient-trace-data). -/
def reductionAugmentationCoinductionAdjunction :
    (reductionAugmentation l E T n).V ⊣ scalarReductionDerivedCoinduction l E T n :=
  (scalarReductionDerivedCoinductionAdjunction l E T n).ofNatIsoLeft
    (reductionAugmentationRestrictionIso l E T n).symm

/-- The quotient-linear trace is the adjoint transpose of the shifted cone boundary.
Source: Stacks Tags 06YP, 06YY, 07A6 and 093M; the actual principal Koszul short exact sequence
and the universal derived adjunction.
(blueprint: def-sf-regular-quotient-trace-data). -/
def reductionCoinductionTrace :
    shiftFunctor (DerivedCategory (scalarReductionSource.{u,u} l E T)) (-1 : ℤ) ⋙
        (reductionCochainModel l E T n).T ⟶
      scalarReductionDerivedCoinduction l E T n :=
  (reductionAugmentation l E T n).coinductionTrace
    (reductionAugmentationCoinductionAdjunction l E T n)

/-- The universal extension model agrees with the project's fixed derived reduction.
Source: Stacks Tags 06YP, 06YY, 07A6 and 093M; the actual principal Koszul short exact sequence
and the universal derived adjunction.
(blueprint: def-sf-regular-quotient-trace-data). -/
def reductionCochainModelIso :
    (reductionCochainModel l E T n).T ≅ scalarReductionDerivedExtension.{u,u} l E T n :=
  Adjunction.leftAdjointUniq
    ((reductionAugmentation l E T n).adjunction.ofNatIsoRight
      (reductionAugmentationRestrictionIso l E T n))
    (derivedScalarExtensionRestrictionAdjunction.{u,u} l E T n).choose

end WeilConjectures
