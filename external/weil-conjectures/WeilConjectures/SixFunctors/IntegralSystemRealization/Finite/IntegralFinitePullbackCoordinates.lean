/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison

/-! # Canonical finite pullback coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  WeilConjectures.pullbackTensorCalculus
  WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf
  WeilConjectures.completedIntegralCommRingSheafUnrestricted
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
attribute [local implicit_reducible] WeilConjectures.PurCompactSupport.completed
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The finite ringed pullback in the constant-ring coordinates.
Source: Stacks 03D3, 03D6 and 07A6; the derived finiteDirectImage_eq adjoint.
(blueprint: def-sf-integral-finite-pullback-coordinates). -/
def finiteRingPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    PurCompactSupport.pull
        (PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)) f ≅
      finiteDerivedPullback l E n f := by
  let := proEtaleConstantModuleDirectImage_additive f
    (Padic.coefficientExtensionRing l E (n + 1))
  exact ((proEtaleRingDerivedAdjunction f
    ((PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)).ring Y)
    ((PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)).ring X)
    ((PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)).pull f)).ofNatIsoRight
      (Functor.rightDerivedFunctorNatIso
        (eqToIso (PurCompactSupport.finiteDirectImage_eq l E n f)))).leftAdjointUniq
          (finiteAdj l E f n)

/-- Scalar/pullback balancing in the published finite coordinates.
Source: Stacks 03D8, 06YY, 07A6.
(blueprint: def-sf-integral-finite-pullback-coordinates). -/
def finiteScalarPullback {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    ringedPull l E f ⋙ scalarReductionDerivedExtension l E X n ≅
      scalarReductionDerivedExtension l E Y n ⋙ finiteDerivedPullback l E n f :=
  Functor.isoWhiskerLeft _ (PurCompactSupport.finiteReductionIso l E X n).symm ≪≫
    PurCompactSupport.scalarPull
      (PurCompactSupport.reduction l E (n + 1) (Nat.le_add_left 1 n)) f ≪≫
    Functor.isoWhiskerLeft _ (finiteRingPullbackIso l E f n) ≪≫
    Functor.isoWhiskerRight (PurCompactSupport.finiteReductionIso l E Y n) _

end WeilConjectures.IntegralSystemRealization
