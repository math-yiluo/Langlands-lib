/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralRestrictionFunctors
public import WeilConjectures.AlgebraicGeometry.RationalP1.Tate.RationalTatePullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Trace.TraceBaseChangeSecond
/-! # Cartesian integral Tate line comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
attribute [local instance 20000] CategoryTheory.Mod.derivedMonoidalCategory
namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction
open DiagonalCoefficients
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
/-- The section-module positive twist is the internal integral root line.
Source: paragraph (1), positive integral Tate convention.
(blueprint: def-integral-kernel-tate-comparisons). -/
def positiveTateLineIso (X : Scheme.{u}) :
    tateLine ℓ E X 1 ≅ spIntegralTwist X ℓ E :=
  (InternalAbelianSheafModule.sectionModuleEquivalence
    (Scheme.ProEt.topology X)
    (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X)).unitIso.symm.app _
/-- The Cartesian integral root line, through the exact module equivalence.
Source: paragraph (1), Cartesian Tate coefficients.
(blueprint: def-integral-kernel-tate-comparisons). -/
def integralLinePullIso {X S : Scheme.{u}} (f : X ⟶ S)
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    [∀ x : S, Invertible (ℓ : S.residueField x)] :
    (upperStar (Profinite.padicIntegersRingObj ℓ E.val) f).obj (spIntegralTwist S ℓ E) ≅
      spIntegralTwist X ℓ E :=
  RationalP1.linePullIso _ f _ _ (spIntegralComparison f ℓ E)
    ((RationalP1.adicComparison ℓ f).integral_rational_cartesian E).1
/-- Pullback of the positive integral Tate line in degree minus two.
Source: paragraph (1), shifted Cartesian Tate comparison.
(blueprint: def-integral-kernel-tate-comparisons). -/
def integralShiftedLinePullIso {X S : Scheme.{u}} (f : X ⟶ S)
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    [∀ x : S, Invertible (ℓ : S.residueField x)] :
    (moduleObjectDerivedPullback (Profinite.padicIntegersRingObj ℓ E.val) f).obj
      (traceTate ℓ E S) ≅ traceTate ℓ E X := by
  unfold traceTate
  let F := moduleObjectDerivedPullback (Profinite.padicIntegersRingObj ℓ E.val) f
  exact (F.commShiftIso (2 : ℤ)).app _ ≪≫
    (shiftFunctor _ (2 : ℤ)).mapIso
      ((upperStar (Profinite.padicIntegersRingObj ℓ E.val)
          f).singleFunctorCompLeftDerivedFunctorIso.app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso (integralLinePullIso ℓ E f))
end AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction
