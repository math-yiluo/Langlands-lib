/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.FrobeniusCoefficientTwists.FrobeniusCoefficientTwistsCanonical
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SchemeGeometricFrobenius
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
public import WeilConjectures.SixFunctors.Orientation.OrientationIntegralCoefficientTwists
public import WeilConjectures.SmoothPurity.Integral.Twist.IntegralTwistBaseChange
public import WeilConjectures.SmoothPurity.Supporting.SignedTwistReductionComparison
public import WeilConjectures.SixFunctors.Supporting.PositiveRootTensorProduct
public import WeilConjectures.Algebra.Homology.FlatSingleDerivedNormalization.FlatSingleDerivedNormalization
public import WeilConjectures.SixFunctors.Integral.IntegralPullbackAugmentationAmbient
public import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
public import WeilConjectures.SixFunctors.Supporting.RoosIntrinsicCompletenessEquivalence
public import WeilConjectures.DeligneLaumon.PrincipalKoszulStrictReplacement.PrincipalKoszulStrictReplacement
public import Mathlib.Data.Nat.Prime.Infinite
import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
import WeilConjectures.DeligneLaumon.PrincipalKoszulStrictReplacement.PrincipalKoszulStrictReplacement
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange

/-! # Canonical Tate comparisons: ScalarComparisons

Source: current blueprint, definition-weil-structure--1, canonical root-line comparisons.
This module preserves the original unshifted comparison declarations.
(blueprint: def-pur-canonical-tate-scalar-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u v a b c d
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct ChangeOfRings
namespace WeilConjectures.CanonicalTate
open FrobeniusCoefficientTwists

attribute [local instance 5000] integralTowerHasDerivedCategory scalarReductionTargetDerived

attribute [-instance] PrincipalKoszulStrictReplacement.abSheafify
  PrincipalKoszulStrictReplacement.abLocallyBijective
  PrincipalKoszulStrictReplacement.siteSmall
attribute [local irreducible] IntegralOnSlice.completion
  IntegralOnSlice.completionComparison IntegralOnSlice.completionUnit
  IntegralOnSlice.duality IntegralOnSlice.roosUnit IntegralAmbient.tensorTowerIso
  HasDerivedCategory.standard completedIntegralCoefficientSheafUnrestricted
  coefficientTotalTensor SheafOfModules.monoidalCategory IntegralOnSlice.tower
  IntegralOnSlice.augmentation integralOperationsTensorTowerFunctor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
/-- The completed scalar comparison on a line, fixed by ordinary scalar extension.
Source: blueprint definition-weil-structure--1, canonical roots and tensor powers
(blueprint: def-pur-canonical-tate-scalar-comparisons).
Proof: The scalar-completion map is invertible on the complete line. Its
inverse identifies completed extension with the published ordinary derived
scalar functor. The single-functor comparison and twistLineScalarIso finish
the computation; their unit tensor formulas fix every map and its inverse uniquely. -/
theorem integralScalarLine_existsUnique
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] (r : ℕ) :
    ∃! e : (integralScalarExtension l E L ι X).obj
        (sfIntegralTwistingObject l E X (r : ℤ)) ≅
      sfIntegralTwistingObject l L X (r : ℤ),
      (scalarCompletion l E L ι X).app (sfIntegralTwistingObject l E X (r : ℤ)) ≫
        e.hom =
      ((integralOrdinaryScalar l E L ι X).mapDerivedCategorySingleFunctor 0).hom.app
        (integralTwistLine l E X (r : ℤ)) ≫
      (DerivedCategory.singleFunctor _ 0).map (twistLineScalarIso l E X L ι (r : ℤ)).hom := by
  let e := (scalarCompletionIso l E L ι X
      (sfIntegralTwistingObject l E X (r : ℤ))
      (sfIntegralTwistingObject_mem l E X (r : ℤ)).1).symm ≪≫
    ((integralOrdinaryScalar l E L ι X).mapDerivedCategorySingleFunctor 0).app
      (integralTwistLine l E X (r : ℤ)) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (twistLineScalarIso l E X L ι (r : ℤ))
  refine ⟨e, ?_, ?_⟩
  · simp [e, scalarCompletionIso]
  · intro e' he'
    apply Iso.ext
    have : IsIso ((scalarCompletion l E L ι X).app
        (sfIntegralTwistingObject l E X (r : ℤ))) :=
      (scalarCompletion_existsUnique l E L ι X).exists.choose_spec.2 _
        (sfIntegralTwistingObject_mem l E X (r : ℤ)).1
    apply (cancel_epi ((scalarCompletion l E L ι X).app
      (sfIntegralTwistingObject l E X (r : ℤ)))).1
    simpa [e, scalarCompletionIso] using he'

/-- The specified completed scalar extension of a Tate line.
Source: blueprint definition-weil-structure--1, canonical roots and tensor powers
(blueprint: def-pur-canonical-tate-scalar-comparisons). -/
def integralScalarLine
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] (r : ℕ) :
    (sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
      E L ι X).obj (sfIntegralTwistingCoefficient l E X (r : ℤ)) ≅
      sfIntegralTwistingCoefficient l L X (r : ℤ) :=
  ObjectProperty.isoMk _ (integralScalarLine_existsUnique l E L ι X r).exists.choose

/-- The rational coefficient-line comparison is the localized completed scalar map.
Source: blueprint definition-weil-structure--1, canonical roots and tensor powers
(blueprint: def-pur-canonical-tate-scalar-comparisons). -/
def rationalScalarLine
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] (r : ℕ) :
    (sfRationalScalarExtension l E X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj
        (sfRationalTwistingCoefficient l E X (r : ℤ)) ≅
      sfRationalTwistingCoefficient l L X (r : ℤ) :=
  eqToIso ((sfRationalScalarExtension_existsUnique l E X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).exists.choose_spec.2.1
        (sfRationalTwistingCoefficient l E X (r : ℤ))) ≪≫
    (sfRationalConstructibleLocalization l L X).mapIso (integralScalarLine l E L ι X r)

end WeilConjectures.CanonicalTate
