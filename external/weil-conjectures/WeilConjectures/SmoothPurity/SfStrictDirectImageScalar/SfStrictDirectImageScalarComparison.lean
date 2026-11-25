/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfIntegralDirectImageConstructible
public import WeilConjectures.SmoothPurity.CompletedCoefficientPushforward.CompletedCoefficientPushforwardComparison
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarExtension
public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
public import WeilConjectures.DeligneLaumon.SfScalarExtensionComposition
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDirectImageComposition
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleLinear
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionUniverses
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.SmoothPurity.SfStrictDirectImageScalar.SfStrictDirectImageScalarData
import WeilConjectures.SmoothPurity.SfStrictDirectImageScalar.SfStrictDirectImageIntegralModels
import WeilConjectures.SmoothPurity.SfStrictDirectImageScalar.SfStrictDirectImageScalarData
import WeilConjectures.SmoothPurity.SfStrictDirectImageScalar.SfStrictDirectImageRationalComparisons

/-! # Scalar compatibility of the strict-tower direct image

Source: blueprint strict direct-image scalar comparison, Steps 1--8.
(blueprint: lem-sf-strict-direct-image-scalar-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived

universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.SfStrictDirectImageScalar
attribute [local irreducible] HasDerivedCategory.standard
  completedOrdinaryScalarExtension completedOrdinaryScalarComplex
  completedScalarChangeData completedScalarComparison completedDerivedScalarExtension
  integralUnit sfIntegralScalarUnit sfRationalScalarComp sfRationalScalarUnit
  GeneralAlgebraicallyClosedCoefficients.associator
  GeneralAlgebraicallyClosedCoefficients.unitor

variable (l : ℕ) [Fact l.Prime]
variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
attribute [instance 20000] WeilConjectures.CompletedCoefficientPushforward.modAbelian
attribute [instance 10000] WeilConjectures.CompletedCoefficientPushforward.hasDerived

end WeilConjectures.SfStrictDirectImageScalar
