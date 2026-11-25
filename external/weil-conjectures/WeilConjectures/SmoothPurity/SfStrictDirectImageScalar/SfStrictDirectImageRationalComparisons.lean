/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.SfStrictDirectImageScalar.SfStrictDirectImageScalarData
public import WeilConjectures.CategoryTheory.ScalarLocalization.PbcRationalTransport

/-! # Assembly of the explicit raw rational direct image

Source: strict direct-image scalar comparison, Step 8.
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme TensorProduct
namespace WeilConjectures.SfStrictDirectImageScalar
attribute [local irreducible] sfIntegralConstructible HasDerivedCategory.standard
  completedOrdinaryScalarExtension completedOrdinaryScalarComplex
  completedScalarChangeData completedScalarComparison completedDerivedScalarExtension
  integralUnit sfIntegralScalarUnit sfRationalScalarComp sfRationalScalarUnit
  GeneralAlgebraicallyClosedCoefficients.associator
  GeneralAlgebraicallyClosedCoefficients.unitor

variable (l : ℕ) [Fact l.Prime]
variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open GeneralAlgebraicallyClosedCoefficients (Stage transition associator unitor)

attribute [instance 20000] WeilConjectures.CompletedCoefficientPushforward.modAbelian
attribute [instance 10000] WeilConjectures.CompletedCoefficientPushforward.hasDerived

end WeilConjectures.SfStrictDirectImageScalar
