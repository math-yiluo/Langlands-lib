/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurStrictScalar.NativeConstantSupportModel
import all WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientResolutionNormalization

/-! # K-injective preservation for constant scalar restriction

Restriction from completed to constant coefficients is right adjoint to exact
scalar extension along the flat constant-to-completed coefficient map.
(blueprint: lem-pur-compact-support-scalar-limit-restriction-kinjective).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.IntegralQuotient
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

end WeilConjectures.PurStrictScalar
