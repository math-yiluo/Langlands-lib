/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFrameKummer
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedCup
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion
import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionBaseChange

/-!
# The concrete class of an étale frame

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-a1-kummer,
proposition-purity-vector-bundles (blueprint: proposition-purity-vector-bundles). The existing
EtaleFrame records the scheme-theoretic generating condition. The coefficient extension
realizes each individual support boundary by Yoneda composition. The ordered
product uses the published supported cup, associating to the left.
-/

@[expose] public noncomputable section

set_option Elab.async false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale

namespace WeilConjectures.PurityFiniteSetting

/-- Each new factor contributes degree two.
Source: proposition-purity-vector-bundles, degree addition (blueprint:
proposition-purity-vector-bundles). Proof: distribute multiplication by two over d+1 in the
integers. -/
theorem frameDegreeNext (d : ℕ) : 2 * (d : ℤ) + 2 = 2 * ((d + 1 : ℕ) : ℤ) := by
  simp only [Nat.cast_add, Nat.cast_one, mul_add, mul_one]

end WeilConjectures.PurityFiniteSetting
