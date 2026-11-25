/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.FiniteExceptionalInverseImage
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting

/-!
# Purity specialization of the published intrinsic exceptional inverse image

Source: Weil blueprint, sec-smooth-purity/sk-def-sf-operations, order 1489
(blueprint: theorem-f-shriek-finite-coefficients).

`Scheme.finiteExceptionalInverseImage` already constructs the canonical composite
nu_X^* f^times Rnu_Y,* in intrinsic constant-ring modules. This module only provides
transparent aliases and the finite-quotient instances needed by the purity setting.
It introduces no second comparison, realization, inverse, or exceptional construction.

## Main definitions

- `Scheme.sfIntrinsicExceptionalInverseImage`: alias of the published finite-level functor.
- `PurityFiniteSetting.exceptionalInverseImage`: its purity-setting specialization.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme

namespace WeilConjectures.PurityFiniteSetting

/-- Finiteness of the positive finite coefficient quotient, using the recorded theorem.
Source: blueprint sk-def-sf-operations (vi), finite coefficients
(blueprint: theorem-f-shriek-finite-coefficients). -/
noncomputable instance ringFinite (P : PurityFiniteSetting.{u}) : Finite P.Ring :=
  Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos

/-- Finiteness is preserved by the standard coefficient-size lift.
Source: blueprint sk-def-sf-operations (vi), coefficient universe convention
(blueprint: theorem-f-shriek-finite-coefficients). -/
noncomputable instance coefficientFinite (P : PurityFiniteSetting.{u}) : Finite P.Coefficient :=
  inferInstanceAs (Finite (ULift.{u + 1} P.Ring))

end WeilConjectures.PurityFiniteSetting
