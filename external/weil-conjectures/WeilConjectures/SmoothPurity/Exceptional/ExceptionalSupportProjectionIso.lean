/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantSupportProjection
public import WeilConjectures.AlgebraicGeometry.Ambient.AmbientExceptionalRightAdjoint

import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport

/-!
# Scalar restricted constant support projection

Source: Stacks Tag 0GL6 and the coefficientwise support comparison.
(blueprint: lem-exc-support-constant-projection-after-restriction)
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures

section InstanceTransport
open Lean Meta Elab Tactic

end InstanceTransport

end WeilConjectures
