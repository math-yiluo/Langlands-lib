/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralSystemRealization.IndependentExpression.IndependentExpressionShiftNaturality
import Mathlib.CategoryTheory.Comma.Arrow

set_option linter.privateModule false

/-! # Pointwise reduction and independent expression shifts

Source: blueprint purity transport, Step 2
(blueprint: lem-pur-independent-expression-reduction-shift).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization

attribute [local irreducible] Expression.SlotContext.shift IndependentExpression.shift

end WeilConjectures.IntegralSystemRealization
