/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction
public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels

set_option linter.privateModule false

/-!
# Projection formula and finite coefficient reduction

Source: current blueprint latest, chap-The-six-operations-on-Dbctf,
sk-prop-sf-pf-coherence/prop-sf-pf-reduction (blueprint: prop-sf-pf-reduction).
The proposition uses ordinary unbounded etale categories and reduction retained
as an endofunctor of the original coefficient category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option relaxedAutoImplicit false
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

open AlgebraicGeometry.Etale CategoryTheory.Limits MonoidalCategory

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

end WeilConjectures
