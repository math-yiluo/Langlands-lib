/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.SfStrictDirectImageScalar.SfStrictDirectImageScalarData

/-! # Normalized strict integral direct-image models

Source: the strict direct-image scalar-comparison proof, Steps 1, 2 and 6;
Stacks 0D6E and 0A07.
(blueprint: lem-sf-strict-direct-image-integral-models)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.SfStrictDirectImageScalar
variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]

end WeilConjectures.SfStrictDirectImageScalar
