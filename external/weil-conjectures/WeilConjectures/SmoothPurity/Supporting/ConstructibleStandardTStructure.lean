/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.AlgebraicallyClosedCoefficients.AlgebraicallyClosedCoefficients
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Standard pairs on constructible coefficient categories

Source: Weil conjectures blueprint, `sec-smooth-base-change/sk-rem-rest`,
`prop-weil-localized-tstructure` and `prop-weil-pbc-integral-tstructure`
(blueprint: def-weil-constructible-standard-tstructure).

Integral classes use the cohomology of completed-coefficient module sheaves.
Rational and algebraically closed classes are the indicated isomorphism closures.
The shifted classes use cohomological shifts. No t-structure axioms are asserted.
-/

@[expose] public section

set_option autoImplicit false

universe d u v

open CategoryTheory CategoryTheory.Limits

namespace WeilConjectures

variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (Y : AlgebraicGeometry.Scheme.{u})

variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

end WeilConjectures
