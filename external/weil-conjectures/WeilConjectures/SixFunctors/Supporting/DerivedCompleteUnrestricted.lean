/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedComplete
public import WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined

/-!
# Unrestricted derived completeness

Source: Bhatt--Scholze, Definition 3.5.2 (blueprint: def-weil-derived-complete).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t})

/-- Derived completeness of the existing completed coefficient sheaf, with no
finite-field condition. The finite-field datum is an auxiliary presentation only:
all the completed rings, reductions and augmentation maps in IsDerivedComplete
ignore it. Such a datum with characteristic different from l always exists (use
F_2 if l differs from 2 and F_3 otherwise), so this existential changes no condition
on K. Source: Bhatt--Scholze, Definition 3.5.2, p. 24
(blueprint: def-weil-derived-complete). -/
noncomputable def IsDerivedCompleteUnrestricted
    (K : DerivedCategory (integralTowerModules.{t, u} l E Y)) : Prop :=
  ∃ (D : FiniteFieldDatum.{0}) (hl : l ≠ D.p), IsDerivedComplete l E Y D hl K

end WeilConjectures
