/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficients

/-!
# Completed integral coefficient sheaves

Source: Weil conjectures blueprint, `chap-Smooth-purity`, `sk-def-sf-operations`, order 1455
(blueprint: def-weil-completed-integral-coefficients).

The natural-number index `n` stands for the positive exponent `n + 1`. Coefficients are
lifted into a universe containing the small pro-etale site. The completion is a limit
of ring sheaves, not the discrete constant sheaf of the valuation ring.

## Main definitions

- `integralCoefficientSheafSystem`: the inverse sequence of finite constant ring sheaves.
- `completedIntegralCoefficientSheaf`: its limit in sheaves of rings.
- `completedIntegralCoefficientProjection`: the limit projections.
- `completedIntegralModuleSheaves` and `completedIntegralDerivedCategory`: module categories.
- `completedIntegralCohomology`: cohomology objects of cochain complexes.
- `completedIntegralRestrictScalars`: restriction along each limit projection.
-/

@[expose] public section

universe d t u

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : AlgebraicGeometry.Scheme.{t})

variable (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)






/-- The same completed sheaf with commutativity retained. Forgetting commutativity
recovers the recorded completed ring sheaf definitionally.
Source: Bhatt--Scholze, Section 6.5 (blueprint: def-weil-completed-integral-coefficients). -/
noncomputable def completedIntegralCommRingSheaf (D : FiniteFieldDatum.{d})
    (hl : l ≠ D.p) :
    Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)} :=
  let _ := hl
  completedIntegralCommRingSheafUnrestricted l E Y

/-- The existing limit projection as a morphism of commutative ring sheaves.
Source: Bhatt--Scholze, Section 6.5 (blueprint: def-weil-completed-integral-coefficients). -/
noncomputable def completedIntegralCommRingProjection (n : ℕ) :
    completedIntegralCommRingSheaf l E Y D hl ⟶ integralCoefficientCommRingSheaf l E Y n :=
  completedIntegralCommRingProjectionUnrestricted l E Y n

end WeilConjectures
