/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.SmoothPurity.Rational.RationalScalarDerivedRestriction
import WeilConjectures.SmoothPurity.Rational.RationalScalarRestrictionComplete
import WeilConjectures.SmoothPurity.Rational.RationalScalarRestrictionReductionConstructible

/-!
# Constructibility under completed coefficient restriction

Source: Bhatt--Scholze, Proposition 6.8.14(2), Remark 6.8.15; the finite
coefficient restriction step (blueprint: lem-sf-rational-scalar-restriction-constructible).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime]
  (E F : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (ι : E →ₐ[ℚ_[l]] F) (W : AlgebraicGeometry.Scheme.{u})

/-- Exact completed coefficient restriction preserves the intrinsic integral
constructible predicate.

Source: Bhatt--Scholze, Proposition 6.8.14(2), Remark 6.8.15; step 1 of
`lem-sf-rational-scalar-extension-right-adjoint` (agent elaboration).
(blueprint: lem-sf-rational-scalar-restriction-constructible).

Proof: first identify the normalized completed coefficient presentations by
`purCoefficientIso`. The square formed by these isomorphisms and the two
completed scalar maps commutes: its finite quotient projections are the same
maps induced by the integral coefficient inclusion, and projections detect
maps into the completion. Exact restriction along this square identifies the
derived restriction functors. Apply `pbcScalarRestrictionComplete`, then transport
its conclusion by `purCoefficientModel_predicates`. This supplies completeness
for the actual restriction used here, rather than a different coefficient model.

For the reductions, the O_E-uniformizer maps to a unit times a positive power e
of the O_F-uniformizer. Hence O_F modulo the n-th power of the image is O_F
modulo the (e*n)-th power of its uniformizer. The completed O_F coefficient sheaf
is finite free over the completed O_E coefficient sheaf. Derived change of rings
therefore identifies the n-th reduction of the restricted input with restriction
of its (e*n)-th reduction along the induced finite quotient coefficient map.
Restriction is exact. Each given finite constructible stratification, local
trivializing cover and finite constant module model remains such a model after
restriction: the quotient coefficient rings are finite, so a finite module is
still finite. Sheafification commutes with this restriction by its universal
property, and restriction to a stratum commutes sectionwise. These identifications
preserve the original common cohomological interval. The comparison is
ramification-indexed at e * n rather than levelwise at n. Together with completeness
this is precisely the intrinsic predicate, without a geometric noetherian or
dimension assumption. Zero complexes and empty schemes satisfy the same argument;
ramified extensions use e*n rather than equality of uniformizer powers. -/
theorem rationalScalarDerivedRestriction_constructible
    (K : sfIntegralConstructibleCategory l F W) :
    sfIntegralConstructible l E W
      ((rationalScalarDerivedRestriction l E F ι W).obj K.obj) := by
  rw [sfIntegralConstructible]
  exact ⟨rationalScalarDerivedRestriction_complete l E F ι W K,
    rationalScalarDerivedRestriction_reduction_constructible l E F ι W K⟩

end WeilConjectures
