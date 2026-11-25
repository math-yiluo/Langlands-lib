/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientConstructibleEtaleModules
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekLocality
import Mathlib.RingTheory.Ideal.Quotient.Index

/-!
# Constructibility of the ordinary proper exceptional adjoint

Source: Zheng, Six operations and Lefschetz--Verdier formula for Deligne--Mumford stacks,
Propositions 3.16(2) and 2.29(2); Bhatt--Scholze, The pro-etale topology for schemes,
Lemma 6.7.18 (blueprint: lem-sfb-ordinary-exceptional-ctf-preservation).

This is the finite-coefficient preservation step of the third proof sentence of
`theorem-exceptional-inverse-image--16` in the current blueprint. The categories
are the ordinary unbounded small etale derived categories. Constructibility uses the
existing finite-stratification predicate; on these Noetherian schemes it is the same
notion as the affine-local predicate of `def-pe-etale-constructible-module`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace Padic

/-- The literal quotient `O_E / ell^r O_E`. This uses the recorded ring of integers
and Mathlib's principal-ideal quotient, rather than replacing `ell` by a uniformizer.
Source: Zheng, Propositions 3.16(2), 2.29(2), with the coefficient convention of
`def-weil-l-adic-coefficient-extension`
(blueprint: lem-sfb-ordinary-exceptional-ctf-preservation). -/
abbrev coefficientExtensionEllQuotient (ell : ℕ) [Fact ell.Prime]
    (E : Type v) [Field E] [Algebra ℚ_[ell] E] [FiniteDimensional ℚ_[ell] E] (r : ℕ) :=
  coefficientExtensionIntegers ell E ⧸
    Ideal.span ({(ell : coefficientExtensionIntegers ell E) ^ r} :
      Set (coefficientExtensionIntegers ell E))

end Padic

namespace AlgebraicGeometry.Etale

end AlgebraicGeometry.Etale
