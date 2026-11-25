/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenFactorCoherence.OpenFactorPullModel
import WeilConjectures.SixFunctors.IntegralSystemRealization.Ringed.IntegralRingedPullCompletion

/-! # Strict quotient normalization of completed open pullback -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.IntegralOnSlice.abSheafify
attribute [-instance] WeilConjectures.IntegralOnSlice.abLocallyBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.PurCompactSupport
namespace WeilConjectures.OpenFactorCoherence
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The completed open pullback has the published strict quotient-tower model.
Source: Stacks 099N(2),(5), 0941; Bhatt--Scholze 6.5.8.
(blueprint: lem-sf-open-factor-pull-realization).

Proof: inverse image along an open immersion is exact. Its coefficient map preserves
the constant sections and all quotient projections. The balanced scalar comparison
therefore gives, simultaneously in n, an isomorphism from the quotient tower of
the termwise pullback to integralOperationsPullbackTowerFunctor. Its formula on
1 tensor x is exactly the generators equation in Pull. Naturality on the quotient
maps makes this an isomorphism of strict towers. Pullback preserves flat terms
and K-flatness: exact extension by zero is its exact left adjoint, and the
coefficient-compatible tensor adjunction tests acyclicity on the open. Thus good
representatives pull back to good representatives. Apply the signed Roos functor
to the strict tower isomorphism and localize. The two localized functors are
computed on these same good representatives, so their localization universal
property gives comparison, with the displayed representative equation model.
Empty opens and zero representatives give the same equations. This concerns only
pullback normalization; it asserts neither extension-completion commutation nor
constructibility or any complete-subcategory equivalence. -/
theorem openFactorPullRealization
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Nonempty (Pull l E j) := by
  exact IntegralSystemRealization.integralRingedPullCompletion l E j

end WeilConjectures.OpenFactorCoherence
