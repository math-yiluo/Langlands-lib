/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Sf.SfIntegralReductionTowerSupplement

/-!
# Derived completeness without an auxiliary finite-field datum

Source: Bhatt--Scholze, Definition 3.5.2, p. 24; Stacks Tag 06YL
(blueprint: def-weil-derived-complete).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

/-- Completeness means that the canonical reduction units are the first map in the
Roos triangle. The existential product witness merely supplies the product used in
that triangle; no arbitrary completion or comparison map is chosen.
Source: Bhatt--Scholze, Definition 3.5.2; Stacks Tag 06YL
(blueprint: def-weil-derived-complete). -/
noncomputable def IsSfDerivedComplete (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : AlgebraicGeometry.Scheme.{u})
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) : Prop :=
  ∃ hprod : HasProduct (fun n : ℕ ↦ (sfDerivedReductionRestricted l E X n).obj K),
    letI := hprod
    ∃ δ : (∏ᶜ fun n : ℕ ↦ (sfDerivedReductionRestricted l E X n).obj K) ⟶ K⟦(1 : ℤ)⟧,
      IsDerivedLimitTriangle (fun n ↦ (sfDerivedReductionTransition l E X n).app K) K
        (Pi.lift (fun n ↦ (sfDerivedReductionUnit l E X n).app K)) δ

end WeilConjectures
