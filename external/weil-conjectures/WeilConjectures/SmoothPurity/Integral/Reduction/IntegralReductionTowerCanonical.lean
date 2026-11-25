/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Integral.IntegralReductionTowerWellDefinedUnrestricted
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Cones

/-! # The integral reduction tower

Source: Bhatt--Scholze, p. 24, Proposition 3.5.1(1) and Definition 3.5.2;
Stacks Project, Tag 06YL (blueprint: def-weil-integral-reduction-tower).

The natural-number index n denotes exponent n+1. We use the chosen complex
representative K and its chosen K-flat resolution q:P→K. The already recorded
chain-level maps are characterized by the sheafified pure-tensor formulas.

The interface omits the unused auxiliary finite-field datum. It uses the existing
completed coefficient ring, projections and scalar extension with independent
site and coefficient universes.

## Main definitions

- `canonicalIntegralReductionTower`: the inverse system of restricted finite reductions.
- `canonicalIntegralReductionTowerMap`: the compatible maps from the represented object.
- `canonicalIntegralReductionTowerCone`: the augmented reduction tower.
-/

@[expose] public section

set_option autoImplicit false

universe t u

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : AlgebraicGeometry.Scheme.{t})

/-- The inverse system of the restricted termwise reductions of P, with transitions
[id⊗ρ_n]. For a K-flat resolution of K this represents Res_n(K⊗ᴸA_{E,n+1}).
Source: Bhatt--Scholze, p. 24, Definition 3.5.2; Stacks Tag 06YL
(blueprint: def-weil-integral-reduction-tower). -/
noncomputable def canonicalIntegralReductionTower
    (P : CochainComplex (scalarReductionSource l E Y) ℤ) :
    ℕᵒᵖ ⥤ DerivedCategory (scalarReductionSource l E Y) :=
  Functor.ofOpSequence
    (X := fun n ↦ DerivedCategory.Q.obj (unrestrictedTowerComplex l E Y n P))
    (fun n ↦
    DerivedCategory.Q.map (unrestrictedTowerTransition l E Y P n))

/-- The map c_n=[q]⁻¹≫[γ_n] to the reduction at exponent n+1, where γ_n(x)=x⊗1.
Source: Bhatt--Scholze, p. 24, Definition 3.5.2; Stacks Tag 06YL
(blueprint: def-weil-integral-reduction-tower). -/
noncomputable def canonicalIntegralReductionTowerMap
    {P K : CochainComplex (scalarReductionSource l E Y) ℤ}
    (q : P ⟶ K)
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheafUnrestricted l E Y) q) (n : ℕ) :
    DerivedCategory.Q.obj K ⟶ (canonicalIntegralReductionTower l E Y P).obj (op n) :=
  (unrestrictedTowerAugmentationIso l E Y q hq).inv ≫
    DerivedCategory.Q.map (unrestrictedTowerUnit l E Y P n)

end WeilConjectures
