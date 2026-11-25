/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Compact.CompactSupportNativeTowerPresentation

/-! # The specification of a compact-support reduction tower

Naming the proposition keeps repeated dependent choice predicates small.
Source: the coherent compact-support tower construction and its canonical
coefficient comparisons, blueprint `lemma-change-coefficients-compact-support`.
(blueprint: def-weil-compact-support-reduction-tower-functor-spec).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
  [Linear (Padic.coefficientExtensionIntegers l E) (scalarReductionSource l E X)]
  [Linear (Padic.coefficientExtensionIntegers l E) (scalarReductionSource l E Y)]

/-- The linearity, exactness, canonical evaluations, quotient transitions, and
native presentation of one compact-support reduction tower.
Source: blueprint `lemma-change-coefficients-compact-support`, canonical coefficient comparisons.
(blueprint: def-weil-compact-support-reduction-tower-functor-spec). -/
def CompactSupportReductionTowerFunctorSpec
    (T : DerivedCategory (scalarReductionSource l E X) ⥤
      DerivedCategory (pbcTowers Y (completedIntegralCommRingSheafUnrestricted l E Y))) : Prop :=
  T.Linear (Padic.coefficientExtensionIntegers l E) ∧
  ∃ (_shift : T.CommShift ℤ), T.IsTriangulated ∧
    ∃ e : ∀ n : ℕ,
        T ⋙ pbcTowerEvaluation Y (completedIntegralCommRingSheafUnrestricted l E Y) n ≅
          compactSupportRestrictedLevel l E c n,
      (∀ (m n : ℕ) (h : n ≤ m) (K : DerivedCategory (scalarReductionSource l E X)),
        (pbcTowerTransition Y (completedIntegralCommRingSheafUnrestricted l E Y)
            m n h).app (T.obj K) ≫ (e n).hom.app K =
          (e m).hom.app K ≫ compactSupportRestrictedTransition l E c m n h K) ∧
      IsNativeCompactSupportTowerPresentation l E c T e

end WeilConjectures
