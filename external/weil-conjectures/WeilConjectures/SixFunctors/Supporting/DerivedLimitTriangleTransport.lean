/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit

@[expose] public section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

/-- Transport a derived-limit triangle along an isomorphism of its vertex. -/
theorem derivedLimitTriangleTransport
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] {T : ℕ → C} [HasProduct T]
    (t : ∀ n, T (n + 1) ⟶ T n) {A B : C}
    (e : A ≅ B) (p : B ⟶ ∏ᶜ T) (δ : ∏ᶜ T ⟶ B⟦(1 : ℤ)⟧)
    (h : IsDerivedLimitTriangle t B p δ) :
    IsDerivedLimitTriangle t A (e.hom ≫ p)
      (δ ≫ (shiftFunctor C (1 : ℤ)).map e.inv) := by
  let T₁ := Pretriangulated.Triangle.mk p
    (CategoryTheory.towerTransitionEndomorphism t) δ
  let T₂ := Pretriangulated.Triangle.mk (e.hom ≫ p)
    (CategoryTheory.towerTransitionEndomorphism t)
    (δ ≫ (shiftFunctor C (1 : ℤ)).map e.inv)
  apply Pretriangulated.isomorphic_distinguished T₁ h T₂
  refine Pretriangulated.Triangle.isoMk _ _ e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · simp [T₁, T₂]
  · simp [T₁, T₂]
  · simp [T₁, T₂, ← Functor.map_comp]
