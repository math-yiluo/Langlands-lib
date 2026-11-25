/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Point.PointSectionsDerivedReductionData
import WeilConjectures.PoincareDuality.Point.PointSectionsDerivedReductionIso
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! Intermediate proof components for point sections derived reduction.
(blueprint: lem-pod-point-sections-derived-reduction) -/

@[expose] public section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale

namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The homology and exact-sections component of integral reduction.
Source: Stacks Tags 0946, 010N and 06YY; blueprint `lem-pod-point-sections-derived-reduction`.
Exact point sections applied to the comparison give this component in every degree.
(blueprint: lem-pod-point-sections-derived-reduction-homology)
-/
theorem point_sections_derived_reduction_homology (_hl : l ≠ D.p) (n : ℕ) :
    ∀ r : ℤ, Nonempty
      (pointReductionTensorSections D l E n ⋙ DerivedCategory.homologyFunctor _ r ≅
        (sfIntegralConstructible l E (Spec (.of D.k))).ι ⋙
          scalarReductionDerivedExtension l E (Spec (.of D.k)) n ⋙
            DerivedCategory.homologyFunctor _ r ⋙
              pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))) := by
  intro r
  let e := (point_sections_derived_reduction_iso D l E _hl n).some
  let h := (pointFiniteSections D.k
    (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategoryHomologyFunctorIso r
  exact ⟨Functor.isoWhiskerRight e (DerivedCategory.homologyFunctor _ r) ≪≫
    Functor.isoWhiskerLeft
      ((sfIntegralConstructible l E (Spec (.of D.k))).ι ⋙
        scalarReductionDerivedExtension l E (Spec (.of D.k)) n) h.symm⟩

end WeilConjectures
