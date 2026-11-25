/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.StalkFunctor
public import WeilConjectures.WeilSheaf.Triangle

/-!
# Exactness of the pullback of Weil sheaves

The pullback `φ^*` of Weil sheaves along a morphism of `k₀`-schemes is exact: it is the
restriction of the exact pullback of pro-étale Weil sheaves, and the inclusion of Weil sheaves
into pro-étale Weil sheaves is fully faithful and exact.

## Main statements

- `AlgebraicGeometry.WeilSheaf.shortExact_map_upperStar`: the pullback of a short exact sequence
  of Weil sheaves is short exact.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]

instance : PreservesFiniteLimits (upperStar (k₀ := k₀) (l := l) φ) := by
  have : PreservesFiniteLimits (upperStar (k₀ := k₀) (l := l) φ ⋙
      (WeilSheaf.objectProperty k₀ l X).ι) :=
    preservesFiniteLimits_of_natIso (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _).symm
  have : ReflectsLimitsOfSize.{0, 0} (WeilSheaf.objectProperty k₀ l X).ι := inferInstance
  exact preservesFiniteLimits_of_reflects_of_preserves _ (WeilSheaf.objectProperty k₀ l X).ι

instance : PreservesFiniteColimits (upperStar (k₀ := k₀) (l := l) φ) := by
  have : PreservesFiniteColimits (upperStar (k₀ := k₀) (l := l) φ ⋙
      (WeilSheaf.objectProperty k₀ l X).ι) :=
    preservesFiniteColimits_of_natIso (ObjectProperty.liftFullSubcategoryCompιIso _ _ _ _).symm
  have : ReflectsColimitsOfSize.{0, 0} (WeilSheaf.objectProperty k₀ l X).ι := inferInstance
  exact preservesFiniteColimits_of_reflects_of_preserves _ (WeilSheaf.objectProperty k₀ l X).ι

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- The pullback of Weil sheaves preserves short exact sequences. -/
theorem shortExact_map_upperStar {S : ShortComplex (WeilSheaf k₀ l Y)} (hS : S.ShortExact) :
    (S.map (upperStar φ)).ShortExact :=
  hS.map_of_exact _

end AlgebraicGeometry.WeilSheaf
