/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.LowerShriekForget
public import WeilConjectures.WeilSheaf.SmoothPurityTraceCriterion

/-!
# Testing a native trace on the geometric fibre

The compact-support free comparison supplies the free-object hypothesis of the
universal-arrow criterion. Thus a native trace whose geometric realization is universal
has an invertible adjoint transpose.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X Y : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]

/-- A geometric universal arrow lifts to a native purity isomorphism. -/
theorem isIso_homEquiv_of_geometric_trace
    {J : WeilComplex k₀ l Y ⥤ WeilComplex k₀ l X}
    (adj : derivedLowerShriek k₀ l f ⊣ J) {P : WeilComplex k₀ l X}
    {T : WeilComplex k₀ l Y} (ε : (derivedLowerShriek k₀ l f).obj P ⟶ T)
    (h : ∀ (K : WeilComplex k₀ l X) (n : ℤ), Function.Bijective
      fun φ : (shiftFunctor _ n).obj (forget.obj K) ⟶ forget.obj P ↦
        (ProEtaleWeilSheaf.geometricRightDerivedLowerShriek k₀ l f
          (lowerShriekCompactification k₀ f)).map φ ≫
        (ProEtaleWeilSheaf.rightDerivedLowerShriekCompForgetIso k₀ l f
          (lowerShriekCompactification k₀ f)).inv.app P.obj ≫ forget.map ε) :
    IsIso (adj.homEquiv P T ε) := by
  apply Adjunction.isIso_homEquiv_of_bijective adj ε
  intro K
  exact bijective_map_comp_derivedLowerShriek f ε
    (isIso_freeComparison_rightDerivedLowerShriek f K) (h K)

end AlgebraicGeometry.WeilComplex
