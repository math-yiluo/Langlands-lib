/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityAbsoluteDescent
public import WeilConjectures.WeilSheaf.SmoothPurityAffineLineConstant
public import WeilConjectures.WeilSheaf.SmoothPuritySeparatedAdjunction

/-! # The trivial-line Thom functor from finite-base Tate descent -/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilComplex

attribute [local instance 1100] CategoryTheory.instOverClass

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

/-- The underived Tate encoding and absolute purity suffice for the Thom
functor; no relative smooth-purity adjunction is required. -/
theorem nonempty_trivialLineThom_of_tate_encoding
    (α : (ProEtaleWeilSheaf.toCondensed k₀ l (affineLine k₀)).obj
        (WeilSheaf.tateTwistSheaf k₀ l (affineLine k₀) 1).obj ≅
      (ProEtale.CondensedRing.geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj l)
        (affineLine k₀ ↘ Spec (CommRingCat.of k₀))).obj
          (ProEtale.tateTwist (affineLine k₀) l 1))
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [Y.Over (Spec (CommRingCat.of k₀))]
    (π : Y ⟶ X) (s : Y ⟶ affineLine k₀) [π.IsOver (Spec (CommRingCat.of k₀))]
    (hπ : IsPullback π s (X ↘ Spec (CommRingCat.of k₀))
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)))
    [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] :
    Nonempty (upperStar π ⋙ derivedLowerShriek k₀ l π ≅
      tateTwist k₀ l X (-1) ⋙ shiftFunctor _ (-2 : ℤ)) := by
  have : HasUpperShriek k₀ l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) :=
    isLeftAdjoint_derivedLowerShriek_of_separated_base _
  have : HasUpperShriek k₀ l (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)) :=
    isLeftAdjoint_derivedLowerShriek_of_separated_base _
  have : SmoothOfRelativeDimension 1 (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) := by
    simpa using AffineSpace.smoothOfRelativeDimension_over PUnit.{u + 1} (Spec (.of k₀))
  obtain ⟨eX⟩ := nonempty_shriekRightAdjoint_adicConstant_iso_of_tate_encoding 1 α
    (derivedLowerShriekUpperShriekAdjunction (affineLine k₀ ↘ Spec (CommRingCat.of k₀)))
  obtain ⟨e⟩ := nonempty_affineLine_compact_constant_iso_of_absolute_purity eX
  exact nonempty_trivialLineThom_of_affineLine_constant e π s hπ

end AlgebraicGeometry.WeilComplex
