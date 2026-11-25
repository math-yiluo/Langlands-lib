/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityCompactHomotopy
public import WeilConjectures.WeilSheaf.SmoothPurityThom

/-!
# Compact constant cohomology of the affine line from absolute purity

The ordinary affine-line unit is invertible by homotopy invariance. Verdier
exchange and absolute purity convert this to the compact Tate calculation.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilComplex

attribute [local instance 1100] CategoryTheory.instOverClass

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  [HasUpperShriek k₀ l ((Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀))]

/-- The dualizing object of the finite-field point is its constant object. -/
theorem nonempty_point_dualizing_iso_constant :
    Nonempty (dualizingComplex k₀ l (Spec (CommRingCat.of k₀)) ≅
      WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀)))) := by
  let a := Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)
  let eL : derivedLowerShriek k₀ l a ≅ 𝟭 _ :=
    derivedLowerShriekIsoDerivedLowerStar a ≪≫ derivedLowerStarIdIso
  let eR := ((derivedLowerShriekUpperShriekAdjunction (k₀ := k₀) (l := l) a).ofNatIsoLeft
    eL).rightAdjointUniq (Adjunction.id)
  exact ⟨eR.app _⟩

variable [HasUpperShriek k₀ l (affineLine k₀ ↘ Spec (CommRingCat.of k₀))]

/-- Absolute purity of the affine line determines its compact constant complex. -/
theorem nonempty_affineLine_compact_constant_iso_of_absolute_purity
    (eX : dualizingComplex k₀ l (affineLine k₀) ≅
      ((tateTwist k₀ l (affineLine k₀) 1).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l (affineLine k₀)))) ⟦(2 : ℤ)⟧) :
    Nonempty ((derivedLowerShriek k₀ l (affineLine k₀ ↘ Spec (CommRingCat.of k₀))).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l (affineLine k₀))) ≅
      (WeilSheaf.toComplex.obj
        (WeilSheaf.tateTwistSheaf k₀ l (Spec (CommRingCat.of k₀)) (-1))) ⟦(-2 : ℤ)⟧) := by
  let a := affineLine k₀ ↘ Spec (CommRingCat.of k₀)
  let U := WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀)))
  have := isIso_unit_app_toComplex_of_isLisse a (𝟙 _) IsPullback.of_id_snd
    (WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀)))
    (WeilSheaf.isLisse_adicConstant k₀ l (Spec (CommRingCat.of k₀)))
  let h : (derivedLowerStar a).obj
      (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l (affineLine k₀))) ≅ U :=
    (derivedLowerStar a).mapIso (purityUpperStarConstantIso a).symm ≪≫
      (asIso ((upperStarDerivedLowerStarAdjunction a).unit.app U)).symm
  obtain ⟨eY⟩ := nonempty_point_dualizing_iso_constant (k₀ := k₀) (l := l)
  obtain ⟨e⟩ := nonempty_compact_constant_iso_of_absolute_purity a 1 h eX eY
  exact ⟨e ≪≫ (shiftFunctor _ (-2 : ℤ)).mapIso (tateTwistConstantSingleIso (-1))⟩

end AlgebraicGeometry.WeilComplex
