/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.LowerShriekIndependence
public import WeilConjectures.WeilSheaf.FourierInversion.TensorLisse

/-!
# Smooth purity along open immersions

For an open immersion, the compact-support direct image is extension by zero. Its right
adjoint is the ordinary pullback, which is the purity functor in relative dimension zero.
This case uses the extension-by-zero adjunction independently of general smooth purity.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

variable (k₀ l X) in
/-- The zero Tate twist of Weil complexes is the identity. -/
noncomputable def tateTwistZeroIso [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] :
    tateTwist k₀ l X 0 ≅ 𝟭 (WeilComplex k₀ l X) :=
  nonempty_iso_tensorLisse_adicConstant.some

variable (j : X ⟶ Y) [j.IsOver (Spec (CommRingCat.of k₀))]
  [IsOpenImmersion j] [QuasiCompact j]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- The smooth-purity adjunction in relative dimension zero for an open immersion. -/
theorem nonempty_derivedLowerShriek_adjunction_of_isOpenImmersion :
    Nonempty (derivedLowerShriek k₀ l j ⊣
      upperStar j ⋙ tateTwist k₀ l X 0 ⋙ shiftFunctor (WeilComplex k₀ l X) (2 * 0 : ℤ)) := by
  obtain ⟨e⟩ := nonempty_derivedLowerShriek_iso_extensionByZero (k₀ := k₀) (l := l) j
  let eT : tateTwist k₀ l X 0 ⋙ shiftFunctor (WeilComplex k₀ l X) (2 * 0 : ℤ) ≅
      𝟭 (WeilComplex k₀ l X) :=
    Functor.isoWhiskerRight (tateTwistZeroIso k₀ l X) _ ≪≫ Functor.leftUnitor _ ≪≫
      shiftFunctorZero' _ _ (by simp)
  let eR : upperStar j ⋙ tateTwist k₀ l X 0 ⋙
      shiftFunctor (WeilComplex k₀ l X) (2 * 0 : ℤ) ≅ upperStar (k₀ := k₀) (l := l) j :=
    Functor.isoWhiskerLeft (upperStar j) eT ≪≫ Functor.rightUnitor _
  exact ⟨((extensionByZeroUpperStarAdjunction j).ofNatIsoLeft e.symm).ofNatIsoRight eR.symm⟩

end AlgebraicGeometry.WeilComplex
