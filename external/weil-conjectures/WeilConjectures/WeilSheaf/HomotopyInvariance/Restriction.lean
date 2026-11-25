/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.HomotopyInvariance.Basic

/-!
# Homotopy invariance and direct images

Let `π : Y ≅ X ×_{k₀} 𝔸¹ ⟶ X` be the trivial line bundle and `g : Z ⟶ X` a separated
morphism of `k₀`-schemes. The base change `Y ×_X Z ⟶ Z` of `π` along `g` is the trivial line
bundle over `Z`.
If the unit `M ⟶ Rπ'_* π'^* M` is an isomorphism for a Weil complex `M` on `Z` and every trivial
line bundle `π'` over `Z`, then the unit `Rg_* M ⟶ Rπ_* π^* Rg_* M` is an isomorphism
(`AlgebraicGeometry.WeilComplex.isIso_unit_app_derivedLowerStar_obj`). This is the smooth base
change theorem for the cartesian square of `π` and `g`
(`AlgebraicGeometry.WeilComplex.isIso_baseChange_of_smooth`), through the mate description of
the base change morphism
(`AlgebraicGeometry.WeilComplex.isIso_unit_app_derivedLowerStar_obj_of_isIso_baseChange_app`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (π : Y ⟶ X) (s : Y ⟶ affineLine k₀)
  [π.IsOver (Spec (CommRingCat.of k₀))]
  (hπ : IsPullback π s (X ↘ Spec (CommRingCat.of k₀))
    (affineLine k₀ ↘ Spec (CommRingCat.of k₀)))
  [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

include hπ in
/-- Let `g : Z ⟶ X` be a separated morphism of `k₀`-schemes of finite type, quasi-compact and
quasi-separated, and `M` a Weil complex on `Z` such that the unit `M ⟶ Rπ'_* π'^* M` is an
isomorphism for every trivial line bundle `π' : Y' ≅ Z ×_{k₀} 𝔸¹ ⟶ Z`. Then the unit
`Rg_* M ⟶ Rπ_* π^* Rg_* M` is an isomorphism: apply the hypothesis to the base change
`Y ×_X Z ⟶ Z` of `π`, and smooth base change to the cartesian square of `π` and `g`. -/
theorem isIso_unit_app_derivedLowerStar_obj {Z : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Z ↘ Spec (CommRingCat.of k₀))] (g : Z ⟶ X)
    [g.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated g] [QuasiCompact g] [QuasiSeparated g]
    [LocallyOfFiniteType g] (M : WeilComplex k₀ l Z)
    (H : ∀ (Y' : Scheme.{u}) [Y'.Over (Spec (CommRingCat.of k₀))] (π' : Y' ⟶ Z)
      (s' : Y' ⟶ affineLine k₀) [π'.IsOver (Spec (CommRingCat.of k₀))],
      IsPullback π' s' (Z ↘ Spec (CommRingCat.of k₀))
        (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) →
      ∀ [IsSeparated π'] [LocallyOfFiniteType π'] [QuasiCompact π'],
        IsIso ((upperStarDerivedLowerStarAdjunction (k₀ := k₀) (l := l) π').unit.app M)) :
    IsIso ((upperStarDerivedLowerStarAdjunction (k₀ := k₀) (l := l) π).unit.app
      ((derivedLowerStar g).obj M)) := by
  let : (pullback π g).Over (Spec (CommRingCat.of k₀)) :=
    ⟨pullback.snd π g ≫ Z ↘ Spec (CommRingCat.of k₀)⟩
  have : (pullback.snd π g).IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : (pullback.fst π g).IsOver (Spec (CommRingCat.of k₀)) := ⟨by
    rw [← comp_over π, ← Category.assoc, pullback.condition, Category.assoc, comp_over g]
    rfl⟩
  have : LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over π]
    infer_instance
  have : QuasiCompact (Y ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over π]
    infer_instance
  have hπ' : IsPullback (pullback.snd π g) (pullback.fst π g ≫ s)
      (Z ↘ Spec (CommRingCat.of k₀)) (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over g]
    exact (IsPullback.of_hasPullback π g).flip.paste_vert hπ
  have := smooth_of_isPullback hπ
  have := isIso_baseChange_of_smooth (k₀ := k₀) (l := l) (IsPullback.of_hasPullback π g)
  have := H _ (pullback.snd π g) _ hπ'
  exact isIso_unit_app_derivedLowerStar_obj_of_isIso_baseChange_app
    (IsPullback.of_hasPullback π g).w M

end AlgebraicGeometry.WeilComplex
