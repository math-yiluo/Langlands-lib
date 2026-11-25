/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.FourierInversion.Defs

/-!
# Functions to the affine line

Composition rules for the morphism `X ⟶ 𝔸¹` defined by a global function
(`AlgebraicGeometry.affineLine.homOfSection`): pullback of the function, scaling, and the
Artin–Schreier map.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀]

section HomOfSection

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

omit [Finite k₀] in
/-- The coordinate of the morphism `X ⟶ 𝔸¹` defined by a function `a` is `a`. -/
@[simp]
lemma affineLine.homOfSection_appTop_coord (a : Γ(X, ⊤)) :
    (affineLine.homOfSection k₀ a).appTop (AffineSpace.coord _ PUnit.unit) = a :=
  AffineSpace.homOfVector_appTop_coord _ _ _

omit [Finite k₀] in
/-- The composite of a function `a : X ⟶ 𝔸¹` with the scaling `x ↦ c x` is the function `c a`. -/
lemma affineLine.homOfSection_comp_smul (a : Γ(X, ⊤)) (c : k₀) :
    affineLine.homOfSection k₀ a ≫ affineLine.smul k₀ c =
      affineLine.homOfSection k₀
        ((X ↘ Spec (CommRingCat.of k₀)).appTop ((Scheme.ΓSpecIso (.of k₀)).inv.hom c) * a) := by
  refine AffineSpace.hom_ext ?_ fun i ↦ ?_
  · simp [affineLine.homOfSection, affineLine.smul]
  · simp only [affineLine.smul, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      AffineSpace.smul_appTop_coord, map_mul]
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
    simp [affineLine.homOfSection]

/-- The composite of a function `a : X ⟶ 𝔸¹` with the Artin–Schreier map is `a ^ q - a`. -/
lemma affineLine.homOfSection_comp_artinSchreierMap (a : Γ(X, ⊤)) :
    letI := Fintype.ofFinite k₀
    affineLine.homOfSection k₀ a ≫ affineLine.artinSchreierMap k₀ =
      affineLine.homOfSection k₀ (a ^ Fintype.card k₀ - a) := by
  refine AffineSpace.hom_ext ?_ fun i ↦ ?_
  · simp [affineLine.homOfSection, affineLine.artinSchreierMap]
  · simp [affineLine.artinSchreierMap, affineLine.homOfSection]

omit [Finite k₀] in
/-- The composite of a function `a : X ⟶ 𝔸¹` with the reflection `x ↦ -x` is the function `-a`. -/
lemma affineLine.homOfSection_comp_smul_neg_one (a : Γ(X, ⊤)) :
    affineLine.homOfSection k₀ a ≫ affineLine.smul k₀ (-1) = affineLine.homOfSection k₀ (-a) := by
  rw [affineLine.homOfSection_comp_smul]
  simp

omit [Finite k₀] in
/-- The composite of a morphism `φ : Y ⟶ X` over `k₀` with the function `a : X ⟶ 𝔸¹` is the
function `φ^* a`. -/
lemma affineLine.comp_homOfSection {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]
    (φ : Y ⟶ X) [φ.IsOver (Spec (CommRingCat.of k₀))] (a : Γ(X, ⊤)) :
    φ ≫ affineLine.homOfSection k₀ a = affineLine.homOfSection k₀ (φ.appTop a) := by
  rw [affineLine.homOfSection, affineLine.homOfSection, AffineSpace.comp_homOfVector,
    comp_over]
  rfl

end HomOfSection

end AlgebraicGeometry
