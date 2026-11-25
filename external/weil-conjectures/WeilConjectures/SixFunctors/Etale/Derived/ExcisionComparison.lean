/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ClosedImmersionPositiveDegree
public import WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekBaseChange

/-!
# The excision comparison is not the base-change comparison

For a cartesian square with `f = 𝟙_Y` and `g = g' : Y' ⟶ Y` an open immersion, the base-change
comparison `Lg'^* Rf^! ⟶ Rf'^! Lg^*` of the exceptional inverse image is an isomorphism, whereas
the excision comparison `Rf_!(g'_! ⟶ g'_*)`, which is `g_! ⟶ Rg_*`, need not be one (blueprint
`ex-exc-excision-is-not-the-comparison`). The counterexample is the punctured affine line
`j : 𝔾_{m,k} ⟶ 𝔸¹_k` over a separably closed field `k`: the stalk of `Rj_* Λ` at the origin is
nonzero, whereas that of `j_! Λ` vanishes.

## The argument

The blueprint reads off the stalk of `j_* Λ` at the origin from the description of direct
images. Here it is read off from the closed support triangle
`s_* Rs^! Λ_T ⟶ Λ_T ⟶ Rj_* Λ_G ⟶` of the zero section `s` (blueprint
`lemma-local-cohomology-right-adjoint--2`): if `Ls^* Rj_* Λ_G` vanished, then
`Rs^! Λ_T ≅ Ls^* Λ_T ≅ Λ_k` would have nonzero `𝓗⁰`, whereas `(Rs^! Λ_T)[2] ≅ Λ_k` by purity
(`Etale.nonempty_iso_shift_rightDerivedUpperShriek_affineLineZero_of_isSepClosed`).
This route needs a normalized Tate twist datum.

## Main statements

- `AlgebraicGeometry.Etale.not_isZero_leftDerivedUpperStar_zeroSection_rightDerivedLowerStar`:
  `Ls^* Rj_* Λ_G ≠ 0`.
- `AlgebraicGeometry.Etale.isIso_baseChange_and_not_isIso_excision_affineLine`: the
  counterexample.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [Nontrivial Λ] [HasTateTwist Λ]
  [HasTateTwist.IsNormalized Λ] (k : Type u) [Field k] [IsSepClosed k]
  [HasInvertibleExponent Λ (Spec (.of k))]
  {G : Scheme.{u}} (j : G ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k))) [IsOpenImmersion j]

/-- For the open complement `j : G ⟶ 𝔸¹_k` of the zero section `s` over a separably closed
field, `Ls^* Rj_* Λ_G ≠ 0`: the closed support triangle `s_* Rs^! Λ ⟶ Λ ⟶ Rj_* Λ_G ⟶` would
otherwise give `Rs^! Λ ≅ Λ_k`, contradicting `(Rs^! Λ)[2] ≅ Λ_k`. -/
theorem not_isZero_leftDerivedUpperStar_zeroSection_rightDerivedLowerStar
    (hj : Set.range j.base =
      (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) (Spec (.of k))).base)ᶜ) :
    ¬ IsZero ((L((AffineSpace.zeroSection (ULift.{u} (Fin 1)) (Spec (.of k)))^*[
        ModuleCat.{u + 1} Λ])).obj
      ((R((j)_*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ G))) := by
  have hij : Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) (Spec (.of k))).base =
      (Set.range j.base)ᶜ := by
    rw [hj, compl_compl]
  let T := 𝔸(ULift.{u} (Fin 1); Spec (.of k))
  let s := AffineSpace.zeroSection (ULift.{u} (Fin 1)) (Spec (.of k))
  have : HasInvertibleExponent Λ T := .of_hom (T ↘ Spec (.of k))
  have : HasInvertibleExponent Λ G := .of_hom (j ≫ T ↘ Spec (.of k))
  intro h
  obtain ⟨w, hw⟩ := (existsUnique_distTriang_closedSupportTriangle s j hij
    (constantComplex Λ T)).exists
  have hT := (L((s)^*[ModuleCat.{u + 1} Λ])).map_distinguished _ hw
  have h₃ : IsZero ((L((s)^*[ModuleCat.{u + 1} Λ])).obj ((R((j)_*[ModuleCat.{u + 1} Λ])).obj
      ((L((j)^*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ T)))) :=
    h.of_iso ((L((s)^*[ModuleCat.{u + 1} Λ])).mapIso ((R((j)_*[ModuleCat.{u + 1} Λ])).mapIso
      (leftDerivedUpperStarConstantComplexIso Λ j)))
  have h₁ := (Triangle.isZero₃_iff_isIso₁ _ hT).1 h₃
  -- `Ls^* Rs_* ≅ 𝟭`, `Rs_*` being fully faithful
  have := (fullyFaithfulRightDerivedLowerStarOfIsClosedImmersion (Λ := Λ) s).full
  have := (fullyFaithfulRightDerivedLowerStarOfIsClosedImmersion (Λ := Λ) s).faithful
  have : IsIso (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) s).counit :=
    (derivedUpperStarLowerStarAdjunction _ s).counit_isIso_of_R_fully_faithful
  -- hence `Rs^! Λ_T ≅ Λ_k`
  let e : (R(s)^![Λ]).obj (constantComplex Λ T) ≅
      constantComplex Λ (Spec (.of k)) :=
    ((rightDerivedUpperShriekAdjunction Λ s).rightAdjointUniq
        (Adjunction.ofIsLeftAdjoint (R(s)_![ModuleCat.{u + 1} Λ]))).app _ ≪≫
      ((asIso (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) s).counit).app _).symm ≪≫
      @asIso _ _ _ _ _ h₁ ≪≫ leftDerivedUpperStarConstantComplexIso Λ s
  obtain ⟨e'⟩ := nonempty_iso_shift_rightDerivedUpperShriek_affineLineZero_of_isSepClosed Λ k
  -- `𝓗⁰(Λ_k) ≅ 𝓗⁰(Rs^! Λ_T) ≅ 𝓗⁻²(Λ_k) = 0`
  refine not_isZero_homology_zero_constantComplex_spec Λ k
    ((isZero_homology_constantComplex Λ (Spec (.of k)) (-2) (by norm_num)).of_iso ?_)
  exact (DerivedCategory.homologyFunctor _ 0).mapIso e.symm ≪≫
    (((DerivedCategory.homologyFunctor _ 0).shiftIso (2 * 1 : ℤ) (-2) 0
      (by norm_num)).app _).symm ≪≫
    (DerivedCategory.homologyFunctor _ (-2)).mapIso e'

/-- For the open complement `j : G ⟶ 𝔸¹_k` of the zero section over a separably closed field,
the excision comparison `j_! Λ_G ⟶ Rj_* Λ_G`
(`AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekToLowerStar`) is not an isomorphism: its
source vanishes at the origin, its target does not
(`AlgebraicGeometry.Etale.not_isZero_leftDerivedUpperStar_zeroSection_rightDerivedLowerStar`). -/
theorem not_isIso_derivedOpenImmersionLowerShriekToLowerStar_app_affineLine
    (hj : Set.range j.base =
      (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) (Spec (.of k))).base)ᶜ) :
    ¬ IsIso ((derivedOpenImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) j).app
      (constantComplex Λ G)) := fun h ↦
  not_isZero_leftDerivedUpperStar_zeroSection_rightDerivedLowerStar Λ k j hj
    ((isZero_leftDerivedUpperStar_obj_mapDerivedCategory_openImmersionLowerShriek_of_disjoint_range
      (ModuleCat.{u + 1} Λ) j _ (hj ▸ disjoint_compl_right) _).of_iso
      ((L((AffineSpace.zeroSection (ULift.{u} (Fin 1)) (Spec (.of k)))^*[
        ModuleCat.{u + 1} Λ])).mapIso (@asIso _ _ _ _ _ h).symm))

/-- Blueprint `ex-exc-excision-is-not-the-comparison`: The excision comparison is not the
base-change comparison.

Take `f = 𝟙` on the affine line `T = 𝔸¹_k` over a separably closed field `k`, and let
`g = j : G ⟶ T` be the open complement of the origin, so that the square `j ≫ 𝟙 = 𝟙 ≫ j` is
cartesian. The base-change comparison `Lj^* R𝟙^! ⟶ R𝟙^! Lj^*`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap`) is an isomorphism, whereas the
excision comparison `R𝟙_!(j_! ⟶ Rj_*)`, i.e. `j_! ⟶ Rj_*`, is not an isomorphism at `Λ_G`.
Hence the two statements are not equivalent. -/
theorem isIso_baseChange_and_not_isIso_excision_affineLine
    (hj : Set.range j.base =
      (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) (Spec (.of k))).base)ᶜ) :
    IsIso (rightDerivedUpperShriekBaseChangeMap Λ
        (IsPullback.of_vert_isIso (fst := j) (snd := 𝟙 _) (f := 𝟙 _) (g := j) ⟨by simp⟩)) ∧
      ¬ IsIso ((derivedOpenImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) j).app
        (constantComplex Λ G)) :=
  ⟨isIso_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion Λ _,
    not_isIso_derivedOpenImmersionLowerShriekToLowerStar_app_affineLine Λ k j hj⟩

end Etale

end AlgebraicGeometry
