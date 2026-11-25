/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.CoproductsOfHomologyProperty
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum

/-!
# Amplitude of the direct image along an exact change of coefficients

Let `a : Λ ⟶ Λ'` be a morphism of commutative condensed rings whose extensions of scalars
`Λ'_X ⊗_{Λ_X} -` are exact, and `p : Z ⟶ Y` a morphism of schemes such that the (Push)
comparison `Λ'_Y ⊗ᴸ Rp_* K ⟶ Rp_*(Λ'_Z ⊗ᴸ K)` is invertible on bounded below complexes. If `Rp_*`
sends the constructible `Λ_Z`-modules, placed in degree `0`, into degrees `≤ d`, then it sends
into degrees `≤ d` every `Λ'_Z`-module `N` such that `N[0] ≅ Λ'_Z ⊗ᴸ K₀` for a bounded
constructible `Λ_Z`-complex `K₀`
(`ProEtale.CondensedRing.isLE_rightDerivedLowerStar_singleFunctor_of_extendScalars`).

Indeed `Rp_*(N[0]) ≅ Λ'_Y ⊗ Rp_* K₀`. In the truncation triangle
`τ^{< 1} K₀ ⟶ K₀ ⟶ τ^{≥ 1} K₀ ⟶`, the complex `Λ'_Y ⊗ Rp_* τ^{≥ 1} K₀ ≅ Rp_*(Λ'_Z ⊗ τ^{≥ 1} K₀)`
vanishes, `Λ'_Z ⊗ -` commuting with truncations and `N[0]` being concentrated in degree `0`,
while `Rp_* τ^{< 1} K₀` lies in degrees `≤ d` by dévissage
(`DerivedCategory.isLE_obj_of_isLE_of_homologyProperty`).

This is the passage from the integral to the rational coefficients, and from finite
subextensions `E` to `ℚ̄_ℓ`, in the proof of blueprint `lemma-uniform-bound-proper-direct-image--1`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor ZeroObject

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme DerivedCategory.TStructure

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ]

/-- If `Rp_*` sends the constructible `Λ_Z`-modules, in degree `0`, into degrees `≤ d`, it sends
the truncation `τ^{< 1} K₀` of a bounded constructible complex `K₀` into degrees `≤ d`, by
dévissage. -/
lemma isLE_rightDerivedLowerStar_truncLT_of_boundedConstructible {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (d : ℤ) (hd : ∀ N₀, IsConstructibleModuleObject (condensedRingObj Λ Z) N₀ →
      (R((p)_*⟦Λ⟧).obj ((DerivedCategory.singleFunctor _ 0).obj N₀)).IsLE d)
    (K₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z)))
    (hK₀ : boundedConstructible (condensedRingObj Λ Z) K₀) :
    (R((p)_*⟦Λ⟧).obj ((t.truncLT 1).obj K₀)).IsLE d := by
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (IsConstructibleModuleObject (condensedRingObj Λ Z)) :=
    ⟨fun e hM ↦ hM.of_iso e⟩
  have : ObjectProperty.ContainsZero (IsConstructibleModuleObject (condensedRingObj Λ Z)) :=
    ⟨0, isZero_zero _, isConstructibleModuleObject_of_isZero _ (isZero_zero _)⟩
  have hb : t.bounded ((t.truncLT 1).obj K₀) := by
    obtain ⟨⟨m, hm⟩, -⟩ := hK₀.1
    exact ⟨⟨m, inferInstance⟩, ⟨0, t.isLE_truncLT_obj _ _ _ (by lia)⟩⟩
  have hP : DerivedCategory.homologyProperty
      (IsConstructibleModuleObject (condensedRingObj Λ Z)) ((t.truncLT 1).obj K₀) :=
    (DerivedCategory.homologyProperty _).prop_of_iso
      ((t.truncLEIsoTruncLT 0 1 (by lia)).app K₀)
      (DerivedCategory.homologyProperty_truncLE hK₀.2 0)
  have : ((t.truncLT 1).obj K₀).IsLE 0 := t.isLE_truncLT_obj _ _ _ (by lia)
  simpa using DerivedCategory.isLE_obj_of_isLE_of_homologyProperty R((p)_*⟦Λ⟧) d _ hd _ hb hP 0


variable {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [IsCommMonObj Λ] [MonObj Λ']
  [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]
  [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]

/-- **Amplitude along an exact change of coefficients.** Let `a : Λ ⟶ Λ'` have exact extensions
of scalars, and let `p : Z ⟶ Y` have invertible (Push) comparisons on bounded below complexes. If
`Rp_*` sends the constructible `Λ_Z`-modules, in degree `0`, into degrees `≤ d`, it sends `N[0]`
into degrees `≤ d` for every `Λ'_Z`-module `N` with `N[0] ≅ Λ'_Z ⊗ᴸ K₀`, `K₀` bounded
constructible. -/
theorem isLE_rightDerivedLowerStar_singleFunctor_of_extendScalars {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (d : ℤ)
    (hpush : ∀ (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) (n : ℤ), K.IsGE n → IsIso ((derivedPushHom a p).app K))
    (hd : ∀ N₀, IsConstructibleModuleObject (condensedRingObj Λ Z) N₀ →
      (R((p)_*⟦Λ⟧).obj ((DerivedCategory.singleFunctor _ 0).obj N₀)).IsLE d)
    (K₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z)))
    (hK₀ : boundedConstructible (condensedRingObj Λ Z) K₀)
    {N : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ' Z)}
    (e : (Mod.extendScalars (coefficientMap a Z)).leftDerivedFunctor.obj K₀ ≅
      (DerivedCategory.singleFunctor _ 0).obj N) :
    (R((p)_*⟦Λ'⟧).obj ((DerivedCategory.singleFunctor _ 0).obj N)).IsLE d := by
  let φZ := Mod.extendScalars (coefficientMap a Z)
  let φY := Mod.extendScalars (coefficientMap a Y)
  -- the functor `K ↦ Λ'_Y ⊗ Rp_* K`, computed levelwise
  let G := R((p)_*⟦Λ⟧) ⋙ φY.mapDerivedCategory
  -- `G` vanishes on `τ^{≥ 1} K₀`
  have hGE : IsZero (G.obj ((t.truncGE 1).obj K₀)) := by
    have hZ : IsZero (φZ.leftDerivedFunctor.obj ((t.truncGE 1).obj K₀)) := by
      have : t.IsLE ((DerivedCategory.singleFunctor _ 0).obj N) 0 := inferInstance
      have h0 : IsZero ((t.truncGE 1).obj ((DerivedCategory.singleFunctor _ 0).obj N)) :=
        t.isZero_truncGE_obj_of_isLE 0 1 (by decide) _
      have e₁ : φZ.leftDerivedFunctor.obj ((t.truncGE 1).obj K₀) ≅
          φZ.mapDerivedCategory.obj ((t.truncGE 1).obj K₀) :=
        φZ.leftDerivedFunctorIsoMapDerivedCategory.app _
      have e₂ : φZ.mapDerivedCategory.obj ((t.truncGE 1).obj K₀) ≅
          (t.truncGE 1).obj (φZ.mapDerivedCategory.obj K₀) :=
        (φZ.mapDerivedCategoryTruncGEIso 1).app K₀
      have e₃ : φZ.mapDerivedCategory.obj K₀ ≅ (DerivedCategory.singleFunctor _ 0).obj N :=
        φZ.leftDerivedFunctorIsoMapDerivedCategory.symm.app K₀ ≪≫ e
      exact h0.of_iso (e₁ ≪≫ e₂ ≪≫ (t.truncGE 1).mapIso e₃)
    have := hpush ((t.truncGE 1).obj K₀) 1 inferInstance
    exact (R((p)_*⟦Λ'⟧).map_isZero hZ).of_iso
      ((φY.leftDerivedFunctorIsoMapDerivedCategory.app _).symm ≪≫
        asIso ((derivedPushHom a p).app ((t.truncGE 1).obj K₀)))
  -- `G` sends `τ^{< 1} K₀` into degrees `≤ d`
  have hLT : (G.obj ((t.truncLT 1).obj K₀)).IsLE d := by
    have := isLE_rightDerivedLowerStar_truncLT_of_boundedConstructible p d hd K₀ hK₀
    exact φY.isLE_mapDerivedCategory_obj _ d
  have hT := G.map_distinguished _ (t.triangleLTGE_distinguished 1 K₀)
  have hK : t.IsLE (φY.mapDerivedCategory.obj (R((p)_*⟦Λ⟧).obj K₀)) d :=
    t.isLE₂ _ hT d hLT (by
      have : t.IsLE (G.obj ((t.truncGE 1).obj K₀)) d := t.isLE_of_isZero hGE d
      exact this)
  have := hpush K₀ _ (hK₀.1.1.choose_spec)
  exact t.isLE_of_iso ((φY.leftDerivedFunctorIsoMapDerivedCategory.app _).symm ≪≫
    asIso ((derivedPushHom a p).app K₀) ≪≫ R((p)_*⟦Λ'⟧).mapIso e) d

end AlgebraicGeometry.ProEtale.CondensedRing
