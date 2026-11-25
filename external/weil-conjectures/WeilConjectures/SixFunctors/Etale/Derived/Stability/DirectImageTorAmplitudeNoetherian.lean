/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.DirectImageTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImageAmplitudeTorsion
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.TorAmplitudeFiniteConstant

/-!
# The direct image of a complex of finite Tor amplitude, Noetherian coefficients

Let `k` be a field, `f : X ⟶ Y` a morphism of `k`-schemes of finite type with `dim X ≤ d`, and
`Λ` a Noetherian ring. If `K ∈ D(X_ét, Λ)` has Tor amplitude in `[a, b]` and is killed by a
nonzero integer `N`, then `Rf_* K` has Tor amplitude in `[a, b + 2d]`
(`AlgebraicGeometry.Etale.torAmplitudeIn_rightDerivedLowerStar_of_nsmul_id_eq_zero`). This is the
case of blueprint `sk-thm-sf-direct-image-tor-amplitude` used at the integral coefficient stage.

The proof follows the one for finite coefficients
(`AlgebraicGeometry.Etale.torAmplitudeIn_rightDerivedLowerStar_of_finite`), with two changes:

* the bound `Rf_* D^{≤ n} ⊆ D^{≤ n + 2d}` is only available for bounded complexes killed by `N`
  (`AlgebraicGeometry.Etale.isLE_rightDerivedLowerStar_obj_of_nsmul_id_eq_zero`); the complexes
  `K ⊗ᴸ M_X` met in the way-out argument proving the projection formula for a finitely generated
  `M` (blueprint `proposition-open-direct-image-preserves-finite--1`) are of this kind, by the Tor
  amplitude of `K`;
* the residue test is replaced by the test on finitely generated constant sheaves
  (`AlgebraicGeometry.Etale.torAmplitudeIn_of_forall_finite_constantSheaf`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

/-- The derived tensor product `K ⊗ᴸ M` is killed by every integer killing `K`. -/
lemma nsmul_id_derivedTensor_obj_obj_eq_zero (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {X : Scheme.{u}} (K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) {N : ℕ}
    (hK : N • 𝟙 K = 0) : N • 𝟙 (((-⊗ᴸ-(X)[A]).obj K).obj M) = 0 := by
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory (Sheaf X.smallEtaleTopology A)
  have h : N • 𝟙 (((-⊗ᴸ-(X)[A]).obj M).obj K) = 0 := by
    rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul, hK, Functor.map_zero]
  have e : ((-⊗ᴸ-(X)[A]).obj M).obj K ≅ ((-⊗ᴸ-(X)[A]).obj K).obj M := β_ M K
  have : N • 𝟙 (((-⊗ᴸ-(X)[A]).obj K).obj M) = e.inv ≫ (N • 𝟙 _) ≫ e.hom := by simp
  rw [this, h, zero_comp, comp_zero]

variable (Λ : Type (u + 1)) [CommRing Λ] {k : Type u} [Field k] {X Y : Scheme.{u}}
  (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
  [LocallyOfFiniteType aY] [QuasiCompact aY] (f : X ⟶ Y) (hf : f ≫ aY = aX) (d : ℕ)
  (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))

include hf hd in
/-- Blueprint `proposition-open-direct-image-preserves-finite--1`: The projection formula with a
finitely presented constant coefficient, for Noetherian coefficients and complexes killed by an
integer.

Let `f : X ⟶ Y` be a morphism of `k`-schemes of finite type with `dim X ≤ d`, `Λ` a Noetherian
ring, `K ∈ D(X_ét, Λ)` of Tor amplitude in `[a, b]` and killed by a nonzero integer `N`, and `M`
a finitely generated `Λ`-module. Then the projection map `Rf_* K ⊗ᴸ M_Y ⟶ Rf_*(K ⊗ᴸ Lf^* M_Y)` is
an isomorphism. The proof is the way-out argument of
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_app_app_constantSingle`: both
sides vanish above `b + 2d`, as `K` and the `K ⊗ᴸ M'_X` are bounded and killed by `N`
(`AlgebraicGeometry.Etale.isLE_rightDerivedLowerStar_obj_of_nsmul_id_eq_zero`). -/
theorem isIso_rightDerivedLowerStarProjectionMap_app_app_constantSingle_of_nsmul_id_eq_zero
    [IsNoetherianRing Λ] {a b : ℤ}
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (N : ℕ)
    [NeZero N] (hN : N • 𝟙 K = 0) (hta : torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K)
    (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M] :
    IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) f).app K).app
      (constantSingle (ModuleCat.{u + 1} Λ) Y M)) := by
  obtain ⟨hKa, hKb⟩ := _root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn hta
  refine _root_.DerivedCategory.isIso_app_of_exists_distTriang
    (rightDerivedLowerStarProjectionMapApp Λ f K)
    (fun Z ↦ ∃ (M : ModuleCat.{u + 1} Λ) (_ : Module.Finite Λ M),
      Z = constantSingle (ModuleCat.{u + 1} Λ) Y M)
    (b + 2 * d) ?_ ?_ _ ⟨M, inferInstance, rfl⟩
  · rintro _ ⟨M, _, rfl⟩
    have : (R((f)_*[ModuleCat.{u + 1} Λ]).obj K).IsLE (b + 2 * d) :=
      isLE_rightDerivedLowerStar_obj_of_nsmul_id_eq_zero Λ aX aY f hf d hd K ⟨⟨a, hKa⟩, ⟨b, hKb⟩⟩
        N hN b
    have hM : (L((f)^*[ModuleCat.{u + 1} Λ]).obj
        (constantSingle (ModuleCat.{u + 1} Λ) Y M)).IsLE 0 :=
      _root_.DerivedCategory.TStructure.t.isLE_of_iso
        (leftDerivedUpperStarSingleConstantSheafIso _ f M).symm 0
    have h₁ := isLE_derivedTensor_obj (ModuleCat.{u + 1} Λ) Y
      (R((f)_*[ModuleCat.{u + 1} Λ]).obj K) (constantSingle (ModuleCat.{u + 1} Λ) Y M)
      (b + 2 * d) 0
    rw [add_zero] at h₁
    -- `K ⊗ᴸ Lf^* M_Y ≅ K ⊗ᴸ M_X` has homology in `[a, b]` and is killed by `N`
    have h₂ := (_root_.DerivedCategory.homologyConcentratedIn a b).prop_of_iso
      (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).mapIso
        (leftDerivedUpperStarSingleConstantSheafIso _ f M).symm)
      ((torAmplitudeIn_iff_forall_derivedTensor _ X a b K).1 hta
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))
    obtain ⟨h₂a, h₂b⟩ := h₂
    exact ⟨h₁, isLE_rightDerivedLowerStar_obj_of_nsmul_id_eq_zero Λ aX aY f hf d hd _
      ⟨⟨a, h₂a⟩, ⟨b, h₂b⟩⟩ N (nsmul_id_derivedTensor_obj_obj_eq_zero _ K _ hN) b⟩
  · rintro _ ⟨M, _, rfl⟩
    obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' Λ M
    let S := ModuleCat.shortComplexOfCompEqZero (LinearMap.ker p).subtype p (by ext; simp)
    have hS : S.ShortExact :=
      ModuleCat.shortComplex_shortExact S p.exact_subtype_ker_map Subtype.val_injective hp
    exact ⟨_, (hS.map_of_exact
      (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))).singleTriangle_distinguished,
      rfl, ⟨ModuleCat.of Λ (LinearMap.ker p), inferInstance, rfl⟩,
      isIso_rightDerivedLowerStarProjectionMapApp_constantSingle_pi Λ f K n⟩

include hf hd in
/-- Blueprint `sk-thm-sf-direct-image-tor-amplitude`: Direct image with finite Tor amplitude,
for Noetherian coefficients.

Let `f : X ⟶ Y` be a morphism of `k`-schemes of finite type with `dim X ≤ d`, `Λ` a Noetherian
ring and `K ∈ D(X_ét, Λ)` of Tor amplitude in `[a, b]`, killed by a nonzero integer `N`. Then
`Rf_* K` has Tor amplitude in `[a, b + 2d]`. For a finitely generated `Λ`-module `M`, the
projection formula
(`isIso_rightDerivedLowerStarProjectionMap_app_app_constantSingle_of_nsmul_id_eq_zero`)
gives `Rf_* K ⊗ᴸ M_Y ≅ Rf_*(K ⊗ᴸ M_X)`, which has homology in `[a, b + 2d]`; and Tor amplitude
is tested on finitely generated constant sheaves
(`AlgebraicGeometry.Etale.torAmplitudeIn_of_forall_finite_constantSheaf`). -/
theorem torAmplitudeIn_rightDerivedLowerStar_of_nsmul_id_eq_zero [IsNoetherianRing Λ] (a b : ℤ)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (N : ℕ)
    [NeZero N] (hN : N • 𝟙 K = 0) (hta : torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K) :
    torAmplitudeIn (ModuleCat.{u + 1} Λ) Y a (b + 2 * (d : ℤ))
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K) := by
  refine torAmplitudeIn_of_forall_finite_constantSheaf _ fun M _ ↦ ?_
  have := isIso_rightDerivedLowerStarProjectionMap_app_app_constantSingle_of_nsmul_id_eq_zero Λ aX
    aY f hf d hd K N hN hta M
  refine tensorSingleConcentratedIn_rightDerivedLowerStar_of_isIso _ f K M ?_
  obtain ⟨h₁, h₂⟩ := (torAmplitudeIn_iff_forall_derivedTensor _ X a b K).1 hta
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)
  exact ⟨@isGE_rightDerivedLowerStar_obj Λ _ X Y f _ a h₁,
    isLE_rightDerivedLowerStar_obj_of_nsmul_id_eq_zero Λ aX aY f hf d hd _ ⟨⟨a, h₁⟩, ⟨b, h₂⟩⟩ N
      (nsmul_id_derivedTensor_obj_obj_eq_zero _ K _ hN) b⟩

end Etale

end AlgebraicGeometry
