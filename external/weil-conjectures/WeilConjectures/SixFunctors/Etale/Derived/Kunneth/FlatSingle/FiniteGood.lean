/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FlatSingle.Pasting
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperFactor.ExchangeCompat
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper

/-!
# The base change map for a pushforward tensored with a finite pushforward of the unit

For a commutative square `h ≫ f' = e ≫ g` and a finite morphism `π' : X'ᵢ ⟶ X'` with base change
`ρ : Yᵢ ⟶ Y` along `h`, the base change map (`AlgebraicGeometry.Etale.tensorBaseChangeMap`)

`Rπ'_* Λ ⊗ᴸ Lf'^* Rg_* F ⟶ Rh_* (Lh^* Rπ'_* Λ ⊗ᴸ Le^* F)`

is an isomorphism as soon as the derived base change maps `Lf'^* Rg_* F ⟶ Rh_* Le^* F` and
`Lπ'^* Rh_* Le^* F ⟶ Rhᵢ_* Lρ^* Le^* F` are
(`AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap_rightDerivedLowerStar_unit`). This is the
computation of the finite pushforwards `πᵢ_* Λ` in the proof of blueprint
`lemma-kunneth-field-coefficients--1`: the projection formula and the base change theorem for the
finite morphisms `π'` and `ρ` reduce it to the base change theorem along `X'ᵢ ⟶ S'`.

The proof compares the base change map with the Künneth maps over `X'`: by pasting with a
degenerate square (`AlgebraicGeometry.Etale.tensorBaseChangeMap_paste`) it becomes the base
change map of the square `(h, 𝟙, 𝟙, h)`, which is the Künneth map of `(X', Y)` over `X'`
(`AlgebraicGeometry.Etale.kunnethMap_eq`); the Künneth maps of `(X', Y)` at `Rπ'_* Λ` and of
`(X'ᵢ, Y)` at `Λ` are compatible with the exchange map of `π'`
(`AlgebraicGeometry.Etale.kunnethMap_derivedBaseChangeMap`), and the latter Künneth map is the
base change map at the unit of the square `(hᵢ, ρ, π', h)`
(`AlgebraicGeometry.Etale.tensorBaseChangeMap_tensorUnit`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

omit [Finite Λ] in
/-- The invertibility of the base change map does not depend on the way the horizontal maps are
written. -/
lemma isIso_tensorBaseChangeMap_congr {X' S' T Y : Scheme.{u}} (h : Y ⟶ X') {e e₀ : Y ⟶ T}
    {f' f₀ : X' ⟶ S'} (g : T ⟶ S') (he : e₀ = e) (hf : f₀ = f') (w : h ≫ f' = e ≫ g)
    (w₀ : h ≫ f₀ = e₀ ≫ g)
    (M : DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (F : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (tensorBaseChangeMap (ModuleCat.{u + 1} Λ) h e₀ f₀ g w₀ M F) ↔
      IsIso (tensorBaseChangeMap (ModuleCat.{u + 1} Λ) h e f' g w M F) := by
  subst he hf
  rfl

omit [Finite Λ] in
/-- If the derived base change map `Lf'^* Rg_* F ⟶ Rh_* Le^* F` is an isomorphism, the base change
map `M ⊗ᴸ Lf'^* Rg_* F ⟶ Rh_* (Lh^* M ⊗ᴸ Le^* F)` is an isomorphism if and only if the base
change map of the degenerate square `(h, 𝟙, 𝟙, h)` at `(M, Le^* F)` is. -/
lemma isIso_tensorBaseChangeMap_iff_degenerate {X' S' T Y : Scheme.{u}} (h : Y ⟶ X')
    (e : Y ⟶ T) (f' : X' ⟶ S') (g : T ⟶ S') (w : h ≫ f' = e ≫ g)
    (M : DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (F : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hBC : IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) (CommSq.mk w.symm)).app F)) :
    IsIso (tensorBaseChangeMap (ModuleCat.{u + 1} Λ) h e f' g w M F) ↔
      IsIso (tensorBaseChangeMap (ModuleCat.{u + 1} Λ) h (𝟙 Y) (𝟙 X') h (by simp) M
        (L((e)^*[ModuleCat.{u + 1} Λ]).obj F)) := by
  have key := tensorBaseChangeMap_paste (ModuleCat.{u + 1} Λ) h (𝟙 Y) (𝟙 X') h (by simp) e f' g w
    (by simpa using w) M F
  rw [← isIso_tensorBaseChangeMap_congr Λ h g (Category.id_comp e) (Category.id_comp f') w
    (by simpa using w), ← isIso_comp_right_iff _ (R((h)_*[ModuleCat.{u + 1} Λ]).map
      (((-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).obj (L((h)^*[ModuleCat.{u + 1} Λ]).obj M)).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) (𝟙 Y) e).hom.app F))), key,
    isIso_comp_left_iff]

/-- The base change map of the degenerate square `(h, 𝟙, 𝟙, h)` is an isomorphism if and only if
the Künneth map of `(X', Y)` over `X'` is: they differ by the projection map of the identity and
the derived pushforward along the identity. -/
lemma isIso_tensorBaseChangeMap_degenerate_iff_kunnethMap {X' Y : Scheme.{u}} (h : Y ⟶ X')
    (M : DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (tensorBaseChangeMap (ModuleCat.{u + 1} Λ) h (𝟙 Y) (𝟙 X') h (by simp) M K) ↔
      IsIso (kunnethMap (ModuleCat.{u + 1} Λ) h (𝟙 Y) (𝟙 X') h h (by simp) (by simp) M K) := by
  have := isIso_rightDerivedLowerStarProjectionMap_of_isProper Λ isAddTorsion_of_finite (𝟙 X')
  rw [kunnethMap_eq, isIso_comp_left_iff, isIso_comp_right_iff,
    NatIso.isIso_map_iff (rightDerivedLowerStarIdIso Λ X')]
  exact Iff.rfl

-- the derived-category computation unfolds large terms
/-- The Künneth map `Rπ'_* Λ ⊗ᴸ Rh_* K ⟶ Rc_* (Lhᵢ^* Λ ⊗ᴸ Lρ^* K)` of a commutative square
`hᵢ ≫ π' = ρ ≫ h = c` with `π'` proper is an isomorphism if the derived base change map
`Lπ'^* Rh_* K ⟶ Rhᵢ_* Lρ^* K` is. -/
lemma isIso_kunnethMap_tensorUnit {X' Y X'ᵢ Yᵢ : Scheme.{u}} (h : Y ⟶ X') (π' : X'ᵢ ⟶ X')
    [IsProper π'] (hᵢ : Yᵢ ⟶ X'ᵢ) (ρ : Yᵢ ⟶ Y) (w : hᵢ ≫ π' = ρ ≫ h)
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hBC : IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) (CommSq.mk w.symm)).app K)) :
    IsIso (kunnethMap (ModuleCat.{u + 1} Λ) hᵢ ρ π' h (ρ ≫ h) w rfl (𝟙_ _) K) := by
  have := isIso_rightDerivedLowerStarProjectionMap_of_isProper Λ isAddTorsion_of_finite π'
  have := isIso_tensorBaseChangeMap_tensorUnit (ModuleCat.{u + 1} Λ) hᵢ ρ π' h w K hBC
  rw [kunnethMap_eq]
  infer_instance

/-- For a finite `π' : X'ᵢ ⟶ X'` with base change `ρ : Yᵢ ⟶ Y` along `h : Y ⟶ X'`, the Künneth map
of `(X', Y)` over `X'` at `Rπ'_* Λ` is an isomorphism if the Künneth map of `(X'ᵢ, Y)` over `X'`
at `Λ` is (`AlgebraicGeometry.Etale.kunnethMap_derivedBaseChangeMap`). -/
lemma isIso_kunnethMap_rightDerivedLowerStar_unit {X' Y X'ᵢ Yᵢ : Scheme.{u}} (h : Y ⟶ X')
    (π' : X'ᵢ ⟶ X') [IsFinite π'] (hᵢ : Yᵢ ⟶ X'ᵢ) (ρ : Yᵢ ⟶ Y) (sq : IsPullback hᵢ ρ π' h)
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hU : IsIso (kunnethMap (ModuleCat.{u + 1} Λ) hᵢ ρ π' h (ρ ≫ h) sq.w rfl (𝟙_ _) K)) :
    IsIso (kunnethMap (ModuleCat.{u + 1} Λ) h (𝟙 Y) (𝟙 X') h h (by simp) (by simp)
      (R((π')_*[ModuleCat.{u + 1} Λ]).obj (𝟙_ _)) K) := by
  have hΛ : IsAddTorsion Λ := isAddTorsion_of_finite
  have : IsFinite ρ := MorphismProperty.of_isPullback sq inferInstance
  have := isIso_rightDerivedLowerStarProjectionMap_of_isProper Λ hΛ ρ
  have := isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring Λ hΛ sq
  have key := kunnethMap_derivedBaseChangeMap (ModuleCat.{u + 1} Λ) (𝟙 X') h π' h (𝟙 Y) h
    (by simp) (by simp) π' (by simp) hᵢ ρ sq.toCommSq ρ (by simp) (ρ ≫ h) rfl sq.w rfl (𝟙_ _) K
  have hL : IsIso (kunnethMap (ModuleCat.{u + 1} Λ) h (𝟙 Y) (𝟙 X') h h (by simp) (by simp)
      (R((π')_*[ModuleCat.{u + 1} Λ]).obj (𝟙_ _)) K ≫
      R((h)_*[ModuleCat.{u + 1} Λ]).map
          (((-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).map ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
            sq.toCommSq).app (𝟙_ _))).app (L((𝟙 Y)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
            ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) ρ).app _).app _) ≫
        (rightDerivedLowerStarCompIsoOfComp (ModuleCat.{u + 1} Λ) ρ h (ρ ≫ h) rfl).hom.app _ ≫
        R((ρ ≫ h)_*[ModuleCat.{u + 1} Λ]).map
          (((-⊗ᴸ-(Yᵢ)[ModuleCat.{u + 1} Λ]).obj _).map
            ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) ρ (𝟙 Y) ρ (by simp)).inv.app K))) := by
    rw [← key]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp hL

/-- **Finite pushforwards of the unit.** For a commutative square `h ≫ f' = e ≫ g` and a finite
morphism `π' : X'ᵢ ⟶ X'` with base change `ρ : Yᵢ ⟶ Y` along `h`, the base change map
`Rπ'_* Λ ⊗ᴸ Lf'^* Rg_* F ⟶ Rh_* (Lh^* Rπ'_* Λ ⊗ᴸ Le^* F)` is an isomorphism as soon as the derived
base change maps `Lf'^* Rg_* F ⟶ Rh_* Le^* F` and `Lπ'^* Rh_* Le^* F ⟶ Rhᵢ_* Lρ^* Le^* F` are. -/
theorem isIso_tensorBaseChangeMap_rightDerivedLowerStar_unit {X' S' T Y X'ᵢ Yᵢ : Scheme.{u}}
    (h : Y ⟶ X') (e : Y ⟶ T) (f' : X' ⟶ S') (g : T ⟶ S') (w : h ≫ f' = e ≫ g)
    (π' : X'ᵢ ⟶ X') [IsFinite π'] (hᵢ : Yᵢ ⟶ X'ᵢ) (ρ : Yᵢ ⟶ Y) (sq : IsPullback hᵢ ρ π' h)
    (F : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hBC : IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) (CommSq.mk w.symm)).app F))
    (hBCᵢ : IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) (CommSq.mk sq.w.symm)).app
      (L((e)^*[ModuleCat.{u + 1} Λ]).obj F))) :
    IsIso (tensorBaseChangeMap (ModuleCat.{u + 1} Λ) h e f' g w
      (R((π')_*[ModuleCat.{u + 1} Λ]).obj (𝟙_ _)) F) := by
  rw [isIso_tensorBaseChangeMap_iff_degenerate Λ h e f' g w _ F hBC,
    isIso_tensorBaseChangeMap_degenerate_iff_kunnethMap]
  exact isIso_kunnethMap_rightDerivedLowerStar_unit Λ h π' hᵢ ρ sq _
    (isIso_kunnethMap_tensorUnit Λ h π' hᵢ ρ sq.w _ hBCᵢ)

end Etale

end AlgebraicGeometry
