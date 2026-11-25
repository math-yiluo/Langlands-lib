/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperFactor.KunnethMapAgrees
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence

/-!
# The factors of the Künneth map over a field

Let `k` be a field, `Λ` a finite ring whose exponent is invertible in `k`, and
`X`, `Y` schemes of finite type over `k`, with `W = X ×_k Y` and projections `p₁ : W ⟶ X`,
`p₂ : W ⟶ Y`. The Künneth map is a composite of three canonical maps
(`AlgebraicGeometry.Etale.kunnethMap_eq_of_isPullback`). This file shows that each of them is an
isomorphism, for unbounded complexes:

* generic base change: the derived base change map `La_Y^* Ra_{X*} F ⟶ Rp₂_* Lp₁^* F` is an
  isomorphism (`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_of_field`);
* the relative projection formula: the projection map
  `Rp₂_*(Lp₁^* F) ⊗ᴸ M ⟶ Rp₂_*(Lp₁^* F ⊗ᴸ Lp₂^* M)` is an isomorphism
  (`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_leftDerivedUpperStar`);
* over a separably closed field, the projection formula over the point, which is the instance
  `AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_app_app`.

Both statements follow from the base change theorem for a pushforward tensored with a complex
(`AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap`) and its decomposition
(`AlgebraicGeometry.Etale.tensorBaseChangeMap_eq_projectionMap`): the base change map
`M ⊗ᴸ La_Y^* Ra_{X*} F ⟶ Rp₂_*(Lp₂^* M ⊗ᴸ Lp₁^* F)` is `M ⊗ᴸ` the derived base change map
followed by the projection map of `p₂`. At `M = 𝟙` the projection map is an isomorphism, which
gives generic base change, and then the projection formula follows by two-out-of-three.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k]
  [HasInvertibleExponent Λ (Spec (.of k))] {X Y W : Scheme.{u}}
  (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
  [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]

/-- For `W = X ×_k Y` over a field `k`, the base change map for a pushforward
tensored with a complex `M ⊗ᴸ La_Y^* Ra_{X*} F ⟶ Rp₂_*(Lp₂^* M ⊗ᴸ Lp₁^* F)`
(`AlgebraicGeometry.Etale.tensorBaseChangeMap`) is an isomorphism for all `M ∈ D(Y_ét, Λ)` and
`F ∈ D(X_ét, Λ)`, unbounded: `AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap` for the
diagram `Y = Y ⟵ W`, `Spec k = Spec k ⟵ X`. -/
theorem isIso_tensorBaseChangeMap_of_field (p₁ : W ⟶ X) (p₂ : W ⟶ Y)
    (sq : IsPullback p₁ p₂ aX aY)
    (M : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (F : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (tensorBaseChangeMap (ModuleCat.{u + 1} Λ) p₂ p₁ aY aX sq.flip.w M F) := by
  have h := isIso_tensorBaseChangeMap Λ aY (𝟙 _) aX (𝟙 Y) aY p₂ p₁ aX (Category.comp_id _)
    (IsPullback.of_horiz_isIso (by simp)) sq.flip M F
  -- remove `L(𝟙)^*` using the identification `L(𝟙)^* ≅ 𝟭`
  let ι := (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) Y).app M
  have hn := tensorBaseChangeMap_naturality (ModuleCat.{u + 1} Λ) p₂ p₁ aY aX sq.flip.w ι.hom
    (𝟙 F)
  have := IsIso.of_isIso_fac_left hn
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ ((-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ].obj M).map
    (L((aY)^*[ModuleCat.{u + 1} Λ]).map (R((aX)_*[ModuleCat.{u + 1} Λ]).map (𝟙 F)))) _ _ this

/-- Generic base change over a field: for `W = X ×_k Y` with `X`, `Y` of finite
type over a field `k`, the derived base change map
`La_Y^* Ra_{X*} F ⟶ Rp₂_* Lp₁^* F` (`AlgebraicGeometry.Etale.derivedBaseChangeMap`) is an
isomorphism for all `F ∈ D(X_ét, Λ)`, unbounded. It is the base change map of
`AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap_of_field` at `M = 𝟙`, up to the
projection map of `p₂` at the unit, which is an isomorphism. -/
theorem isIso_derivedBaseChangeMap_of_field (p₁ : W ⟶ X) (p₂ : W ⟶ Y)
    (sq : IsPullback p₁ p₂ aX aY)
    (F : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) (CommSq.mk sq.w)).app F) := by
  have h := isIso_tensorBaseChangeMap_of_field Λ aX aY p₁ p₂ sq (𝟙_ _) F
  rw [tensorBaseChangeMap_eq_projectionMap] at h
  have := isIso_rightDerivedLowerStarProjectionMap_app_app_tensorUnit (ModuleCat.{u + 1} Λ) p₂
    ((L((p₁)^*[ModuleCat.{u + 1} Λ])).obj F)
  have := @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ _ h
  simp only [derivedTensor, curriedTensor_obj_map] at this
  rw [(Iso.eq_inv_comp _).2 (leftUnitor_naturality ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ)
    (CommSq.mk sq.w)).app F)).symm]
  infer_instance

/-- The relative projection formula over a field: for `W = X ×_k Y` with `X`,
`Y` of finite type over a field `k`, the projection map
`Rp₂_*(Lp₁^* F) ⊗ᴸ M ⟶ Rp₂_*(Lp₁^* F ⊗ᴸ Lp₂^* M)`
(`AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap`) is an isomorphism for all
`F ∈ D(X_ét, Λ)` and `M ∈ D(Y_ét, Λ)`, unbounded. By
`AlgebraicGeometry.Etale.tensorBaseChangeMap_eq_projectionMap`, the base change map of
`AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap_of_field` is this projection map
composed with `M ⊗ᴸ` the derived base change map, an isomorphism by
`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_of_field`, and symmetries. -/
theorem isIso_rightDerivedLowerStarProjectionMap_leftDerivedUpperStar (p₁ : W ⟶ X)
    (p₂ : W ⟶ Y) (sq : IsPullback p₁ p₂ aX aY)
    (F : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (M : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) p₂).app
      ((L((p₁)^*[ModuleCat.{u + 1} Λ])).obj F)).app M) := by
  have h := isIso_tensorBaseChangeMap_of_field Λ aX aY p₁ p₂ sq M F
  rw [tensorBaseChangeMap_eq_projectionMap] at h
  have := isIso_derivedBaseChangeMap_of_field Λ aX aY p₁ p₂ sq F
  have h₁ := @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ _ h
  have := @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ _ h₁
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ _ this

end Etale

end AlgebraicGeometry
