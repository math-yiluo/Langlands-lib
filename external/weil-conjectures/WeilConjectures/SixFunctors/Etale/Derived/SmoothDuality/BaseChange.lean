/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.Charts

/-!
# Base change for smooth duality reduces to the dualizing complex

The last step of the proof of blueprint `proposition-exceptional-inverse-image-smooth-morphism--6`:
the base change map of the exceptional inverse image respects the tensor isomorphisms of
`proposition-exceptional-inverse-image-smooth-morphism`. For a cartesian square

```
  X' --g'--> X
  |          |
  f'         f
  ↓          ↓
  Y' --g---> Y
```

with `f'` quasi-compact, the canonical base change map `β_K : Lg'^* Rf^! K ⟶ Rf'^! Lg^* K`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap`) is, through the tensor maps
`θ_f` and `θ_{f'}`, the base change map `β_Λ : Lg'^* ω_f ⟶ ω_{f'}` of the dualizing complexes
tensored with `Lg'^* Lf^* K ≅ Lf'^* Lg^* K`. Hence when the tensor maps are isomorphisms, `β` is
an isomorphism at every object as soon as it is one at `Λ_Y`.

## Main statements

- `CategoryTheory.Adjunction.isIso_mateEquiv_app_of_isIso_projectionTensorMap`
- `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_app_of_isIso_tensorMap`
- `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_forall_isIso`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace CategoryTheory.Adjunction

/-- **Base change at an object where the tensor maps are isomorphisms.** In the situation of
`CategoryTheory.Adjunction.projectionTensorMap_mateEquiv`, if the base change map `β` is an
isomorphism at `𝟙_`, and the tensor maps of `adj` at `(𝟙_, N)` and of `adj'` at
`(Gb 𝟙_, Gb N)` are isomorphisms, then `β` is an isomorphism at `N`: `β` at `𝟙_ ⊗ N` is, through
the tensor maps, `β` at `𝟙_` tensored with `κ N`. -/
theorem isIso_mateEquiv_app_of_isIso_projectionTensorMap
    {Cx Cy Cx' Cy' : Type*} [Category* Cx] [Category* Cy] [Category* Cx'] [Category* Cy']
    [MonoidalCategory Cx] [MonoidalCategory Cy] [MonoidalCategory Cx'] [MonoidalCategory Cy']
    {F : Cy ⥤ Cx} {L : Cx ⥤ Cy} {R : Cy ⥤ Cx} (adj : L ⊣ R)
    {F' : Cy' ⥤ Cx'} {L' : Cx' ⥤ Cy'} {R' : Cy' ⥤ Cx'} (adj' : L' ⊣ R')
    (π : ∀ (M : Cx) (N : Cy), L.obj M ⊗ N ⟶ L.obj (M ⊗ F.obj N)) [∀ M N, IsIso (π M N)]
    (π' : ∀ (M : Cx') (N : Cy'), L'.obj M ⊗ N ⟶ L'.obj (M ⊗ F'.obj N)) [∀ M N, IsIso (π' M N)]
    (hπ' : ∀ {M M' : Cx'} (φ : M ⟶ M') (N : Cy'),
      L'.map φ ▷ N ≫ π' M' N = π' M N ≫ L'.map (φ ▷ F'.obj N))
    {Ga : Cx ⥤ Cx'} {Gb : Cy ⥤ Cy'}
    (δa : ∀ M M' : Cx, Ga.obj (M ⊗ M') ⟶ Ga.obj M ⊗ Ga.obj M') [∀ M M', IsIso (δa M M')]
    (δb : ∀ N N' : Cy, Gb.obj (N ⊗ N') ⟶ Gb.obj N ⊗ Gb.obj N') [∀ N N', IsIso (δb N N')]
    (hδb : ∀ {N N' : Cy} (φ : N ⟶ N') (N'' : Cy),
      Gb.map (φ ▷ N'') ≫ δb N' N'' = δb N N'' ≫ Gb.map φ ▷ Gb.obj N'')
    (κ : ∀ N : Cy, Ga.obj (F.obj N) ⟶ F'.obj (Gb.obj N)) [∀ N, IsIso (κ N)]
    (Ex : L ⋙ Gb ⟶ Ga ⋙ L') [IsIso Ex] (ξ : TwoSquare Ga L L' Gb)
    (hExξ : ∀ M : Cx, Ex.app M ≫ ξ.app M = 𝟙 _)
    (hEx : ∀ (M : Cx) (N : Cy), Gb.map (π M N) ≫ Ex.app (M ⊗ F.obj N) ≫
      L'.map (δa M (F.obj N)) ≫ L'.map (Ga.obj M ◁ κ N) =
        δb (L.obj M) N ≫ Ex.app M ▷ Gb.obj N ≫ π' (Ga.obj M) (Gb.obj N))
    (h₁ : IsIso ((mateEquiv adj adj' ξ).app (𝟙_ Cy))) {N : Cy}
    (hT : IsIso (adj.projectionTensorMap π (𝟙_ _) N))
    (hT' : IsIso (adj'.projectionTensorMap π' (Gb.obj (𝟙_ _)) (Gb.obj N))) :
    IsIso ((mateEquiv adj adj' ξ).app N) := by
  have key := projectionTensorMap_mateEquiv adj adj' π π' hπ' δa δb hδb κ Ex ξ hExξ hEx (𝟙_ _) N
  have h₂ : IsIso (Ga.map (adj.projectionTensorMap π (𝟙_ _) N) ≫
      (mateEquiv adj adj' ξ).app (𝟙_ _ ⊗ N) ≫ R'.map (δb (𝟙_ _) N)) := by
    rw [key]
    infer_instance
  have := (isIso_comp_left_iff _ _).1 h₂
  have : IsIso ((mateEquiv adj adj' ξ).app (𝟙_ _ ⊗ N)) :=
    IsIso.of_isIso_comp_right _ (R'.map (δb (𝟙_ _) N))
  have hn := (mateEquiv adj adj' ξ).naturality (λ_ N).hom
  have h₄ : IsIso ((R ⋙ Ga).map (λ_ N).hom ≫ (mateEquiv adj adj' ξ).app N) := by
    rw [hn]
    infer_instance
  exact (isIso_comp_left_iff _ _).1 h₄

end CategoryTheory.Adjunction

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

-- Search the braiding of `ModuleCat Λ` through its symmetric structure, as in the generic
-- definitions of the derived tensor product.
attribute [local instance high] SymmetricCategory.toBraidedCategory

-- As in `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange`, whose
-- compatibility of the projection map with base change is used below: with the same instances,
-- its statement matches the one expected here syntactically.
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint ModuleCat.hasColimitsOfShape
  ModuleCat.hasColimitsOfSize

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
  (sq : IsPullback g' f' f g) [HasCompactification f] [HasCompactification f'] [QuasiCompact f']

/-- **Base change at an object where the tensor maps are isomorphisms.** For a cartesian square
`g' ≫ f = f' ≫ g` with quasi-compact `f'`, if the base change map `Lg'^* Rf^! ⟶ Rf'^! Lg^*` is an
isomorphism at `Λ_Y`, and the tensor maps of `f` at `(Λ_Y, N)` and of `f'` at
`(Lg^* Λ_Y, Lg^* N)` are isomorphisms, then the base change map is an isomorphism at `N`. -/
theorem isIso_rightDerivedUpperShriekBaseChangeMap_app_of_isIso_tensorMap
    (h₁ : IsIso ((rightDerivedUpperShriekBaseChangeMap Λ sq).app (𝟙_ _)))
    {N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hT : IsIso (rightDerivedUpperShriekTensorMap f (𝟙_ _) N))
    (hT' : IsIso (rightDerivedUpperShriekTensorMap f' ((L((g)^*[ModuleCat.{u + 1} Λ])).obj (𝟙_ _))
      ((L((g)^*[ModuleCat.{u + 1} Λ])).obj N))) :
    IsIso ((rightDerivedUpperShriekBaseChangeMap Λ sq).app N) := by
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  have hlib := projectionMap_rightDerivedLowerShriekBaseChangeMap Λ sq
  simp only [← leftDerivedUpperStarTensorIso_hom] at hlib
  have : ∀ N, IsIso (derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} Λ) sq.toCommSq N) :=
    fun N ↦ by
      unfold derivedSquareUpperStarIsoInvApp
      infer_instance
  exact Adjunction.isIso_mateEquiv_app_of_isIso_projectionTensorMap
    (rightDerivedUpperShriekAdjunction Λ f)
    (rightDerivedUpperShriekAdjunction Λ f')
    (fun M N ↦ ((projectionMap (ModuleCat.{u + 1} Λ) f).app M).app N)
    (fun M N ↦ ((projectionMap (ModuleCat.{u + 1} Λ) f').app M).app N)
    (projectionMap_app_app_naturality_left f')
    (fun M M' ↦ (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) g' M M').hom)
    (fun N N' ↦ (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) g N N').hom)
    (fun φ N'' ↦ leftDerivedUpperStarTensorIso_hom_naturality_left g φ N'')
    (fun N ↦ derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} Λ) sq.toCommSq N)
    (rightDerivedLowerShriekBaseChangeMap Λ sq) (inv (rightDerivedLowerShriekBaseChangeMap Λ sq))
    (fun M ↦ by simp [NatIso.isIso_inv_app]) hlib h₁ hT hT'

/-- **The base change map respects the tensor isomorphisms.** For a cartesian square
`g' ≫ f = f' ≫ g` with quasi-compact `f'` such that the canonical tensor maps of `f` and `f'` are
isomorphisms at every object, the base change map `Lg'^* Rf^! ⟶ Rf'^! Lg^*` is an isomorphism as
soon as it is one at `Λ_Y`, that is, as soon as `Lg'^* ω_f ⟶ ω_{f'}` is an isomorphism
(`AlgebraicGeometry.Etale.isIso_dualizingComplexBaseChangeMap_iff`). -/
theorem isIso_rightDerivedUpperShriekBaseChangeMap_of_forall_isIso
    (hθ : ∀ K, IsIso (dualizingComplexTensorMap Λ f K))
    (hθ' : ∀ K, IsIso (dualizingComplexTensorMap Λ f' K))
    (h₁ : IsIso ((rightDerivedUpperShriekBaseChangeMap Λ sq).app (𝟙_ _))) :
    IsIso (rightDerivedUpperShriekBaseChangeMap Λ sq) := by
  have (N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
      IsIso ((rightDerivedUpperShriekBaseChangeMap Λ sq).app N) :=
    isIso_rightDerivedUpperShriekBaseChangeMap_app_of_isIso_tensorMap sq h₁
      ((isIso_lowerShriekRightAdjointUnitTensorMap_iff (rightDerivedUpperShriekAdjunction Λ f) N).1
        (hθ N))
      (isIso_lowerShriekRightAdjointTensorMap_of_forall (rightDerivedUpperShriekAdjunction Λ f')
        (projectionMapAssociativity Λ f') hθ' _ _)
  exact NatIso.isIso_of_isIso_app _

end Etale

end AlgebraicGeometry
