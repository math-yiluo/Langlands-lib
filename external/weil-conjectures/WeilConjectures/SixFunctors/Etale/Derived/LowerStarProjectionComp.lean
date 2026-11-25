/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comp

/-!
# The projection map of the derived pushforward along a composite

For `g₁₂ = g₁ ≫ g₂`, the projection map `Rg₁₂_*M ⊗ᴸ L ⟶ Rg₁₂_*(M ⊗ᴸ Lg₁₂^*L)`
(`AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap`) is the composite of the projection
maps of `Rg₂_*` and `Rg₁_*`, read through the composition isomorphism `Rg₁_* ⋙ Rg₂_* ⟶ Rg₁₂_*`
conjugate to `AlgebraicGeometry.Etale.leftDerivedUpperStarComp`
(`AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap_comp`).
-/

@[expose] public section

universe u' u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]

namespace Etale

variable {T S R : Scheme.{u}} (g₁ : T ⟶ S) (g₂ : S ⟶ R) (g₁₂ : T ⟶ R) (hg : g₁₂ = g₁ ≫ g₂)

/-- The naturality of the projection map `Rg_*M ⊗ᴸ L ⟶ Rg_*(M ⊗ᴸ Lg^*L)` in `M`. -/
@[reassoc]
lemma rightDerivedLowerStarProjectionMap_naturality_left {X Y : Scheme.{u}} (g : X ⟶ Y)
    {M M' : DerivedCategory (Sheaf X.smallEtaleTopology A)} (x : M ⟶ M')
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ((-⊗ᴸ-(Y)[A]).map (R((g)_*[A]).map x)).app L ≫
        ((rightDerivedLowerStarProjectionMap A g).app M').app L =
      ((rightDerivedLowerStarProjectionMap A g).app M).app L ≫
        R((g)_*[A]).map (((-⊗ᴸ-(X)[A]).map x).app (L((g)^*[A]).obj L)) :=
  NatTrans.congr_app ((rightDerivedLowerStarProjectionMap A g).naturality x) L

/-- The composition isomorphism `Rg₁_* ⋙ Rg₂_* ⟶ Rg₁₂_*` of the derived pushforwards, conjugate
to `AlgebraicGeometry.Etale.leftDerivedUpperStarComp` under the adjunctions `Lg^* ⊣ Rg_*`. -/
noncomputable abbrev rightDerivedLowerStarCompHom :
    R((g₁)_*[A]) ⋙ R((g₂)_*[A]) ⟶ R((g₁₂)_*[A]) :=
  conjugateEquiv ((derivedUpperStarLowerStarAdjunction A g₂).comp
      (derivedUpperStarLowerStarAdjunction A g₁)) (derivedUpperStarLowerStarAdjunction A g₁₂)
    (leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).hom

/-- **The projection map of a composite**: for `g₁₂ = g₁ ≫ g₂`, the square
```
Rg₂_*Rg₁_*M ⊗ᴸ L ──π₂, Rg₂_* π₁──▶ Rg₂_*Rg₁_*(M ⊗ᴸ Lg₁^*Lg₂^*L)
        │                                       │
        ▼                                       ▼
 Rg₁₂_*M ⊗ᴸ L ──π₁₂──▶ Rg₁₂_*(M ⊗ᴸ Lg₁₂^*L) ──▶ Rg₁₂_*(M ⊗ᴸ Lg₁^*Lg₂^*L)
```
commutes, with vertical arrows the composition map `rightDerivedLowerStarCompHom`. -/
lemma rightDerivedLowerStarProjectionMap_comp
    (M : DerivedCategory (Sheaf T.smallEtaleTopology A))
    (L : DerivedCategory (Sheaf R.smallEtaleTopology A)) :
    ((-⊗ᴸ-(R)[A]).map ((rightDerivedLowerStarCompHom A g₁ g₂ g₁₂ hg).app M)).app L ≫
        ((rightDerivedLowerStarProjectionMap A g₁₂).app M).app L ≫
        R((g₁₂)_*[A]).map (((-⊗ᴸ-(T)[A]).obj M).map
          ((leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).hom.app L)) =
      ((rightDerivedLowerStarProjectionMap A g₂).app (R((g₁)_*[A]).obj M)).app L ≫
        R((g₂)_*[A]).map (((rightDerivedLowerStarProjectionMap A g₁).app M).app
          (L((g₂)^*[A]).obj L)) ≫
        (rightDerivedLowerStarCompHom A g₁ g₂ g₁₂ hg).app
          (((-⊗ᴸ-(T)[A]).obj M).obj (L((g₁)^*[A]).obj (L((g₂)^*[A]).obj L))) := by
  let φ := (Functor.postcompose₂.obj L((g₁)^*[A])).map
    (leftDerivedUpperStarTensorComparison A g₂) ≫
    (((Functor.whiskeringLeft₂ _).obj L((g₂)^*[A])).obj L((g₂)^*[A])).map
      (leftDerivedUpperStarTensorComparison A g₁)
  have h := Adjunction.rightAdjointProjectionMap_conjugate (T_D := -⊗ᴸ-(R)[A]) (T_C := -⊗ᴸ-(T)[A])
    ((derivedUpperStarLowerStarAdjunction A g₂).comp (derivedUpperStarLowerStarAdjunction A g₁))
    φ (derivedUpperStarLowerStarAdjunction A g₁₂) (leftDerivedUpperStarTensorComparison A g₁₂)
    (leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).hom (fun a b ↦ by
      have := leftDerivedUpperStarTensorComparison_comp A g₁ g₂ g₁₂ hg a b
      rw [tensorHom_def] at this
      exact this.symm) M L
  rw [Adjunction.rightAdjointProjectionMap_comp (derivedUpperStarLowerStarAdjunction A g₂)
    (derivedUpperStarLowerStarAdjunction A g₁) (leftDerivedUpperStarTensorComparison A g₂)
    (leftDerivedUpperStarTensorComparison A g₁) _ (fun _ _ ↦ rfl)] at h
  unfold rightDerivedLowerStarProjectionMap
  rw [Category.assoc] at h
  convert h using 2
  all_goals rfl


/-- The form of `rightDerivedLowerStarProjectionMap_comp` computing `(β ⊗ 1) ≫ π₁₂`. -/
@[reassoc]
lemma rightDerivedLowerStarProjectionMap_comp'
    (M : DerivedCategory (Sheaf T.smallEtaleTopology A))
    (L : DerivedCategory (Sheaf R.smallEtaleTopology A)) :
    ((-⊗ᴸ-(R)[A]).map ((rightDerivedLowerStarCompHom A g₁ g₂ g₁₂ hg).app M)).app L ≫
        ((rightDerivedLowerStarProjectionMap A g₁₂).app M).app L =
      ((rightDerivedLowerStarProjectionMap A g₂).app (R((g₁)_*[A]).obj M)).app L ≫
        R((g₂)_*[A]).map (((rightDerivedLowerStarProjectionMap A g₁).app M).app
          (L((g₂)^*[A]).obj L)) ≫
        (rightDerivedLowerStarCompHom A g₁ g₂ g₁₂ hg).app
          (((-⊗ᴸ-(T)[A]).obj M).obj (L((g₁)^*[A]).obj (L((g₂)^*[A]).obj L))) ≫
        R((g₁₂)_*[A]).map (((-⊗ᴸ-(T)[A]).obj M).map
          ((leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).inv.app L)) := by
  rw [← reassoc_of% (rightDerivedLowerStarProjectionMap_comp A g₁ g₂ g₁₂ hg M L),
    ← Functor.map_comp, ← Functor.map_comp, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.comp_id]
end Etale

end AlgebraicGeometry
