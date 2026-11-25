/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comp

/-!
# The projection map of the derived pushforward commutes with base change

For a commutative square `g' ≫ f = f' ≫ g` of schemes, the projection map
`Rf_*K ⊗ᴸ L ⟶ Rf_*(K ⊗ᴸ Lf^*L)` (`AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap`)
commutes with the derived base change map `Ex_* : Lg^* Rf_* ⟶ Rf'_* Lg'^*`
(`AlgebraicGeometry.Etale.derivedBaseChangeMap`) and the tensor comparisons of the derived
pullbacks.

## Main results

- `AlgebraicGeometry.Etale.derivedSquareUpperStarIso_hom_tensor`: the isomorphism
  `Lg^* Lf'^* ≅ Lf^* Lg'^*` of a commutative square commutes with the tensor comparisons.
- `AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap_derivedBaseChangeMap`: the
  projection map commutes with `Ex_*`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]

namespace Etale

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The isomorphism `Lg^* ⋙ Lf'^* ≅ Lf^* ⋙ Lg'^*` of a commutative square `g' ≫ f = f' ≫ g`
commutes with the tensor comparisons of the derived pullbacks. -/
@[reassoc]
lemma derivedSquareUpperStarIso_hom_tensor (sq : CommSq g' f' f g)
    (a b : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    L((f')^*[A]).map (((leftDerivedUpperStarTensorComparison A g).app a).app b) ≫
        ((leftDerivedUpperStarTensorComparison A f').app _).app _ ≫
        ((derivedSquareUpperStarIso A sq).hom.app a ⊗ₘ
          (derivedSquareUpperStarIso A sq).hom.app b) =
      (derivedSquareUpperStarIso A sq).hom.app (a ⊗ b) ≫
        L((g')^*[A]).map (((leftDerivedUpperStarTensorComparison A f).app a).app b) ≫
        ((leftDerivedUpperStarTensorComparison A g').app _).app _ := by
  have h₁ := leftDerivedUpperStarTensorComparison_comp A f' g (g' ≫ f) sq.w a b
  have h₂ := leftDerivedUpperStarTensorComparison_comp A g' f (g' ≫ f) rfl a b
  dsimp only [derivedSquareUpperStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  have h₁' : L((f')^*[A]).map (((leftDerivedUpperStarTensorComparison A g).app a).app b) ≫
      ((leftDerivedUpperStarTensorComparison A f').app _).app _ =
      (leftDerivedUpperStarComp A f' g (g' ≫ f) sq.w).inv.app (a ⊗ b) ≫
        ((leftDerivedUpperStarTensorComparison A (g' ≫ f)).app a).app b ≫
        ((leftDerivedUpperStarComp A f' g (g' ≫ f) sq.w).hom.app a ⊗ₘ
          (leftDerivedUpperStarComp A f' g (g' ≫ f) sq.w).hom.app b) := by
    rw [h₁, Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% h₁', tensorHom_comp_tensorHom, Iso.hom_inv_id_app_assoc,
    Iso.hom_inv_id_app_assoc, h₂, Category.assoc]

/-- **The projection map commutes with base change**: for a commutative square
`g' ≫ f = f' ≫ g`, `K` in `D(X_ét)` and `L` in `D(Y_ét)`, the square
```
Lg^*(Rf_*K ⊗ᴸ L) ──Lg^* π──▶ Lg^*Rf_*(K ⊗ᴸ Lf^*L) ──Ex_*──▶ Rf'_*Lg'^*(K ⊗ᴸ Lf^*L)
       │                                                          │
       ▼                                                          ▼
Lg^*Rf_*K ⊗ᴸ Lg^*L ──Ex_* ⊗ 1──▶ Rf'_*Lg'^*K ⊗ᴸ Lg^*L ──π──▶ Rf'_*(Lg'^*K ⊗ᴸ Lg'^*Lf^*L)
```
commutes, where the vertical arrows are the tensor comparisons of the derived pullbacks and the
bottom row ends with `Lf'^*Lg^* ≅ Lg'^*Lf^*`. -/
lemma rightDerivedLowerStarProjectionMap_derivedBaseChangeMap (sq : CommSq g' f' f g)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    L((g)^*[A]).map (((rightDerivedLowerStarProjectionMap A f).app K).app L) ≫
        (derivedBaseChangeMap A sq).app (((-⊗ᴸ-(X)[A]).obj K).obj (L((f)^*[A]).obj L)) ≫
        R((f')_*[A]).map (((leftDerivedUpperStarTensorComparison A g').app K).app
          (L((f)^*[A]).obj L)) =
      ((leftDerivedUpperStarTensorComparison A g).app (R((f)_*[A]).obj K)).app L ≫
        ((-⊗ᴸ-(Y')[A]).map ((derivedBaseChangeMap A sq).app K)).app (L((g)^*[A]).obj L) ≫
        ((rightDerivedLowerStarProjectionMap A f').app (L((g')^*[A]).obj K)).app
          (L((g)^*[A]).obj L) ≫
        R((f')_*[A]).map (((-⊗ᴸ-(X')[A]).obj (L((g')^*[A]).obj K)).map
          ((derivedSquareUpperStarIso A sq).hom.app L)) :=
  Adjunction.rightAdjointProjectionMap_mate (derivedUpperStarLowerStarAdjunction A f)
    (derivedUpperStarLowerStarAdjunction A f') (leftDerivedUpperStarTensorComparison A f)
    (leftDerivedUpperStarTensorComparison A f') (leftDerivedUpperStarTensorComparison A g)
    (leftDerivedUpperStarTensorComparison A g') (derivedSquareUpperStarIso A sq).hom
    (derivedBaseChangeMap A sq)
    (fun a b ↦ by
      have := derivedSquareUpperStarIso_hom_tensor A sq a b
      rw [tensorHom_def] at this
      exact this)
    (derivedUpperStar_map_derivedBaseChangeMap_app_counit A sq) K L

end Etale

end AlgebraicGeometry
