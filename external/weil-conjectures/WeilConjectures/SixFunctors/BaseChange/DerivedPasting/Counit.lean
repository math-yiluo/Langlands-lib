/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Identity
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction

/-!
# The derived base change map of a degenerate square is the counit

For a morphism `f : X ⟶ Y`, the square

```
X --𝟙--> X
|        |
𝟙        f
v        v
X --f--> Y
```

commutes, and its derived base change map `f^* Rf_* ⟶ R(𝟙)_* (𝟙)^*` is the counit of
`f^* ⊣ Rf_*` followed by the unit of `(𝟙)^* ⊣ R(𝟙)_*`
(`AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_eq_counit_comp_unit`); modulo the identity
isomorphisms `(𝟙)^* ≅ 𝟭` and `R(𝟙)_* ≅ 𝟭` it is the counit
(`AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_app_comp_lowerStarIdDerivedPlus`).

The file also records the vertical pasting law
`AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_paste_vert_of_eq` for composites which are only
propositionally equal to the given diagonals.
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits

namespace AlgebraicGeometry

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

open Etale

variable {X Y : Scheme.{u}}

omit [HasSmallSiteSheafify A] in
/-- The square isomorphism of the degenerate square `𝟙 ≫ f = 𝟙 ≫ f` is the identity. -/
lemma Etale.squareUpperStarIso_hom_of_id_id (f : X ⟶ Y) (sq : CommSq (𝟙 X) (𝟙 X) f f) :
    (Etale.squareUpperStarIso A sq).hom = 𝟙 _ := by
  simp [Etale.squareUpperStarIso]

omit [HasSmallSiteSheafify A] in
/-- **The derived base change map of the degenerate square** `𝟙 ≫ f = 𝟙 ≫ f` is the counit of
`D f^*⁺ ⊣ R f_*⁺` followed by the unit of `D (𝟙)^*⁺ ⊣ R (𝟙)_*⁺`: it is the derived mate of the
identity square. -/
lemma Etale.derivedBaseChangeMapPlus_eq_counit_comp_unit (f : X ⟶ Y)
    (sq : CommSq (𝟙 X) (𝟙 X) f f) :
    Etale.derivedBaseChangeMapPlus A sq =
      (Etale.upperStarLowerStarAdjunction A f).derivedPlus.counit ≫
        (Etale.upperStarLowerStarAdjunction A (𝟙 X)).derivedPlus.unit := by
  have hmate : (mateEquiv (Etale.upperStarLowerStarAdjunction A f).derivedPlus
      (Etale.upperStarLowerStarAdjunction A (𝟙 X)).derivedPlus
      (TwoSquare.mk _ _ _ _ (𝟙 _))) =
      (Etale.upperStarLowerStarAdjunction A f).derivedPlus.counit ≫
        (Etale.upperStarLowerStarAdjunction A (𝟙 X)).derivedPlus.unit := by
    ext Z : 2
    have := (Etale.upperStarLowerStarAdjunction A (𝟙 X)).derivedPlus.unit.naturality
      ((Etale.upperStarLowerStarAdjunction A f).derivedPlus.counit.app Z)
    simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map] at this
    rw [NatTrans.comp_app, this]
    simp [mateEquiv_apply]
  symm
  refine Etale.derivedBaseChangeMapPlus_ext A sq _ fun K => ?_
  rw [← hmate]
  refine Adjunction.derivedPlus_mateEquiv_app_fac (Etale.upperStarLowerStarAdjunction A f)
    (Etale.upperStarLowerStarAdjunction A (𝟙 X))
    (TwoSquare.mk _ _ _ _ (Etale.squareUpperStarIso A sq).hom)
    (TwoSquare.mk _ _ _ _ (𝟙 _)) (fun N => ?_) K
  simp only [Etale.squareUpperStarIso_hom_of_id_id, NatTrans.mapHomotopyCategoryPlus_id,
    NatTrans.id_app, id_comp]
  erw [CategoryTheory.Functor.map_id]
  erw [comp_id]

/-- **The derived base change map of the degenerate square is the counit**: modulo the
identity isomorphisms `D (𝟙)^*⁺ ≅ 𝟭` and `R (𝟙)_*⁺ ≅ 𝟭`, the derived base change map
`f^* Rf_* ⟶ R(𝟙)_* (𝟙)^*` of the square `𝟙 ≫ f = 𝟙 ≫ f` is the counit of `D f^*⁺ ⊣ R f_*⁺`. -/
@[reassoc]
lemma Etale.derivedBaseChangeMapPlus_app_comp_lowerStarIdDerivedPlus (f : X ⟶ Y)
    (sq : CommSq (𝟙 X) (𝟙 X) f f) (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    (Etale.derivedBaseChangeMapPlus A sq).app K ≫
        ((𝟙 X)_*[A]).rightDerivedFunctorPlus.map ((Etale.upperStarIdDerivedPlus A X).hom.app K) ≫
        (Etale.lowerStarIdDerivedPlus A X).hom.app K =
      (Etale.upperStarLowerStarAdjunction A f).derivedPlus.counit.app K := by
  have h := NatTrans.congr_app (Etale.derivedPlus_unit_comp_upperStarIdDerivedPlus A X) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app] at h
  rw [Etale.derivedBaseChangeMapPlus_eq_counit_comp_unit, NatTrans.comp_app, assoc,
    reassoc_of% h, Iso.inv_hom_id_app]
  simp

variable {X' X Y' Y Z' Z : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  {e' : Y' ⟶ Z'} {e : Y ⟶ Z} {k : Z' ⟶ Z}

/-- **Vertical pasting of the derived base change maps**, for composites `fe = f ≫ e` and
`f'e' = f' ≫ e'` which are only propositionally equal to the given diagonals: the variant of
`AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_paste_vert` with the composition isomorphisms
`AlgebraicGeometry.Etale.lowerStarComp` taken with the given composites. -/
lemma Etale.derivedBaseChangeMapPlus_paste_vert_of_eq (sq₁ : CommSq g' f' f g)
    (sq₂ : CommSq g e' e k) {fe : X ⟶ Z} {f'e' : X' ⟶ Z'} (hfe : f ≫ e = fe)
    (hfe' : f' ≫ e' = f'e') (sq : CommSq g' f'e' fe k) :
    Etale.derivedBaseChangeMapPlus A sq =
      Functor.whiskerRight (Functor.rightDerivedFunctorPlusCompIso' (f)_*[A] (e)_*[A]
          (Etale.lowerStarComp A f e fe hfe.symm)).inv ((k)^*[A]).mapDerivedCategoryPlus ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (f)_*[A].rightDerivedFunctorPlus
          (Etale.derivedBaseChangeMapPlus A sq₂) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (Etale.derivedBaseChangeMapPlus A sq₁)
          (e')_*[A].rightDerivedFunctorPlus ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft ((g')^*[A]).mapDerivedCategoryPlus
          (Functor.rightDerivedFunctorPlusCompIso' (f')_*[A] (e')_*[A]
            (Etale.lowerStarComp A f' e' f'e' hfe'.symm)).hom := by
  subst hfe hfe'
  exact Etale.derivedBaseChangeMapPlus_paste_vert A sq₁ sq₂ sq

end AlgebraicGeometry
