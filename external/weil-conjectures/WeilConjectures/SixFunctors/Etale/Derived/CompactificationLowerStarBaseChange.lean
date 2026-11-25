/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionComp
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekToLowerStarBaseChange

/-!
# Pasting of derived base change maps along a compactification

For a compactification `c` of `f` and a compactification `c'` of its base change `f'` lying over
`c`, the derived base change map of `f` is the pasting of the derived base change maps of the
open and of the proper part, through the composition maps `R(c.i)_* ⋙ R(c.g)_* ⟶ Rf_*`
(`AlgebraicGeometry.Etale.map_rightDerivedLowerStarCompHom_derivedBaseChangeMap`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace Etale

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  (sq : CommSq g' f' f g) (c : Compactification f) (c' : Compactification f') (q : c'.Z ⟶ c.Z)
  (hi : IsPullback g' c'.i c.i q) (hp : CommSq q c'.g c.g g)

-- The elaboration of the pasting of several derived adjunction counits is heavy.
/-- **Pasting of derived base change maps along a compactification**: the derived base change
map of `f = c.i ≫ c.g` is the pasting of those of `c.i` and of `c.g`, through the composition
maps `R(c.i)_* ⋙ R(c.g)_* ⟶ Rf_*`. -/
lemma map_rightDerivedLowerStarCompHom_derivedBaseChangeMap
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    L((g)^*[A]).map ((rightDerivedLowerStarCompHom A c.i c.g f c.comm).app K) ≫
        (derivedBaseChangeMap A sq).app K =
      (derivedBaseChangeMap A hp).app (R((c.i)_*[A]).obj K) ≫
        R((c'.g)_*[A]).map ((derivedBaseChangeMap A hi.toCommSq).app K) ≫
        (rightDerivedLowerStarCompHom A c'.i c'.g f' c'.comm).app (L((g')^*[A]).obj K) := by
  apply ((derivedUpperStarLowerStarAdjunction A f').homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [derivedUpperStar_map_derivedBaseChangeMap_app_counit]
  have nsq := (derivedSquareUpperStarIso A sq).hom.naturality
    ((rightDerivedLowerStarCompHom A c.i c.g f c.comm).app K)
  simp only [Functor.comp_map] at nsq
  have hκ := conjugateEquiv_counit ((derivedUpperStarLowerStarAdjunction A c.g).comp
      (derivedUpperStarLowerStarAdjunction A c.i)) (derivedUpperStarLowerStarAdjunction A f)
    (leftDerivedUpperStarComp A c.i c.g f c.comm).hom K
  have hκ' := conjugateEquiv_counit ((derivedUpperStarLowerStarAdjunction A c'.g).comp
      (derivedUpperStarLowerStarAdjunction A c'.i)) (derivedUpperStarLowerStarAdjunction A f')
    (leftDerivedUpperStarComp A c'.i c'.g f' c'.comm).hom (L((g')^*[A]).obj K)
  simp only [Adjunction.comp_counit_app] at hκ hκ'
  rw [reassoc_of% nsq, ← Functor.map_comp, hκ, hκ']
  have key (Z : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
      (derivedSquareUpperStarIso A sq).hom.app Z ≫
        L((g')^*[A]).map ((leftDerivedUpperStarComp A c.i c.g f c.comm).hom.app Z) =
      (leftDerivedUpperStarComp A c'.i c'.g f' c'.comm).hom.app (L((g)^*[A]).obj Z) ≫
        L((c'.i)^*[A]).map ((derivedSquareUpperStarIso A hp).hom.app Z) ≫
        (derivedSquareUpperStarIso A hi.toCommSq).hom.app (L((c.g)^*[A]).obj Z) := by
    have h := compactification_derivedSquareUpperStarIso A sq c c' q hi hp Z
    rw [leftDerivedUpperStarCompactificationIso_eq, leftDerivedUpperStarCompactificationIso_eq]
      at h
    simp only [Iso.symm_hom] at h
    rw [← cancel_epi ((leftDerivedUpperStarComp A c'.i c'.g f' c'.comm).inv.app
      (L((g)^*[A]).obj Z)), Iso.inv_hom_id_app_assoc, ← h]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have nc' := (leftDerivedUpperStarComp A c'.i c'.g f' c'.comm).hom.naturality
    ((derivedBaseChangeMap A hp).app (R((c.i)_*[A]).obj K) ≫
      R((c'.g)_*[A]).map ((derivedBaseChangeMap A hi.toCommSq).app K))
  simp only [Functor.comp_map] at nc'
  have nε : L((c'.g)^*[A]).map (R((c'.g)_*[A]).map ((derivedBaseChangeMap A hi.toCommSq).app K)) ≫
      (derivedUpperStarLowerStarAdjunction A c'.g).counit.app
        (R((c'.i)_*[A]).obj (L((g')^*[A]).obj K)) =
      (derivedUpperStarLowerStarAdjunction A c'.g).counit.app
        (L((q)^*[A]).obj (R((c.i)_*[A]).obj K)) ≫ (derivedBaseChangeMap A hi.toCommSq).app K :=
    (derivedUpperStarLowerStarAdjunction A c'.g).counit.naturality _
  have nhi := (derivedSquareUpperStarIso A hi.toCommSq).hom.naturality
    ((derivedUpperStarLowerStarAdjunction A c.g).counit.app (R((c.i)_*[A]).obj K))
  simp only [Functor.comp_map] at nhi
  rw [Functor.map_comp]
  erw [reassoc_of% (key (R((c.g)_*[A]).obj (R((c.i)_*[A]).obj K)))]
  rw [← Functor.map_comp_assoc (L((f')^*[A]))]
  erw [
    reassoc_of% nc']
  congr 1
  simp only [Functor.map_comp, Category.assoc]
  slice_rhs 2 3 => rw [← Functor.map_comp, nε, Functor.map_comp]
  simp only [Category.assoc]
  have e1 := derivedUpperStar_map_derivedBaseChangeMap_app_counit A hi.toCommSq K
  have e2 := congrArg (L((c'.i)^*[A]).map)
    (derivedUpperStar_map_derivedBaseChangeMap_app_counit A hp (R((c.i)_*[A]).obj K))
  simp only [Functor.map_comp] at e2
  rw [reassoc_of% e2, e1, reassoc_of% nhi]

/-- **The forget-supports maps commute with base change**: the compactly supported base change
map `Lg^* Rf_!(c) ⟶ Rf'_!(c') Lg'^*` followed by the forget-supports map
`Rf'_!(c') ⟶ R(c'.g)_* R(c'.i)_* ⟶ Rf'_*` of `c'` is `Lg^*` of the forget-supports map of `c`
followed by the derived base change map `Lg^* Rf_* ⟶ Rf'_* Lg'^*`. -/
lemma rightDerivedLowerShriekOfCompactificationBaseChangeMap'_app_comp_toLowerStar
    [HasSmallSiteSheafify A] (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (rightDerivedLowerShriekOfCompactificationBaseChangeMap' A c c' q hi hp).app K ≫
        R((c'.g)_*[A]).map ((derivedOpenImmersionLowerShriekToLowerStar A c'.i).app
          (L((g')^*[A]).obj K)) ≫
        (rightDerivedLowerStarCompHom A c'.i c'.g f' c'.comm).app (L((g')^*[A]).obj K) =
      L((g)^*[A]).map (R((c.g)_*[A]).map ((derivedOpenImmersionLowerShriekToLowerStar A c.i).app
          K)) ≫
        L((g)^*[A]).map ((rightDerivedLowerStarCompHom A c.i c.g f c.comm).app K) ≫
        (derivedBaseChangeMap A sq).app K := by
  rw [map_rightDerivedLowerStarCompHom_derivedBaseChangeMap A sq c c' q hi hp,
    rightDerivedLowerShriekOfCompactificationBaseChangeMap'_app]
  have n := (derivedBaseChangeMap A hp).naturality
    ((derivedOpenImmersionLowerShriekToLowerStar A c.i).app K)
  simp only [Functor.comp_map] at n
  rw [reassoc_of% n, Category.assoc]
  congr 1
  simp only [← Functor.map_comp_assoc]
  congr 2
  rw [← derivedOpenImmersionLowerShriekBaseChangeIso_hom_comp_toLowerStar A hi K,
    Iso.inv_hom_id_app_assoc]

end Etale

end AlgebraicGeometry
