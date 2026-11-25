/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat

/-!
# The comparison `D(j_!) ⟶ Rj_*` and base change

For a cartesian square `g' ≫ j = j' ≫ g''` of schemes with `j` and `j'` open immersions, the
derived comparison `D(j_!) ⟶ Rj_*`
(`AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekToLowerStar`)
intertwines the base change isomorphism of the extension by zero with the derived base change map
of the pushforward
(`AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekBaseChangeIso_hom_comp_toLowerStar`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A] [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
  [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]

variable {U' U Z' Z : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z}
  [IsOpenImmersion j] [IsOpenImmersion j']

omit [HasSmallSiteSheafify A] in
/-- The comparison `D(j_!) ⟶ Rj_*` is the transpose of the inverse of the unit of
`D(j_!) ⊣ D(j^*)`. -/
lemma derivedOpenImmersionLowerShriekToLowerStar_app {V W : Scheme.{u}} (k : V ⟶ W)
    [IsOpenImmersion k] (N : DerivedCategory (Sheaf V.smallEtaleTopology A)) :
    (derivedOpenImmersionLowerShriekToLowerStar A k).app N =
      (mapDerivedUpperStarLowerStarAdjunction A k).homEquiv _ _
        (inv ((derivedOpenImmersionLowerShriekUpperStarAdjunction A k).unit.app N)) := by
  simp [derivedOpenImmersionLowerShriekToLowerStar, Adjunction.homEquiv_unit]

/-- **The comparison `D(j_!) ⟶ Rj_*` commutes with base change**: for a cartesian square
`g' ≫ j = j' ≫ g''` with `j`, `j'` open immersions, the base change isomorphism
`Lg'^* ⋙ Dj'_! ≅ Dj_! ⋙ Lg''^*` followed by `Lg''^*` of `D(j_!) ⟶ Rj_*` and the derived base
change map `Lg''^* Rj_* ⟶ Rj'_* Lg'^*` is the comparison `D(j'_!) ⟶ Rj'_*`. -/
lemma derivedOpenImmersionLowerShriekBaseChangeIso_hom_comp_toLowerStar
    (hsq : IsPullback g' j' j g'') (K : DerivedCategory (Sheaf U.smallEtaleTopology A)) :
    (derivedOpenImmersionLowerShriekBaseChangeIso A hsq).hom.app K ≫
        L((g'')^*[A]).map ((derivedOpenImmersionLowerShriekToLowerStar A j).app K) ≫
        (derivedBaseChangeMap A hsq.toCommSq).app K =
      (derivedOpenImmersionLowerShriekToLowerStar A j').app (L((g')^*[A]).obj K) := by
  apply ((mapDerivedUpperStarLowerStarAdjunction A j').homEquiv _ _).symm.injective
  rw [derivedOpenImmersionLowerShriekToLowerStar_app A j']
  erw [Equiv.symm_apply_apply]
  rw [
    Adjunction.homEquiv_counit]
  have hε {V W : Scheme.{u}} (k : V ⟶ W) (N : DerivedCategory (Sheaf V.smallEtaleTopology A)) :
      (mapDerivedUpperStarLowerStarAdjunction A k).counit.app N =
        (leftDerivedUpperStarIsoMapDerivedCategory A k).inv.app (R((k)_*[A]).obj N) ≫
          (derivedUpperStarLowerStarAdjunction A k).counit.app N := by
    rw [mapDerivedUpperStarLowerStarAdjunction_eq]
    rfl
  have hT : D((j)^*[A]).map ((derivedOpenImmersionLowerShriekToLowerStar A j).app K) ≫
      (mapDerivedUpperStarLowerStarAdjunction A j).counit.app K =
        inv ((derivedOpenImmersionLowerShriekUpperStarAdjunction A j).unit.app K) := by
    have h := derivedOpenImmersionLowerShriekToLowerStar_app A j K
    rw [Adjunction.homEquiv_unit] at h
    rw [h, Functor.map_comp, Category.assoc]
    erw [(mapDerivedUpperStarLowerStarAdjunction A j).counit_naturality]
    rw [← Category.assoc]
    erw [(mapDerivedUpperStarLowerStarAdjunction A j).left_triangle_components]
    exact Category.id_comp _
  rw [← cancel_epi ((derivedOpenImmersionLowerShriekUpperStarAdjunction A j').unit.app _),
    IsIso.hom_inv_id]
  have n₁ := (derivedOpenImmersionSquareMap A hsq.toCommSq).naturality
    ((derivedOpenImmersionLowerShriekToLowerStar A j).app K)
  have n₂ := (leftDerivedUpperStarIsoMapDerivedCategory A j').inv.naturality
    ((derivedBaseChangeMap A hsq.toCommSq).app K)
  simp only [Functor.comp_map] at n₁ n₂
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (unit_map_derivedOpenImmersionLowerShriekBaseChangeIso A hsq K),
    ← reassoc_of% n₁, hε, reassoc_of% n₂, derivedUpperStar_map_derivedBaseChangeMap_app_counit,
    derivedOpenImmersionSquareMap_app]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app_assoc]
  rw [hε] at hT
  simp only [← Functor.map_comp]
  rw [hT, IsIso.hom_inv_id, CategoryTheory.Functor.map_id]
  rfl

end Etale

end AlgebraicGeometry
