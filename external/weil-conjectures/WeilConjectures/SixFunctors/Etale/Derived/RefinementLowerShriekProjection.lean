/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange

/-!
# The projection formula for the extension by zero and refinements

For a refinement `r : c.Refinement d` of compactifications whose square over `X` is cartesian,
with `q = r.hom`, the projection formula for `D(d.i)_!` pulled back along `Lq^*` is the
projection formula for `D(c.i)_!`, through the base change isomorphism
`D(c.i)_! ≅ D(d.i)_! ⋙ Dq^*` (`AlgebraicGeometry.Etale.refinementLowerShriekBaseChangeDerivedIso`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A] [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]
  [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]

namespace Etale

variable {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)

-- The tensor comparisons of the derived pullbacks make this rewriting expensive.
omit [HasSmallSiteSheafify A] in
/-- The square map of a refinement is compatible with the comparisons
`Dj^*X ⊗ᴸ Lj^*Y ≅ Dj^*(X ⊗ᴸ Y)` and the tensor comparison of `Lq^*`. -/
lemma refinementSquareMap_tensor (M N : DerivedCategory (Sheaf d.Z.smallEtaleTopology A)) :
    ((mapDerivedCategoryUpperStarDerivedTensorIso A d.i).hom.app M).app N ≫
        (refinementSquareMap A r).app (((-⊗ᴸ-(d.Z)[A]).obj M).obj N) ≫
        D((c.i)^*[A]).map (((leftDerivedUpperStarTensorComparison A r.hom).app M).app N) =
      ((-⊗ᴸ-(X)[A]).map ((refinementSquareMap A r).app M)).app _ ≫
        ((-⊗ᴸ-(X)[A]).obj _).map
          ((leftDerivedUpperStarComp A c.i r.hom d.i r.i_hom.symm).hom.app N) ≫
        ((mapDerivedCategoryUpperStarDerivedTensorIso A c.i).hom.app
          (L((r.hom)^*[A]).obj M)).app (L((r.hom)^*[A]).obj N) := by
  rw [refinementSquareMap_app, refinementSquareMap_app]
  simp only [mapDerivedCategoryUpperStarDerivedTensorIso, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom, Functor.whiskeringLeft₂_map_app_app_app_app,
    Functor.postcompose₂_map_app_app_app, Functor.map_comp, Category.assoc]
  have key₀ : ((leftDerivedUpperStarTensorNatIso A d.i).inv.app M).app N ≫
      (leftDerivedUpperStarComp A c.i r.hom d.i r.i_hom.symm).hom.app
        (((-⊗ᴸ-(d.Z)[A]).obj M).obj N) ≫
      L((c.i)^*[A]).map (((leftDerivedUpperStarTensorComparison A r.hom).app M).app N) =
      ((leftDerivedUpperStarComp A c.i r.hom d.i r.i_hom.symm).hom.app M ⊗ₘ
        (leftDerivedUpperStarComp A c.i r.hom d.i r.i_hom.symm).hom.app N) ≫
      ((leftDerivedUpperStarTensorNatIso A c.i).inv.app (L((r.hom)^*[A]).obj M)).app
        (L((r.hom)^*[A]).obj N) := by
    have h := leftDerivedUpperStarTensorComparison_comp A c.i r.hom d.i r.i_hom.symm M N
    change (leftDerivedUpperStarTensorIso A d.i M N).inv ≫ _ =
      _ ≫ (leftDerivedUpperStarTensorIso A c.i _ _).inv
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, leftDerivedUpperStarTensorIso_hom,
      leftDerivedUpperStarTensorIso_hom]
    rw [Category.assoc]
    exact h.symm
  have c₂ : L((c.i)^*[A]).map (((leftDerivedUpperStarTensorComparison A r.hom).app M).app N) ≫
      (leftDerivedUpperStarIsoMapDerivedCategory A c.i).hom.app
        (((-⊗ᴸ-(c.Z)[A]).obj (L((r.hom)^*[A]).obj M)).obj (L((r.hom)^*[A]).obj N)) =
      (leftDerivedUpperStarIsoMapDerivedCategory A c.i).hom.app
        (L((r.hom)^*[A]).obj (((-⊗ᴸ-(d.Z)[A]).obj M).obj N)) ≫
      D((c.i)^*[A]).map (((leftDerivedUpperStarTensorComparison A r.hom).app M).app N) :=
    (leftDerivedUpperStarIsoMapDerivedCategory A c.i).hom.naturality _
  rw [Iso.hom_inv_id_app_assoc]
  erw [← c₂]
  rw [reassoc_of% key₀]
  simp only [derivedTensor, curriedTensor_map_app, curriedTensor_obj_map]
  have w : (leftDerivedUpperStarIsoMapDerivedCategory A c.i).hom.app (L((r.hom)^*[A]).obj M) ▷
      L((d.i)^*[A]).obj N ≫
      D((c.i)^*[A]).obj (L((r.hom)^*[A]).obj M) ◁
        (leftDerivedUpperStarComp A c.i r.hom d.i r.i_hom.symm).hom.app N ≫
      (leftDerivedUpperStarIsoMapDerivedCategory A c.i).inv.app (L((r.hom)^*[A]).obj M) ▷
        L((c.i)^*[A]).obj (L((r.hom)^*[A]).obj N) =
      L((c.i)^*[A]).obj (L((r.hom)^*[A]).obj M) ◁
        (leftDerivedUpperStarComp A c.i r.hom d.i r.i_hom.symm).hom.app N := by
    rw [← whisker_exchange_assoc]
    dsimp only [Functor.comp_obj]
    rw [← comp_whiskerRight, Iso.hom_inv_id_app, id_whiskerRight, Category.comp_id]
  dsimp only [Functor.comp_obj]
  simp only [reassoc_of% w]
  simp only [MonoidalCategory.tensorHom_def, Category.assoc]


/-- The base change isomorphism `D(c.i)_! ≅ D(d.i)_! ⋙ Lq^*` of a refinement, through the derived
pullback. -/
noncomputable abbrev refinementLowerShriekBaseChangeLeftDerivedIso
    (hcart : IsPullback c.i (𝟙 X) r.hom d.i) :
    D((c.i)_!open[A]) ≅ D((d.i)_!open[A]) ⋙ L((r.hom)^*[A]) :=
  refinementLowerShriekBaseChangeDerivedIso A r hcart ≪≫
    Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory A r.hom).symm

omit [Etale.UpperStarPreservesFlat A] in
lemma unit_map_refinementLowerShriekBaseChangeLeftDerivedIso
    (hcart : IsPullback c.i (𝟙 X) r.hom d.i)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (derivedOpenImmersionLowerShriekUpperStarAdjunction A c.i).unit.app K ≫
        D((c.i)^*[A]).map ((refinementLowerShriekBaseChangeLeftDerivedIso A r hcart).hom.app K) =
      (derivedOpenImmersionLowerShriekUpperStarAdjunction A d.i).unit.app K ≫
        (refinementSquareMap A r).app (D((d.i)_!open[A]).obj K) := by
  have h := unit_map_refinementLowerShriekBaseChangeDerivedIso A r hcart K
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Iso.symm_hom, Functor.map_comp, refinementSquareMap,
    Functor.whiskerRight_app]
  rw [reassoc_of% h]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]

/-- **The projection formula for the extension by zero and refinements**: the derived pullback
along `q = r.hom` of the projection map of `D(d.i)_!` is the projection map of `D(c.i)_!`, through
the base change isomorphism `D(c.i)_! ≅ D(d.i)_! ⋙ Lq^*`. -/
lemma refinementLowerShriekProjectionMap_baseChange (hcart : IsPullback c.i (𝟙 X) r.hom d.i)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (M : DerivedCategory (Sheaf d.Z.smallEtaleTopology A)) :
    (refinementLowerShriekBaseChangeLeftDerivedIso A r hcart).hom.app
          (((-⊗ᴸ-(X)[A]).obj K).obj (L((d.i)^*[A]).obj M)) ≫
        L((r.hom)^*[A]).map (((derivedOpenImmersionLowerShriekProjectionMap A d.i).app K).app M) ≫
        ((leftDerivedUpperStarTensorComparison A r.hom).app (D((d.i)_!open[A]).obj K)).app M =
      D((c.i)_!open[A]).map (((-⊗ᴸ-(X)[A]).obj K).map
          ((leftDerivedUpperStarComp A c.i r.hom d.i r.i_hom.symm).hom.app M)) ≫
        ((derivedOpenImmersionLowerShriekProjectionMap A c.i).app K).app
          (L((r.hom)^*[A]).obj M) ≫
        ((-⊗ᴸ-(c.Z)[A]).map ((refinementLowerShriekBaseChangeLeftDerivedIso A r hcart).hom.app
          K)).app (L((r.hom)^*[A]).obj M) := by
  have h := Adjunction.projectionMap_mate (U := 𝟭 _) (V := L((r.hom)^*[A]))
    (derivedOpenImmersionLowerShriekUpperStarAdjunction A d.i)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction A c.i) L((d.i)^*[A]) L((c.i)^*[A])
    (mapDerivedCategoryUpperStarDerivedTensorIso A d.i).hom
    (mapDerivedCategoryUpperStarDerivedTensorIso A c.i).hom (𝟙 _)
    (leftDerivedUpperStarTensorComparison A r.hom) (refinementSquareMap A r)
    (leftDerivedUpperStarComp A c.i r.hom d.i r.i_hom.symm).hom
    (refinementLowerShriekBaseChangeLeftDerivedIso A r hcart).hom
    (unit_map_refinementLowerShriekBaseChangeLeftDerivedIso A r hcart)
    (fun M N ↦ by
      rw [NatTrans.id_app, NatTrans.id_app, Category.id_comp]
      exact refinementSquareMap_tensor A r M N) K M
  rw [NatTrans.id_app, NatTrans.id_app, CategoryTheory.Functor.map_id, Category.id_comp] at h
  exact h

section Iso

variable {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

/-- The inverse form of `refinementLowerShriekProjectionMap_baseChange`, with the projection
map `j_!K ⊗ᴸ M ⟶ j_!(K ⊗ᴸ Lj^*M)`. -/
lemma refinementLowerShriekProjectionIso_inv_baseChange (hcart : IsPullback c.i (𝟙 X) r.hom d.i)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (M : DerivedCategory (Sheaf d.Z.smallEtaleTopology A)) :
    L((r.hom)^*[A]).map (((derivedOpenImmersionLowerShriekProjectionIso A d.i).inv.app K).app M) ≫
        (refinementLowerShriekBaseChangeLeftDerivedIso A r hcart).inv.app
          (((-⊗ᴸ-(X)[A]).obj K).obj (L((d.i)^*[A]).obj M)) =
      ((leftDerivedUpperStarTensorComparison A r.hom).app (D((d.i)_!open[A]).obj K)).app M ≫
        ((-⊗ᴸ-(c.Z)[A]).map ((refinementLowerShriekBaseChangeLeftDerivedIso A r hcart).inv.app
          K)).app (L((r.hom)^*[A]).obj M) ≫
        ((derivedOpenImmersionLowerShriekProjectionIso A c.i).inv.app K).app
          (L((r.hom)^*[A]).obj M) ≫
        D((c.i)_!open[A]).map (((-⊗ᴸ-(X)[A]).obj K).map
          ((leftDerivedUpperStarComp A c.i r.hom d.i r.i_hom.symm).inv.app M)) := by
  have h := refinementLowerShriekProjectionMap_baseChange A r hcart K M
  rw [← cancel_epi (L((r.hom)^*[A]).map
      (((derivedOpenImmersionLowerShriekProjectionIso A d.i).hom.app K).app M)),
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app_app, CategoryTheory.Functor.map_id,
    Category.id_comp,
    ← cancel_epi ((refinementLowerShriekBaseChangeLeftDerivedIso A r hcart).hom.app
      (((-⊗ᴸ-(X)[A]).obj K).obj (L((d.i)^*[A]).obj M))), Iso.hom_inv_id_app,
    derivedOpenImmersionLowerShriekProjectionIso_hom]
  erw [reassoc_of% h]
  have e₁ : ((-⊗ᴸ-(c.Z)[A]).map ((refinementLowerShriekBaseChangeLeftDerivedIso A r hcart).hom.app
        K)).app (L((r.hom)^*[A]).obj M) ≫
      ((-⊗ᴸ-(c.Z)[A]).map ((refinementLowerShriekBaseChangeLeftDerivedIso A r hcart).inv.app
        K)).app (L((r.hom)^*[A]).obj M) = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← Functor.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id]
    rfl
  have e₂ : ((derivedOpenImmersionLowerShriekProjectionMap A c.i).app K).app
        (L((r.hom)^*[A]).obj M) ≫
      ((derivedOpenImmersionLowerShriekProjectionIso A c.i).inv.app K).app
        (L((r.hom)^*[A]).obj M) = 𝟙 _ := by
    rw [← derivedOpenImmersionLowerShriekProjectionIso_hom, Iso.hom_inv_id_app_app]
  have e₃ : D((c.i)_!open[A]).map (((-⊗ᴸ-(X)[A]).obj K).map
        ((leftDerivedUpperStarComp A c.i r.hom d.i r.i_hom.symm).hom.app M)) ≫
      D((c.i)_!open[A]).map (((-⊗ᴸ-(X)[A]).obj K).map
        ((leftDerivedUpperStarComp A c.i r.hom d.i r.i_hom.symm).inv.app M)) = 𝟙 _ := by
    rw [← Functor.map_comp, ← Functor.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rw [reassoc_of% e₁, reassoc_of% e₂, e₃]

end Iso
end Etale

end AlgebraicGeometry
