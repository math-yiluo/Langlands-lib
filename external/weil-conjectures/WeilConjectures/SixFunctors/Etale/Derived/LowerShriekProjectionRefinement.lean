/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComparison.CompositionLaw
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionComp
public import WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat

/-!
# The projection map and refinements of compactifications

For a refinement `r : c.Refinement d` of compactifications of `f : X ⟶ Y` whose square over `X`
is cartesian, the comparison `Rf_!(d) ⟶ Rf_!(c)`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationComparison`) intertwines the
projection maps `PF_d` and `PF_c`
(`AlgebraicGeometry.Etale.projectionMapOfCompactification_comparison`).
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
  [HasSmallSiteSheafify A]
  {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

namespace Etale

variable {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)

omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A] in
/-- The composition isomorphism `Rq_* ⋙ R(d.g)_* ≅ R(c.g)_*` of a refinement is the conjugate of
the composition isomorphism `D((c.g)^*) ≅ D((d.g)^*) ⋙ D(q^*)` under the derived adjunctions. -/
lemma rightDerivedFunctorCompIso'_refinementLowerStarComp_hom :
    (Functor.rightDerivedFunctorCompIso' (r.hom)_*[A] (d.g)_*[A]
        (refinementLowerStarComp A r)).hom =
      conjugateEquiv ((mapDerivedUpperStarLowerStarAdjunction A d.g).comp
          (mapDerivedUpperStarLowerStarAdjunction A r.hom))
        (mapDerivedUpperStarLowerStarAdjunction A c.g)
        (Functor.mapDerivedCategoryNatIso (Etale.upperStarComp A r.hom d.g c.g r.hom_g.symm) ≪≫
          (Functor.mapDerivedCategoryCompIso _ _).symm).hom :=
  Adjunction.rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv
    (Etale.upperStarLowerStarAdjunction A r.hom) (Etale.upperStarLowerStarAdjunction A d.g)
    (Etale.upperStarLowerStarAdjunction A c.g) _ _ (by
      rw [refinementLowerStarComp_eq]
      exact (congrArg Iso.hom
        (Etale.conjugateIsoEquiv_upperStarComp A r.hom d.g c.g r.hom_g.symm)).symm)

omit [Etale.UpperStarPreservesFlat A] in
lemma rightDerivedFunctorCompIso'_refinementLowerStarComp_hom_eq :
    (Functor.rightDerivedFunctorCompIso' (r.hom)_*[A] (d.g)_*[A]
        (refinementLowerStarComp A r)).hom =
      rightDerivedLowerStarCompHom A r.hom d.g c.g r.hom_g.symm := by
  rw [rightDerivedFunctorCompIso'_refinementLowerStarComp_hom, rightDerivedLowerStarCompHom,
    conjugateEquiv_leftDerivedUpperStarComp_hom]

omit [Etale.UpperStarPreservesFlat A] in
/-- The comparison along a refinement, through the derived pullback `Lq^*`: it is the unit of
`Lq^* ⊣ Rq_*`, the inverse of the base change `D(c.i)_! ≅ D(d.i)_! ⋙ Lq^*` and the composition
map `Rq_* ⋙ R(d.g)_* ⟶ R(c.g)_*`. -/
lemma rightDerivedLowerShriekOfCompactificationComparison_app
    (hcart : IsPullback c.i (𝟙 X) r.hom d.i)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (rightDerivedLowerShriekOfCompactificationComparison A r hcart).app M =
      R((d.g)_*[A]).map ((derivedUpperStarLowerStarAdjunction A r.hom).unit.app
          (D((d.i)_!open[A]).obj M)) ≫
        R((d.g)_*[A]).map (R((r.hom)_*[A]).map
          ((leftDerivedUpperStarIsoMapDerivedCategory A r.hom).hom.app _ ≫
            (refinementLowerShriekBaseChangeDerivedIso A r hcart).inv.app M)) ≫
        (rightDerivedLowerStarCompHom A r.hom d.g c.g r.hom_g.symm).app
          (D((c.i)_!open[A]).obj M) := by
  simp only [rightDerivedLowerShriekOfCompactificationComparison, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_map,
    rightDerivedFunctorCompIso'_refinementLowerStarComp_hom_eq,
    mapDerivedUpperStarLowerStarAdjunction_eq,
    Adjunction.ofNatIsoLeft_unit, Functor.map_comp, Category.assoc]

/-- The key square for `projectionMapOfCompactification_comparison`: on `Z_c`, the derived
pullback along `q = r.hom` of the projection formula for `d.i` matches the projection formula
for `c.i` through the base change `D(c.i)_! ≅ D(d.i)_! ⋙ Lq^*`. -/
lemma refinement_projection_key (hcart : IsPullback c.i (𝟙 X) r.hom d.i)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    L((r.hom)^*[A]).map (((derivedOpenImmersionLowerShriekProjectionIso A d.i).inv.app K).app
        (L((d.g)^*[A]).obj L)) ≫
      L((r.hom)^*[A]).map (D((d.i)_!open[A]).map (((-⊗ᴸ-(X)[A]).obj K).map
        ((leftDerivedUpperStarCompactificationIso A d).hom.app L))) ≫
      (leftDerivedUpperStarIsoMapDerivedCategory A r.hom).hom.app _ ≫
      (refinementLowerShriekBaseChangeDerivedIso A r hcart).inv.app
        (((-⊗ᴸ-(X)[A]).obj K).obj (L((f)^*[A]).obj L)) =
    ((leftDerivedUpperStarTensorComparison A r.hom).app (D((d.i)_!open[A]).obj K)).app
        (L((d.g)^*[A]).obj L) ≫
      ((-⊗ᴸ-(c.Z)[A]).map ((leftDerivedUpperStarIsoMapDerivedCategory A r.hom).hom.app
        (D((d.i)_!open[A]).obj K))).app (L((r.hom)^*[A]).obj (L((d.g)^*[A]).obj L)) ≫
      ((-⊗ᴸ-(c.Z)[A]).map ((refinementLowerShriekBaseChangeDerivedIso A r hcart).inv.app K)).app
        (L((r.hom)^*[A]).obj (L((d.g)^*[A]).obj L)) ≫
      ((-⊗ᴸ-(c.Z)[A]).obj (D((c.i)_!open[A]).obj K)).map
        ((leftDerivedUpperStarComp A r.hom d.g c.g r.hom_g.symm).inv.app L) ≫
      ((derivedOpenImmersionLowerShriekProjectionIso A c.i).inv.app K).app
        (L((c.g)^*[A]).obj L) ≫
      D((c.i)_!open[A]).map (((-⊗ᴸ-(X)[A]).obj K).map
        ((leftDerivedUpperStarCompactificationIso A c).hom.app L)) := by
  have hbcL : ∀ Z, (leftDerivedUpperStarIsoMapDerivedCategory A r.hom).hom.app
      (D((d.i)_!open[A]).obj Z) ≫ (refinementLowerShriekBaseChangeDerivedIso A r hcart).inv.app Z =
      (refinementLowerShriekBaseChangeLeftDerivedIso A r hcart).inv.app Z := fun Z ↦ rfl
  have hnat := (refinementLowerShriekBaseChangeLeftDerivedIso A r hcart).inv.naturality
    (((-⊗ᴸ-(X)[A]).obj K).map ((leftDerivedUpperStarCompactificationIso A d).hom.app L))
  dsimp only [Functor.comp_map, Functor.comp_obj] at hnat
  have h₁₂ : ((-⊗ᴸ-(c.Z)[A]).map ((leftDerivedUpperStarIsoMapDerivedCategory A r.hom).hom.app
        (D((d.i)_!open[A]).obj K))).app (L((r.hom)^*[A]).obj (L((d.g)^*[A]).obj L)) ≫
      ((-⊗ᴸ-(c.Z)[A]).map ((refinementLowerShriekBaseChangeDerivedIso A r hcart).inv.app K)).app
        (L((r.hom)^*[A]).obj (L((d.g)^*[A]).obj L)) =
      ((-⊗ᴸ-(c.Z)[A]).map ((refinementLowerShriekBaseChangeLeftDerivedIso A r hcart).inv.app
        K)).app (L((r.hom)^*[A]).obj (L((d.g)^*[A]).obj L)) := by
    rw [← NatTrans.comp_app, ← Functor.map_comp, hbcL]
  have hρ : ((-⊗ᴸ-(c.Z)[A]).obj (D((c.i)_!open[A]).obj K)).map
        ((leftDerivedUpperStarComp A r.hom d.g c.g r.hom_g.symm).inv.app L) ≫
      ((derivedOpenImmersionLowerShriekProjectionIso A c.i).inv.app K).app
        (L((c.g)^*[A]).obj L) =
      ((derivedOpenImmersionLowerShriekProjectionIso A c.i).inv.app K).app
        (L((r.hom)^*[A]).obj (L((d.g)^*[A]).obj L)) ≫
      D((c.i)_!open[A]).map (((-⊗ᴸ-(X)[A]).obj K).map (L((c.i)^*[A]).map
        ((leftDerivedUpperStarComp A r.hom d.g c.g r.hom_g.symm).inv.app L))) :=
    ((derivedOpenImmersionLowerShriekProjectionIso A c.i).inv.app K).naturality _
  have hcoh : (leftDerivedUpperStarComp A c.i r.hom d.i r.i_hom.symm).inv.app
        (L((d.g)^*[A]).obj L) ≫ (leftDerivedUpperStarCompactificationIso A d).hom.app L =
      L((c.i)^*[A]).map ((leftDerivedUpperStarComp A r.hom d.g c.g r.hom_g.symm).inv.app L) ≫
        (leftDerivedUpperStarCompactificationIso A c).hom.app L := by
    rw [leftDerivedUpperStarCompactificationIso_eq, leftDerivedUpperStarCompactificationIso_eq]
    exact (map_leftDerivedUpperStarComp_inv_app_leftDerivedUpperStarComp_inv_app A c.i r.hom d.g
      d.i c.g f r.i_hom.symm r.hom_g.symm d.comm L).symm
  simp only [hbcL, reassoc_of% h₁₂, reassoc_of% hρ]
  simp only [hnat, reassoc_of% (refinementLowerShriekProjectionIso_inv_baseChange A r hcart K
    (L((d.g)^*[A]).obj L))]
  simp only [← Functor.map_comp, hcoh]

/-- The comparison `Rf_!(d) ⟶ Rf_!(c)` along a refinement intertwines the projection maps. -/
lemma projectionMapOfCompactification_comparison (hcart : IsPullback c.i (𝟙 X) r.hom d.i)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ((projectionMapOfCompactification A d).app K).app L ≫
        (rightDerivedLowerShriekOfCompactificationComparison A r hcart).app
          (((-⊗ᴸ-(X)[A]).obj K).obj (L((f)^*[A]).obj L)) =
      ((-⊗ᴸ-(Y)[A]).map ((rightDerivedLowerShriekOfCompactificationComparison A r hcart).app
          K)).app L ≫
        ((projectionMapOfCompactification A c).app K).app L := by
  rw [rightDerivedLowerShriekOfCompactificationComparison_app,
    rightDerivedLowerShriekOfCompactificationComparison_app,
    projectionMapOfCompactification_app_app,
    projectionMapOfCompactification_app_app]
  simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
  rw [rightDerivedLowerStarProjectionMap_comp'_assoc,
    rightDerivedLowerStarProjectionMap_naturality_left_assoc,
    rightDerivedLowerStarProjectionMap_naturality_left_assoc,
    rightDerivedLowerStarProjectionMap_naturality_left_assoc]
  erw [← (rightDerivedLowerStarCompHom A r.hom d.g c.g r.hom_g.symm).naturality_assoc,
    ← (rightDerivedLowerStarCompHom A r.hom d.g c.g r.hom_g.symm).naturality_assoc,
    ← (rightDerivedLowerStarCompHom A r.hom d.g c.g r.hom_g.symm).naturality]
  simp only [Functor.comp_map, ← Functor.map_comp_assoc]
  congr 2
  refine congrArg (fun t ↦ R((d.g)_*[A]).map t) ?_
  have hη₁ := (derivedUpperStarLowerStarAdjunction A r.hom).unit.naturality
    (D((d.i)_!open[A]).map (((-⊗ᴸ-(X)[A]).obj K).map
      ((leftDerivedUpperStarCompactificationIso A d).hom.app L)))
  have hη₂ : ((derivedOpenImmersionLowerShriekProjectionIso A d.i).inv.app K).app
        (L((d.g)^*[A]).obj L) ≫
      (derivedUpperStarLowerStarAdjunction A r.hom).unit.app (D((d.i)_!open[A]).obj
        (((-⊗ᴸ-(X)[A]).obj K).obj (L((d.i)^*[A]).obj (L((d.g)^*[A]).obj L)))) =
      (derivedUpperStarLowerStarAdjunction A r.hom).unit.app
        (((-⊗ᴸ-(d.Z)[A]).obj (D((d.i)_!open[A]).obj K)).obj (L((d.g)^*[A]).obj L)) ≫
      R((r.hom)_*[A]).map (L((r.hom)^*[A]).map
        (((derivedOpenImmersionLowerShriekProjectionIso A d.i).inv.app K).app
          (L((d.g)^*[A]).obj L))) :=
    (derivedUpperStarLowerStarAdjunction A r.hom).unit.naturality _
  dsimp only [Functor.id_map, Functor.id_obj, Functor.comp_map, Functor.comp_obj] at hη₁
  simp only [reassoc_of% hη₁, reassoc_of% hη₂]
  have hR3 : ((-⊗ᴸ-(d.Z)[A]).map ((derivedUpperStarLowerStarAdjunction A r.hom).unit.app
        (D((d.i)_!open[A]).obj K))).app (L((d.g)^*[A]).obj L) ≫
      ((rightDerivedLowerStarProjectionMap A r.hom).app
        (L((r.hom)^*[A]).obj (D((d.i)_!open[A]).obj K))).app (L((d.g)^*[A]).obj L) =
      (derivedUpperStarLowerStarAdjunction A r.hom).unit.app
          (((-⊗ᴸ-(d.Z)[A]).obj (D((d.i)_!open[A]).obj K)).obj (L((d.g)^*[A]).obj L)) ≫
        R((r.hom)_*[A]).map (((leftDerivedUpperStarTensorComparison A r.hom).app
          (D((d.i)_!open[A]).obj K)).app (L((d.g)^*[A]).obj L)) :=
    (Adjunction.unit_app_comp_map_rightAdjointProjectionMap
      (derivedUpperStarLowerStarAdjunction A r.hom) (leftDerivedUpperStarTensorComparison A r.hom)
      (D((d.i)_!open[A]).obj K) (L((d.g)^*[A]).obj L)).symm
  simp only [rightDerivedLowerStarProjectionMap_naturality_left_assoc, reassoc_of% hR3]
  simp only [← Functor.map_comp]
  refine congrArg (fun t ↦ _ ≫ R((r.hom)_*[A]).map t) ?_
  simpa only [Category.assoc] using refinement_projection_key A r hcart K L


end Etale

end AlgebraicGeometry
