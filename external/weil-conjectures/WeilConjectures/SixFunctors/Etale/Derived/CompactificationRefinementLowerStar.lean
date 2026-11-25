/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.CompactificationLowerStarBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement
public import WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence

/-!
# Forget-supports maps and refinements of compactifications

For a refinement `r : c.Refinement d` of compactifications of `f`, the comparison
`Rf_!(d) ⟶ Rf_!(c)` intertwines the forget-supports maps `Rf_!(c) ⟶ Rf_*` and
`Rf_!(d) ⟶ Rf_*`.
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

/-- The transpose of the composition map `Rg₁_* ⋙ Rg₂_* ⟶ Rg₁₂_*` under `Lg₁₂^* ⊣ Rg₁₂_*`. -/
@[reassoc]
lemma map_rightDerivedLowerStarCompHom_app_counit {T S R : Scheme.{u}} (g₁ : T ⟶ S) (g₂ : S ⟶ R)
    (g₁₂ : T ⟶ R) (hg : g₁₂ = g₁ ≫ g₂) (N : DerivedCategory (Sheaf T.smallEtaleTopology A)) :
    L((g₁₂)^*[A]).map ((rightDerivedLowerStarCompHom A g₁ g₂ g₁₂ hg).app N) ≫
        (derivedUpperStarLowerStarAdjunction A g₁₂).counit.app N =
      (leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).hom.app (R((g₂)_*[A]).obj (R((g₁)_*[A]).obj N)) ≫
        L((g₁)^*[A]).map ((derivedUpperStarLowerStarAdjunction A g₂).counit.app
          (R((g₁)_*[A]).obj N)) ≫
        (derivedUpperStarLowerStarAdjunction A g₁).counit.app N := by
  have h := conjugateEquiv_counit ((derivedUpperStarLowerStarAdjunction A g₂).comp
      (derivedUpperStarLowerStarAdjunction A g₁)) (derivedUpperStarLowerStarAdjunction A g₁₂)
    (leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).hom N
  simp only [Adjunction.comp_counit_app] at h
  exact h

section Assoc

variable {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (fg : W ⟶ Y) (gh : X ⟶ Z)
  (fgh : W ⟶ Z) (hfg : fg = f ≫ g) (hgh : gh = g ≫ h) (hfgh : fgh = fg ≫ h)

/-- **Associativity of the composition maps of derived pushforwards.** -/
lemma rightDerivedLowerStarCompHom_assoc_app (M : DerivedCategory (Sheaf W.smallEtaleTopology A)) :
    (rightDerivedLowerStarCompHom A g h gh hgh).app (R((f)_*[A]).obj M) ≫
        (rightDerivedLowerStarCompHom A f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])).app M =
      R((h)_*[A]).map ((rightDerivedLowerStarCompHom A f g fg hfg).app M) ≫
        (rightDerivedLowerStarCompHom A fg h fgh hfgh).app M := by
  apply ((derivedUpperStarLowerStarAdjunction A fgh).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [map_rightDerivedLowerStarCompHom_app_counit, map_rightDerivedLowerStarCompHom_app_counit]
  have n₁ := (leftDerivedUpperStarComp A f gh fgh
    (by rw [hfgh, hfg, hgh, Category.assoc])).hom.naturality
    ((rightDerivedLowerStarCompHom A g h gh hgh).app (R((f)_*[A]).obj M))
  have n₂ := (leftDerivedUpperStarComp A fg h fgh hfgh).hom.naturality
    (R((h)_*[A]).map ((rightDerivedLowerStarCompHom A f g fg hfg).app M))
  simp only [Functor.comp_map] at n₁ n₂
  rw [reassoc_of% n₁, reassoc_of% n₂, ← Functor.map_comp_assoc,
    map_rightDerivedLowerStarCompHom_app_counit]
  have n₃ : L((h)^*[A]).map (R((h)_*[A]).map ((rightDerivedLowerStarCompHom A f g fg hfg).app M)) ≫
      (derivedUpperStarLowerStarAdjunction A h).counit.app (R((fg)_*[A]).obj M) =
      (derivedUpperStarLowerStarAdjunction A h).counit.app
        (R((g)_*[A]).obj (R((f)_*[A]).obj M)) ≫
        (rightDerivedLowerStarCompHom A f g fg hfg).app M :=
    (derivedUpperStarLowerStarAdjunction A h).counit.naturality _
  rw [← Functor.map_comp_assoc (L((fg)^*[A])), n₃, Functor.map_comp (L((fg)^*[A]))]
  simp only [Category.assoc]
  rw [map_rightDerivedLowerStarCompHom_app_counit]
  have n₄ := (leftDerivedUpperStarComp A f g fg hfg).hom.naturality
    ((derivedUpperStarLowerStarAdjunction A h).counit.app (R((g)_*[A]).obj (R((f)_*[A]).obj M)))
  simp only [Functor.comp_map] at n₄
  rw [reassoc_of% n₄, ← leftDerivedUpperStarComp_assoc'_app_assoc A f g h fg gh fgh hfg hgh hfgh]
  simp only [Functor.map_comp, Category.assoc]

end Assoc

/-- The transpose of the comparison `D(j_!) ⟶ Rj_*` under `Lj^* ⊣ Rj_*` is the inverse of the
unit of `D(j_!) ⊣ D(j^*)`, read through `Lj^* ≅ D(j^*)`. -/
lemma map_derivedOpenImmersionLowerShriekToLowerStar_app_counit {U Z : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] (K : DerivedCategory (Sheaf U.smallEtaleTopology A)) :
    L((j)^*[A]).map ((derivedOpenImmersionLowerShriekToLowerStar A j).app K) ≫
        (derivedUpperStarLowerStarAdjunction A j).counit.app K =
      (leftDerivedUpperStarIsoMapDerivedCategory A j).hom.app (D((j)_!open[A]).obj K) ≫
        inv ((derivedOpenImmersionLowerShriekUpperStarAdjunction A j).unit.app K) := by
  have hε : (mapDerivedUpperStarLowerStarAdjunction A j).counit.app K =
      (leftDerivedUpperStarIsoMapDerivedCategory A j).inv.app (R((j)_*[A]).obj K) ≫
        (derivedUpperStarLowerStarAdjunction A j).counit.app K := by
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
  have n := (leftDerivedUpperStarIsoMapDerivedCategory A j).inv.naturality
    ((derivedOpenImmersionLowerShriekToLowerStar A j).app K)
  rw [hε, reassoc_of% n] at hT
  rw [← hT, Iso.hom_inv_id_app_assoc]

section Refinement

variable [HasSmallSiteSheafify A] {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f}
  (r : c.Refinement d) (hcart : IsPullback c.i (𝟙 X) r.hom d.i)

/-- **The comparison `D(j_!) ⟶ Rj_*` along a refinement**: for `q = r.hom`, the unit of
`Lq^* ⊣ Rq_*` at `D(d.i)_! M`, followed by `Rq_*` of the base change `Lq^* D(d.i)_! ≅ D(c.i)_!`
and of the comparison of `c.i`, and by the composition map `R(c.i)_* ⋙ Rq_* ⟶ R(d.i)_*`, is the
comparison `D(d.i)_! ⟶ R(d.i)_*`. -/
lemma refinement_derivedOpenImmersionLowerShriekToLowerStar_app
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (derivedUpperStarLowerStarAdjunction A r.hom).unit.app (D((d.i)_!open[A]).obj M) ≫
        R((r.hom)_*[A]).map ((leftDerivedUpperStarIsoMapDerivedCategory A r.hom).hom.app _ ≫
          (refinementLowerShriekBaseChangeDerivedIso A r hcart).inv.app M ≫
          (derivedOpenImmersionLowerShriekToLowerStar A c.i).app M) ≫
        (rightDerivedLowerStarCompHom A c.i r.hom d.i r.i_hom.symm).app M =
      (derivedOpenImmersionLowerShriekToLowerStar A d.i).app M := by
  apply ((derivedUpperStarLowerStarAdjunction A d.i).homEquiv _ _).symm.injective
  have hx := ((derivedUpperStarLowerStarAdjunction A r.hom).homEquiv_unit
    (D((d.i)_!open[A]).obj M) (R((c.i)_*[A]).obj M)
    ((leftDerivedUpperStarIsoMapDerivedCategory A r.hom).hom.app (D((d.i)_!open[A]).obj M) ≫
      (refinementLowerShriekBaseChangeDerivedIso A r hcart).inv.app M ≫
      (derivedOpenImmersionLowerShriekToLowerStar A c.i).app M)).symm
  rw [← Category.assoc]
  erw [hx]
  simp only [Adjunction.homEquiv_counit]
  rw [Functor.map_comp, Category.assoc, map_rightDerivedLowerStarCompHom_app_counit,
    map_derivedOpenImmersionLowerShriekToLowerStar_app_counit]
  have n := (leftDerivedUpperStarComp A c.i r.hom d.i r.i_hom.symm).hom.naturality
    (((derivedUpperStarLowerStarAdjunction A r.hom).homEquiv (D((d.i)_!open[A]).obj M)
      (R((c.i)_*[A]).obj M))
        ((leftDerivedUpperStarIsoMapDerivedCategory A r.hom).hom.app (D((d.i)_!open[A]).obj M) ≫
          (refinementLowerShriekBaseChangeDerivedIso A r hcart).inv.app M ≫
          (derivedOpenImmersionLowerShriekToLowerStar A c.i).app M))
  simp only [Functor.comp_map] at n
  have t := ((derivedUpperStarLowerStarAdjunction A r.hom).homEquiv_counit
    (D((d.i)_!open[A]).obj M) (R((c.i)_*[A]).obj M)
    (((derivedUpperStarLowerStarAdjunction A r.hom).homEquiv (D((d.i)_!open[A]).obj M)
      (R((c.i)_*[A]).obj M))
        ((leftDerivedUpperStarIsoMapDerivedCategory A r.hom).hom.app (D((d.i)_!open[A]).obj M) ≫
          (refinementLowerShriekBaseChangeDerivedIso A r hcart).inv.app M ≫
          (derivedOpenImmersionLowerShriekToLowerStar A c.i).app M)))
  rw [Equiv.symm_apply_apply] at t
  rw [reassoc_of% n, ← Functor.map_comp_assoc]
  erw [← t]
  simp only [Functor.map_comp, Category.assoc]
  rw [map_derivedOpenImmersionLowerShriekToLowerStar_app_counit]
  have n₁ := (leftDerivedUpperStarIsoMapDerivedCategory A c.i).hom.naturality
    ((refinementLowerShriekBaseChangeDerivedIso A r hcart).inv.app M)
  have n₂ := (leftDerivedUpperStarIsoMapDerivedCategory A c.i).hom.naturality
    ((leftDerivedUpperStarIsoMapDerivedCategory A r.hom).hom.app (D((d.i)_!open[A]).obj M))
  have sq₂ : (leftDerivedUpperStarComp A c.i r.hom d.i r.i_hom.symm).hom.app
      (D((d.i)_!open[A]).obj M) ≫ (leftDerivedUpperStarIsoMapDerivedCategory A c.i).hom.app
        (L((r.hom)^*[A]).obj (D((d.i)_!open[A]).obj M)) =
      (leftDerivedUpperStarIsoMapDerivedCategory A d.i).hom.app (D((d.i)_!open[A]).obj M) ≫
        (refinementSquareMap A r).app (D((d.i)_!open[A]).obj M) := by
    rw [refinementSquareMap_app, Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% n₁, reassoc_of% n₂, reassoc_of% sq₂]
  congr 1
  simp only [refinementSquareMap, NatTrans.comp_app, Functor.whiskerRight_app, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]
  rw [← cancel_epi ((derivedOpenImmersionLowerShriekUpperStarAdjunction A d.i).unit.app M),
    IsIso.hom_inv_id,
    ← reassoc_of% (unit_map_refinementLowerShriekBaseChangeDerivedIso A r hcart M),
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    IsIso.hom_inv_id]
  rfl

/-- **The comparison along a refinement commutes with the forget-supports maps**: the comparison
`Rf_!(d) ⟶ Rf_!(c)` followed by the forget-supports map `Rf_!(c) ⟶ R(c.g)_* R(c.i)_* ⟶ Rf_*` of
`c` is the forget-supports map of `d`. -/
lemma rightDerivedLowerShriekOfCompactificationComparison_app_comp_toLowerStar
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (rightDerivedLowerShriekOfCompactificationComparison A r hcart).app M ≫
        R((c.g)_*[A]).map ((derivedOpenImmersionLowerShriekToLowerStar A c.i).app M) ≫
        (rightDerivedLowerStarCompHom A c.i c.g f c.comm).app M =
      R((d.g)_*[A]).map ((derivedOpenImmersionLowerShriekToLowerStar A d.i).app M) ≫
        (rightDerivedLowerStarCompHom A d.i d.g f d.comm).app M := by
  rw [rightDerivedLowerShriekOfCompactificationComparison_app]
  have n := (rightDerivedLowerStarCompHom A r.hom d.g c.g r.hom_g.symm).naturality
    ((derivedOpenImmersionLowerShriekToLowerStar A c.i).app M)
  simp only [Functor.comp_map] at n
  simp only [Category.assoc]
  rw [← reassoc_of% n, rightDerivedLowerStarCompHom_assoc_app A c.i r.hom d.g d.i c.g f
    r.i_hom.symm r.hom_g.symm d.comm]
  simp only [← Functor.map_comp_assoc]
  rw [← refinement_derivedOpenImmersionLowerShriekToLowerStar_app A r hcart M]
  simp only [Category.assoc]

end Refinement

section Independence

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Y : Scheme.{u}} {f : X ⟶ Y}
  [QuasiCompact f]

/-- **The forget-supports maps do not depend on the compactification**: the comparison
isomorphism `Rf_!(c) ≅ Rf_!(d)` followed by the forget-supports map of `d` is the
forget-supports map of `c`. -/
lemma rightDerivedLowerShriekOfCompactificationIso_hom_app_comp_toLowerStar
    (c d : Compactification f) (M : DerivedCategory (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerShriekOfCompactificationIso Λ c d).hom.app M ≫
        R((d.g)_*[ModuleCat.{u + 1} Λ]).map
          ((derivedOpenImmersionLowerShriekToLowerStar _ d.i).app M) ≫
        (rightDerivedLowerStarCompHom _ d.i d.g f d.comm).app M =
      R((c.g)_*[ModuleCat.{u + 1} Λ]).map
          ((derivedOpenImmersionLowerShriekToLowerStar _ c.i).app M) ≫
        (rightDerivedLowerStarCompHom _ c.i c.g f c.comm).app M := by
  simp only [rightDerivedLowerShriekOfCompactificationIso, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    asIso_hom, NatTrans.comp_app, Category.assoc]
  rw [← rightDerivedLowerShriekOfCompactificationComparison_app_comp_toLowerStar _
      (Compactification.infSnd c d) (Compactification.isPullback_infSnd c d) M,
    ← NatTrans.comp_app_assoc (inv (rightDerivedLowerShriekOfCompactificationComparison _
      (Compactification.infSnd c d) (Compactification.isPullback_infSnd c d))),
    IsIso.inv_hom_id, NatTrans.id_app, Category.id_comp,
    rightDerivedLowerShriekOfCompactificationComparison_app_comp_toLowerStar]

end Independence

end Etale

end AlgebraicGeometry
