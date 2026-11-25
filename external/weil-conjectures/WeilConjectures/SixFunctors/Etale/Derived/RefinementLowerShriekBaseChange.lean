/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded

/-!
# The base change of the extension by zero along a refinement is a mate

For open immersions `j : X ⟶ C`, `k : X ⟶ D` and `q : C ⟶ D` with `j ≫ q = k`, the base change
comparison `j_! ⟶ k_! ⋙ q^*` (`AlgebraicGeometry.Etale.openImmersionLowerShriekBaseChange`) is
the mate of the composition isomorphism `k^* ≅ q^* ⋙ j^*`
(`AlgebraicGeometry.Etale.unit_map_openImmersionLowerShriekBaseChange_app`), and so is its
derived version for a refinement of compactifications
(`AlgebraicGeometry.Etale.unit_map_refinementLowerShriekBaseChangeDerivedIso`).
-/

@[expose] public section

universe u' u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

namespace Etale

section Underived

variable {X C D : Scheme.{u}} (j : X ⟶ C) [IsOpenImmersion j] (q : C ⟶ D) (k : X ⟶ D)
  [IsOpenImmersion k] (hk : j ≫ q = k)

omit [HasSmallSiteSheafify A] in
/-- The transpose of the base change comparison `j_! ⟶ k_! ⋙ q^*` under `j_! ⊣ j^*` is the unit
of `k_! ⊣ k^*` followed by the composition isomorphism `k^* ≅ q^* ⋙ j^*`. -/
@[reassoc]
lemma unit_map_openImmersionLowerShriekBaseChange_app (F : Sheaf X.smallEtaleTopology A) :
    (openImmersionLowerShriekUpperStarAdjunction A j).unit.app F ≫
        (j)^*[A].map ((openImmersionLowerShriekBaseChange A j q k hk).app F) =
      (openImmersionLowerShriekUpperStarAdjunction A k).unit.app F ≫
        (upperStarCompIso A j q k hk).hom.app ((k)_!open[A].obj F) := by
  have h := unit_conjugateEquiv_symm ((openImmersionLowerShriekUpperStarAdjunction A k).comp
      (upperStarLowerStarAdjunction A q)) (openImmersionLowerShriekUpperStarAdjunction A j)
    (upperStarBaseChange A j q k hk) F
  rw [openImmersionLowerShriekBaseChange, ← h]
  simp only [Adjunction.comp_unit_app, upperStarBaseChange, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_inv_app,
    Functor.leftUnitor_hom_app, Functor.comp_obj, Category.assoc,
    Category.id_comp]
  have hn := (upperStarCompIso A j q k hk).hom.naturality
    ((upperStarLowerStarAdjunction A q).unit.app ((k)_!open[A].obj F))
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn
  rw [reassoc_of% hn]
  erw [Category.comp_id, ← CategoryTheory.Functor.map_comp, Adjunction.left_triangle_components,
    CategoryTheory.Functor.map_id, Category.comp_id]

end Underived

section Derived

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)

/-- The derived base change isomorphism `D(c.i)_! ≅ D(d.i)_! ⋙ Dq^*` of a refinement is the mate
of the isomorphism `D(d.i^*) ≅ Dq^* ⋙ D(c.i^*)` induced by the composition isomorphism. -/
lemma unit_map_refinementLowerShriekBaseChangeDerivedIso (hcart : IsPullback c.i (𝟙 X) r.hom d.i)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (derivedOpenImmersionLowerShriekUpperStarAdjunction A c.i).unit.app K ≫
        D((c.i)^*[A]).map ((refinementLowerShriekBaseChangeDerivedIso A r hcart).hom.app K) =
      (derivedOpenImmersionLowerShriekUpperStarAdjunction A d.i).unit.app K ≫
        (Functor.mapDerivedCategoryTriangleIso
          (upperStarCompIso A c.i r.hom d.i r.i_hom)).hom.app (D((d.i)_!open[A]).obj K) :=
  haveI := r.isIso_openImmersionLowerShriekBaseChange A hcart
  Adjunction.mapDerivedCategoryAdjunction_mate' (openImmersionLowerShriekUpperStarAdjunction A d.i)
    (openImmersionLowerShriekUpperStarAdjunction A c.i)
    (upperStarCompIso A c.i r.hom d.i r.i_hom) (asIso (r.openImmersionLowerShriekBaseChange A))
    (unit_map_openImmersionLowerShriekBaseChange_app A c.i r.hom d.i r.i_hom) K


omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [HasSmallSiteSheafify A] in
lemma upperStarCompIso_eq {X C D : Scheme.{u}} (j : X ⟶ C) (q : C ⟶ D) (k : X ⟶ D)
    (hk : j ≫ q = k) :
    upperStarCompIso A j q k hk = upperStarComp A j q k hk.symm := by
  subst hk
  simp

/-- The square map `D(d.i^*) ⟶ Lq^* ⋙ D(c.i^*)` of a refinement, induced by the composition
isomorphism `d.i^* ≅ q^* ⋙ c.i^*` and read through `Lq^* ≅ Dq^*`. -/
noncomputable def refinementSquareMap :
    D((d.i)^*[A]) ⟶ L((r.hom)^*[A]) ⋙ D((c.i)^*[A]) :=
  (Functor.mapDerivedCategoryTriangleIso (upperStarCompIso A c.i r.hom d.i r.i_hom)).hom ≫
    Functor.whiskerRight (leftDerivedUpperStarIsoMapDerivedCategory A r.hom).inv D((c.i)^*[A])

omit [HasSmallSiteSheafify A] in
/-- The square map of a refinement is the composition isomorphism
`L(d.i)^* ≅ Lq^* ⋙ L(c.i)^*` of the derived pullbacks, read through `Lj^* ≅ Dj^*`. -/
lemma refinementSquareMap_app (Y : DerivedCategory (Sheaf d.Z.smallEtaleTopology A)) :
    (refinementSquareMap A r).app Y =
      (leftDerivedUpperStarIsoMapDerivedCategory A d.i).inv.app Y ≫
        (leftDerivedUpperStarComp A c.i r.hom d.i r.i_hom.symm).hom.app Y ≫
        (leftDerivedUpperStarIsoMapDerivedCategory A c.i).hom.app (L((r.hom)^*[A]).obj Y) := by
  simp only [refinementSquareMap, upperStarCompIso_eq, leftDerivedUpperStarComp,
    Functor.leftDerivedFunctorNatIso, Functor.leftDerivedFunctorCompIso,
    leftDerivedUpperStarIsoMapDerivedCategory, Iso.trans_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [Iso.inv_hom_id_app]
  erw [Category.comp_id]
end Derived

end Etale

end AlgebraicGeometry
