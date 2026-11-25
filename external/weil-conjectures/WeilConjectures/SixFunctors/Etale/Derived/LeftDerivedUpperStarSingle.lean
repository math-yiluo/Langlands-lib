/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

/-!
# The composition isomorphisms of derived pullbacks on sheaves placed in degree zero

On a sheaf `W` placed in degree zero, the composition isomorphism
`L(g ≫ h)^* ≅ Lh^* ⋙ Lg^*` of derived pullbacks (`AlgebraicGeometry.Etale.leftDerivedUpperStarComp`)
is the composition isomorphism `(g ≫ h)^* ≅ h^* ⋙ g^*` of the pullbacks of sheaves
(`AlgebraicGeometry.Etale.upperStarComp`), through the identifications `Lg^*(F[0]) ≅ (g^* F)[0]`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarComp_hom_app_singleFunctor`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- On sheaves placed in degree zero, the composition isomorphism of derived pullbacks is the
composition isomorphism of the pullbacks of sheaves. -/
lemma leftDerivedUpperStarComp_hom_app_singleFunctor {X Y Z : Scheme.{u}} (g : X ⟶ Y)
    (h : Y ⟶ Z) (gh : X ⟶ Z) (hgh : gh = g ≫ h) (W : Sheaf Z.smallEtaleTopology A) :
    (leftDerivedUpperStarComp A g h gh hgh).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj W) ≫
      (L((g)^*[A])).map ((singleFunctorCompLeftDerivedUpperStarIso A h).hom.app W) ≫
        (singleFunctorCompLeftDerivedUpperStarIso A g).hom.app ((h)^*[A].obj W) =
      (singleFunctorCompLeftDerivedUpperStarIso A gh).hom.app W ≫
        (DerivedCategory.singleFunctor _ 0).map ((upperStarComp A g h gh hgh).hom.app W) := by
  have key := Functor.mapDerivedCategoryNatIso_comp_hom_app_singleFunctor (h)^*[A] (g)^*[A]
    (gh)^*[A] (upperStarComp A g h gh hgh) W
  have hε := ((g)^*[A].leftDerivedFunctorIsoMapDerivedCategory).hom.naturality
    ((h)^*[A].leftDerivedFunctorIsoMapDerivedCategory.hom.app
      ((DerivedCategory.singleFunctor _ 0).obj W) ≫
      ((h)^*[A].mapDerivedCategorySingleFunctor 0).hom.app W)
  simp only [leftDerivedUpperStarComp, singleFunctorCompLeftDerivedUpperStarIso,
    Functor.singleFunctorCompLeftDerivedFunctorIso, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Iso.symm_hom, Category.assoc, Functor.comp_obj] at hε ⊢
  rw [Iso.inv_hom_id_app_assoc, reassoc_of% hε, Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app_assoc, key]

/-- For `f : X ⟶ Y` and `π_X = f ≫ π_Y`, a morphism `Θ : f^* B_Y ⟶ B_X` compatible with
morphisms `σ_Y : π_Y^* W ⟶ B_Y` and `σ_X : π_X^* W ⟶ B_X` induces, on the derived pullbacks of
`W` placed in degree zero, the inverse of the composition isomorphism of derived pullbacks. -/
lemma leftDerivedUpperStar_map_singleFunctor_comp {S X Y : Scheme.{u}} (f : X ⟶ Y)
    (πY : Y ⟶ S) (πX : X ⟶ S) (hπ : πX = f ≫ πY) (W : Sheaf S.smallEtaleTopology A)
    {BY : Sheaf Y.smallEtaleTopology A} {BX : Sheaf X.smallEtaleTopology A}
    (σY : (πY)^*[A].obj W ⟶ BY) (σX : (πX)^*[A].obj W ⟶ BX) (Θ : (f)^*[A].obj BY ⟶ BX)
    (hΘ : (upperStarComp A f πY πX hπ).hom.app W ≫ (f)^*[A].map σY ≫ Θ = σX) :
    (L((f)^*[A])).map ((singleFunctorCompLeftDerivedUpperStarIso A πY).hom.app W ≫
        (DerivedCategory.singleFunctor _ 0).map σY) ≫
        (singleFunctorCompLeftDerivedUpperStarIso A f).hom.app BY ≫
          (DerivedCategory.singleFunctor _ 0).map Θ =
      (leftDerivedUpperStarComp A f πY πX hπ).inv.app _ ≫
        (singleFunctorCompLeftDerivedUpperStarIso A πX).hom.app W ≫
          (DerivedCategory.singleFunctor _ 0).map σX := by
  subst hΘ
  rw [← cancel_epi ((leftDerivedUpperStarComp A f πY πX hπ).hom.app _), Iso.hom_inv_id_app_assoc]
  have D1 := leftDerivedUpperStarComp_hom_app_singleFunctor A f πY πX hπ W
  have n := (singleFunctorCompLeftDerivedUpperStarIso A f).hom.naturality σY
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc] at n D1 ⊢
  rw [reassoc_of% n, reassoc_of% D1]

end AlgebraicGeometry.Etale
