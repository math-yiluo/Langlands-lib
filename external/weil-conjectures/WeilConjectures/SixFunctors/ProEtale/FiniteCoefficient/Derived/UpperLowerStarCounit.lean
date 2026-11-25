/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryCounit
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar

/-!
# The identity and composition isomorphisms of `Lg^*` on the homotopy category

The identity isomorphism `L(𝟙 X)^* ≅ 𝟭` and the composition isomorphisms
`L(g₁ ≫ g₂)^* ≅ Lg₂^* ⋙ Lg₁^*` of the derived pullbacks of pro-étale sheaves are compatible with
the counits `Qh ⋙ Lg^* ⟶ g^* ⋙ Qh` of the left derived functors: on the image of an object of the
homotopy category they are induced by `ProEtale.upperStarId` and `ProEtale.upperStarComp`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- On `Qh K`, the identity isomorphism `L(𝟙 X)^* ≅ 𝟭` is the counit of `L(𝟙 X)^*` followed by
`ProEtale.upperStarId`. -/
lemma leftDerivedUpperStarId_hom_app_Qh (X : Scheme.{u})
    (K : HomotopyCategory (Sheaf (ProEt.topology X) A) (.up ℤ)) :
    (leftDerivedUpperStarId A X).hom.app (DerivedCategory.Qh.obj K) =
      ((𝟙 X)^*[A]).leftDerivedFunctorCounit.app K ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory (ProEtale.upperStarId A X).hom (.up ℤ)).app K) := by
  have h := Functor.leftDerivedFunctorNatIso_hom_app_Qh _ (ProEtale.upperStarId A X) K
  rw [← h, leftDerivedUpperStarId, Iso.trans_hom, NatTrans.comp_app,
    Functor.leftDerivedFunctorIsoMapDerivedCategory_trans_mapDerivedCategoryIdIso_hom_app_Qh]

/-- On `Qh K`, the composition isomorphism `L(g₁ ≫ g₂)^* ≅ Lg₂^* ⋙ Lg₁^*` followed by the counits
of `Lg₂^*` and `Lg₁^*` is the counit of `L(g₁ ≫ g₂)^*` followed by `ProEtale.upperStarComp`. -/
@[reassoc]
lemma leftDerivedUpperStarComp_hom_app_Qh {T S R : Scheme.{u}} (g₁ : T ⟶ S) (g₂ : S ⟶ R)
    (K : HomotopyCategory (Sheaf (ProEt.topology R) A) (.up ℤ)) :
    (leftDerivedUpperStarComp A g₁ g₂).hom.app (DerivedCategory.Qh.obj K) ≫
        L((g₁)^*[A]).map (((g₂)^*[A]).leftDerivedFunctorCounit.app K) ≫
        ((g₁)^*[A]).leftDerivedFunctorCounit.app
          (((g₂)^*[A].mapHomotopyCategory (.up ℤ)).obj K) =
      ((g₁ ≫ g₂)^*[A]).leftDerivedFunctorCounit.app K ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory (ProEtale.upperStarComp A g₁ g₂).hom (.up ℤ)).app K) := by
  rw [leftDerivedUpperStarComp, Iso.trans_hom, NatTrans.comp_app, Category.assoc,
    Functor.leftDerivedFunctorCompIso_hom_app_Qh, Functor.leftDerivedFunctorNatIso_hom_app_Qh]

/-- The inverse form of `leftDerivedUpperStarComp_hom_app_Qh`. -/
@[reassoc]
lemma leftDerivedUpperStarComp_inv_app_Qh {T S R : Scheme.{u}} (g₁ : T ⟶ S) (g₂ : S ⟶ R)
    (K : HomotopyCategory (Sheaf (ProEt.topology R) A) (.up ℤ)) :
    (leftDerivedUpperStarComp A g₁ g₂).inv.app (DerivedCategory.Qh.obj K) ≫
        ((g₁ ≫ g₂)^*[A]).leftDerivedFunctorCounit.app K =
      L((g₁)^*[A]).map (((g₂)^*[A]).leftDerivedFunctorCounit.app K) ≫
        ((g₁)^*[A]).leftDerivedFunctorCounit.app
          (((g₂)^*[A].mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory (ProEtale.upperStarComp A g₁ g₂).inv (.up ℤ)).app K) := by
  rw [← cancel_epi ((leftDerivedUpperStarComp A g₁ g₂).hom.app (DerivedCategory.Qh.obj K)),
    Iso.hom_inv_id_app_assoc, leftDerivedUpperStarComp_hom_app_Qh_assoc]
  erw [← Functor.map_comp, ← NatTrans.comp_app, ← NatTrans.mapHomotopyCategory_comp,
    Iso.hom_inv_id, NatTrans.mapHomotopyCategory_id, NatTrans.id_app,
    CategoryTheory.Functor.map_id,
    Category.comp_id]

end AlgebraicGeometry.ProEtale
