/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResiduePullSquareData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResidueOrdinaryRestrictPullComp
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars

/-! # Composition of restriction and derived pullback -/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
local instance instEssentiallySmallProfinite_integralResidueRestrictPullComp
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _
namespace AlgebraicGeometry.ProEtale.CondensedRing
attribute [local irreducible] Functor.leftDerivedFunctor Functor.mapDerivedCategory
  Functor.leftDerivedFunctorIsoMapDerivedCategory
  Functor.mapDerivedCategoryNatIso
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

set_option maxHeartbeats 800000 in
-- Instantiating naturality for the module-object derived squares repeats exactness searches.
/-- Restriction of scalars respects the canonical derived pullback composition.
Source: the coefficient-map composition identity and exact inverse image, as used in
Bhatt--Scholze, Remark 6.8.15.
(blueprint: new-integral-residue-restrict-pull-comp)

Proof. Apply the proved exact-derived square-pasting theorem to the ordinary
restriction-composition identity. Expand the exact-pullback identifications in the
left-derived composition maps. Cancel inverse pairs and use naturality of the
restriction square to transport the levelwise derived identity to the required
left-derived identity. No flatness of scalar reduction is used. -/
theorem residueExchangeRestrictPullIso_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (N : residueExchangeDerived
      (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) Z) :
    (residueExchangeUpperStarComp (integralCoeff ℓ E) f g).hom.app
        ((residueExchangeRestriction ℓ E Z).obj N) ≫
      (residueExchangeUpperStar (integralCoeff ℓ E) f).map
        ((residueExchangeRestrictPullIso ℓ E g).hom.app N) ≫
      (residueExchangeRestrictPullIso ℓ E f).hom.app
        ((residueExchangeUpperStar
          (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) g).obj N) =
    (residueExchangeRestrictPullIso ℓ E (f ≫ g)).hom.app N ≫
      (residueExchangeRestriction ℓ E X).map
        ((residueExchangeUpperStarComp
          (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f g).hom.app N) := by
  have H := Functor.mapDerivedCategorySquareIso_hom_app_comp
    (comapUpperStarIso (integralReductionMap ℓ E) g).symm
    (comapUpperStarIso (integralReductionMap ℓ E) f).symm
    (comapUpperStarIso (integralReductionMap ℓ E) (f ≫ g)).symm
    (upperStarComp (integralCoeff ℓ E) f g)
    (upperStarComp (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f g)
    (fun M ↦ (integralResidue_ordinaryRestrictPull_comp ℓ E f g M).symm) N
  have HD :
      (derivedComapUpperStarIso (integralReductionMap ℓ E) (f ≫ g)).inv.app N ≫
        (residueExchangeRestriction ℓ E X).map
          ((Functor.mapDerivedCategoryTriangleIso
            (upperStarComp
              (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f g)).hom.app N) =
      (Functor.mapDerivedCategoryTriangleIso
        (upperStarComp (integralCoeff ℓ E) f g)).hom.app
          ((residueExchangeRestriction ℓ E Z).obj N) ≫
        D((f)^*⟦integralCoeff ℓ E⟧).map
          ((derivedComapUpperStarIso (integralReductionMap ℓ E) g).inv.app N) ≫
        (derivedComapUpperStarIso (integralReductionMap ℓ E) f).inv.app
          (D((g)^*⟦Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)⟧).obj N) := by
    simpa only [derivedComapUpperStarIso, Functor.mapDerivedCategorySquareIso,
      Iso.trans_inv, Iso.symm_inv, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.mapDerivedCategoryNatIso_symm, residueExchangeRestriction,
      Functor.map_comp, Category.assoc] using H
  have hnat := (derivedComapUpperStarIso (integralReductionMap ℓ E) f).inv.naturality
    ((leftDerivedUpperStarIsoMapDerivedCategory
      (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) g).inv.app N)
  simp only [Functor.comp_map, leftDerivedUpperStarIsoMapDerivedCategory] at hnat
  unfold residueExchangeUpperStarComp residueExchangeRestrictPullIso residueExchangeUpperStar
  dsimp only [id_eq]
  simp only [leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, leftDerivedUpperStarIsoMapDerivedCategory,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.map_comp,
    Functor.comp_obj, Category.assoc]
  simp only [residueExchangeRestriction, Iso.inv_hom_id_app_assoc,
    ← NatTrans.naturality_assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hnat]
  simp only [Functor.mapDerivedCategoryTriangleIso, Iso.trans_hom,
    NatTrans.comp_app, Iso.symm_hom, Functor.map_comp, Category.assoc,
    residueExchangeRestriction] at HD
  rw [← reassoc_of% HD]

end AlgebraicGeometry.ProEtale.CondensedRing
