/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
public import WeilConjectures.CategoryTheory.DerivedCategory.Shift.IdIso
public import WeilConjectures.CategoryTheory.Shift.RestrictFullyFaithful
public import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarShift

/-!
# The derived pullback and pushforward of module objects commute with the shifts

On the unbounded derived categories of module objects over a condensed ring `Λ` on the
pro-étale sites, the derived pullback `L((f)^*⟦Λ⟧)` carries the shift structure of the levelwise
functor `D((f)^*⟦Λ⟧)` (`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarShift`)
and the derived pushforward `R((f)_*⟦Λ⟧)` the shift structure making the derived adjunction
`Lf^* ⊣ Rf_*` commute with the shifts
(`ProEtale.CondensedRing.commShift_derivedUpperStarLowerStarAdjunction`, in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing`). This file shows that
the remaining structural isomorphisms and adjunctions commute with the shifts:

* the composition and identity isomorphisms of the derived pullbacks
  (`ProEtale.CondensedRing.commShift_leftDerivedUpperStarComp_hom`,
  `ProEtale.CondensedRing.commShift_leftDerivedUpperStarId_hom`);
* the derived adjunction `D(j_!) ⊣ Lj^*` of an open immersion and the identity isomorphism of
  the extension by zero along the identity.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

section UpperStar

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y)

/-- The identification `L((f)^*⟦Λ⟧) ≅ D((f)^*⟦Λ⟧)` is compatible with the shifts. -/
instance commShift_leftDerivedUpperStarIsoMapDerivedCategory_hom :
    NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory Λ f).hom ℤ :=
  NatTrans.CommShift.of_iso_inv (leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm ℤ

/-- The composition isomorphism `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` commutes with the shifts. -/
instance commShift_leftDerivedUpperStarComp_hom (g : Y ⟶ Z) :
    NatTrans.CommShift (leftDerivedUpperStarComp Λ f g).hom ℤ := by
  have e : (leftDerivedUpperStarComp Λ f g).hom =
      (leftDerivedUpperStarIsoMapDerivedCategory Λ (f ≫ g)).hom ≫
        (Functor.mapDerivedCategoryNatIso (upperStarComp Λ f g)).hom ≫
        ((g)^*⟦Λ⟧.mapDerivedCategoryCompIso (f)^*⟦Λ⟧).inv ≫
        Functor.whiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ g).inv
          D((f)^*⟦Λ⟧) ≫
        Functor.whiskerLeft L((g)^*⟦Λ⟧) (leftDerivedUpperStarIsoMapDerivedCategory Λ f).inv := by
    simp [leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
      Functor.leftDerivedFunctorCompIso, leftDerivedUpperStarIsoMapDerivedCategory]
  rw [e]
  infer_instance

/-- The identity isomorphism `L(𝟙 X)^* ≅ 𝟭` commutes with the shifts. -/
instance commShift_leftDerivedUpperStarId_hom (X : Scheme.{u}) :
    NatTrans.CommShift (leftDerivedUpperStarId Λ X).hom ℤ := by
  have e : (leftDerivedUpperStarId Λ X).hom =
      (leftDerivedUpperStarIsoMapDerivedCategory Λ (𝟙 X)).hom ≫
        (Functor.mapDerivedCategoryNatIso (upperStarId Λ X)).hom ≫
        (Functor.mapDerivedCategoryIdIso _).hom := by
    simp [leftDerivedUpperStarId, Functor.leftDerivedFunctorNatIso,
      leftDerivedUpperStarIsoMapDerivedCategory]
  rw [e]
  infer_instance

end UpperStar

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The derived adjunction `D(j_!) ⊣ Lj^*` of an open immersion, the levelwise adjunction
`D(j_!) ⊣ D(j^*)` transported along `D(j^*) ≅ Lj^*`, commutes with the shifts. -/
instance commShift_derivedOpenImmersionLowerShriekUpperStarAdjunction_ofNatIsoRight :
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ j).symm).CommShift ℤ := by
  have : NatTrans.CommShift
      (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ j).symm.hom ℤ :=
    Functor.CommShift.ofIso_compatibility (leftDerivedUpperStarIsoMapDerivedCategory Λ j).symm ℤ
  have : (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).CommShift ℤ :=
    (openImmersionLowerShriekUpperStarAdjunction Λ j).commShift_mapDerivedCategoryAdjunction
  exact Adjunction.commShift_ofNatIsoRight _ _

end OpenImmersion

end AlgebraicGeometry.ProEtale.CondensedRing
