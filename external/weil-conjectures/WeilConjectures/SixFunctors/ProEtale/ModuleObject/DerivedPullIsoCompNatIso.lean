/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.CompNatIsoCounit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPullMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralDerivedIso

/-!
# The derived (Pull) isomorphism is induced by the underived one

Let `a : Λ ⟶ Λ'` be a morphism of commutative condensed rings such that every coefficient change
`a_X : Λ_X ⟶ Λ'_X` is flat, and `f : X ⟶ Y` a morphism of schemes. The derived (Pull)
isomorphism `ProEtale.CondensedRing.derivedPullIso a f : Lf^*_Λ ⋙ L(Ext_{a_X}) ≅
L(Ext_{a_Y}) ⋙ Lf^*_Λ'`, defined as a conjugate along the derived adjunctions, is the
isomorphism of composites of left derived functors induced by the underived (Pull) isomorphism
`ProEtale.CondensedRing.pullIso a f` (`Functor.leftDerivedFunctorCompNatIso`), all four functors
being exact (`ProEtale.CondensedRing.derivedPullIso_eq_leftDerivedFunctorCompNatIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]
  [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **(Pull) is induced by the underived (Pull)**: for a flat coefficient change `a`, the derived
(Pull) isomorphism `Lf^*_Λ ⋙ L(Ext_{a_X}) ≅ L(Ext_{a_Y}) ⋙ Lf^*_Λ'` is the isomorphism of
composites of left derived functors induced by `pullIso a f`. -/
theorem derivedPullIso_eq_leftDerivedFunctorCompNatIso :
    derivedPullIso a f = Functor.leftDerivedFunctorCompNatIso
      (Mod.extendScalars (coefficientMap a Y)) (f)^*⟦Λ'⟧ (f)^*⟦Λ⟧
      (Mod.extendScalars (coefficientMap a X)) (pullIso a f) := by
  refine Iso.ext ((mateEquiv (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))).injective ?_)
  refine (mateEquiv_derivedPullIso_hom a f).trans ?_
  refine (Adjunction.mateEquiv_leftDerived_inv_eq
    (Mod.extendRestrictAdjunction (coefficientMap a Y))
    (Mod.extendRestrictAdjunction (coefficientMap a X))
    (pullIso a f).symm (comapUpperStarIso a f).symm (mateEquiv_pullIso_hom a f)
    (Functor.mapHomotopyCategoryCompNatIso (pullIso a f) _).symm
    (Functor.mapHomotopyCategoryCompNatIso_hom (pullIso a f) _)
    _ _ _ _ ((f)^*⟦Λ⟧.leftDerivedFunctorIsoMapDerivedCategory_hom_app_fac) _ _
    ((f)^*⟦Λ'⟧.leftDerivedFunctorIsoMapDerivedCategory_hom_app_fac)
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction_counit_app_Qh_eq (coefficientMap a Y))
    (Mod.derivedExtendMapDerivedCategoryAdjunction_counit_app_Qh_eq (coefficientMap a X))
    (Functor.leftDerivedFunctorCompNatIso (Mod.extendScalars (coefficientMap a Y)) (f)^*⟦Λ'⟧
      (f)^*⟦Λ⟧ (Mod.extendScalars (coefficientMap a X)) (pullIso a f)).symm _ rfl _ rfl
    (fun K ↦ ?_) _ rfl).symm
  simp only [Iso.symm_inv, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.mapHomotopyCategoryCompNatIso_hom, Category.assoc]
  exact Functor.leftDerivedFunctorCompNatIso_hom_app_comp_counit _ _ _ _ (pullIso a f) K

end AlgebraicGeometry.ProEtale.CondensedRing
