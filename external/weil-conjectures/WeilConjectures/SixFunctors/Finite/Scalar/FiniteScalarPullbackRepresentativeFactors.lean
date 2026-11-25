/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarOrdinaryPullbackComparison
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryCounit
import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarPullbackRepresentativeFactorsFactorized
import all Mathlib.Algebra.Homology.Localization

/-! # Representative factors of the scalar inverse mate

Source: Stacks Tags 00YV and 07A6.
(blueprint: lem-sf-finite-scalar-pullback-representative-factors).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MonoidalCategory
open CategoryTheory.Functor
-- Share the already proved coefficient-instance shortcuts used by the canonical map.
attribute [local instance 2000] isNoetherian_of_finite
attribute [local instance 10000] WeilConjectures.sfAbBijective WeilConjectures.sfAbSheafify
  finiteProjection_moduleSheafify finiteProjection_sheafGroth finiteProjection_functorLimits
  finiteProjection_functorColimits finiteProjection_inverseAdditive finiteProjection_inverseLimits
  finiteProjection_inverseColimits finiteProjection_moduleGroth finiteProjection_modulePreadditive
  finiteProjection_moduleFlat

attribute [local instance 10000] WeilConjectures.finiteScalarCountableColimits
  WeilConjectures.finiteScalarTensorTotal
  WeilConjectures.finiteScalarIntrinsicCountableColimits
  WeilConjectures.finiteScalarFunctorAdditive WeilConjectures.finiteScalarFunctorEquivalence
  WeilConjectures.finiteScalarFixedTensorPreadditive

-- Use the same inherited data as the native derived tensor and exact-functor APIs.
attribute [local instance 2000] SymmetricCategory.toBraidedCategory Abelian.toPreadditive
attribute [local instance 4000] Preadditive.preadditiveHasZeroMorphisms

-- Match the native additive data in the published complex tensor models.
attribute [local instance 30000] SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive CategoryTheory.functorCategoryPreadditive
  Preadditive.preadditiveHasZeroMorphisms Functor.preservesZeroMorphisms_of_additive

namespace WeilConjectures

/-- The exact fixed-scalar inverse image computes its total left derived functor.
Source: Stacks Tag 04JC, localization of exact inverse image.
(blueprint: lem-sf-finite-scalar-pullback-representative-factors). -/
@[irreducible] def finiteScalarFixedPullbackFactors
    (R : Type u) [CommRing R] {X Y : Scheme.{u}} (p : X ⟶ Y) :
    DerivedCategory.Q ⋙
        (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).leftDerivedFunctor ≅
      (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).mapHomologicalComplex
        (.up ℤ) ⋙ DerivedCategory.Q :=
  isoWhiskerLeft DerivedCategory.Q
    (ProEtale.upperStar
      (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).leftDerivedFunctorIsoMapDerivedCategory ≪≫
    (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).mapDerivedCategoryFactors

/-- The inverse mate on derived categories has the ordinary mate's chain normalization.
This is a unary statement: it involves no tensor product and no tensor model.

Source: Stacks Tags 07A6 and 0D6E, comparison of derived adjunction Hom bijections.
(blueprint: lem-sf-finite-scalar-pullback-representative-factors).

Proof: write the ordinary comparison as the inverse mate of the section-normalized
ordinary direct-image isomorphism. Apply the exact-derived mate formula to its
termwise localization. The inverse derived direct-image comparison obeys the same
unit equation, first on K-injectives by its definition, and then on every complex
by naturality along a K-injective resolution. Uniqueness of the derived mate gives
the displayed formula. The identification of the two constant direct images is
induced by the coefficient adjunction and is the same in both mate constructions.
The two exact-functor factor isomorphisms put the formula in complex coordinates.
There are no boundedness, nonzero-coefficient, or nonempty-site assumptions.
-/
private theorem exact_factors_eq_counit_local
    {C D : Type*} [Category.{u + 1} C] [Category.{u + 1} D]
    [Abelian C] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} C] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    (L : C ⥤ D) [L.Additive] [Limits.PreservesFiniteLimits L]
    [Limits.PreservesFiniteColimits L] (Z : CochainComplex C ℤ) :
    L.leftDerivedFunctorIsoMapDerivedCategory.hom.app (DerivedCategory.Q.obj Z) ≫
        L.mapDerivedCategoryFactors.hom.app Z =
      L.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient _ _).obj Z) := by
  have h := L.leftDerivedFunctorIsoMapDerivedCategory_hom_app_Qh
    ((HomotopyCategory.quotient _ _).obj Z)
  rw [CategoryTheory.Functor.mapDerivedCategoryFactorsh_hom_app] at h
  dsimp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Quotient.lift.isLift_hom, Quotient.lift.isLift_inv,
    CategoryTheory.Functor.mapHomotopyCategoryFactors] at h
  erw [CategoryTheory.Functor.map_id, Category.id_comp,
    CategoryTheory.Functor.map_id, Category.comp_id, Category.comp_id] at h
  exact h

private theorem fixedFactors_eq_counit_local
    (R : Type u) [CommRing R] [Finite R] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (Z : CochainComplex
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} R))) ℤ) :
    (finiteScalarFixedPullbackFactors R p).hom.app Z =
      (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).leftDerivedFunctorCounit.app
        ((HomotopyCategory.quotient _ _).obj Z) := by
  simpa only [finiteScalarFixedPullbackFactors, Iso.trans_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, whiskerLeft_app] using exact_factors_eq_counit_local
      (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p) Z

/-- The expanded mate-normalization equation before the paper-level wrappers are folded.
Source: Stacks Tags 07A6 and 0D6E.
(blueprint: lem-sf-finite-scalar-pullback-representative-factors-core).

This is the concrete derived-category square obtained from the normalized inverse mate;
it is the single mate calculation used by the wrapper theorem below. -/
private theorem finiteScalarPullback_representative_factors_core
    (R : Type u) [CommRing R] [Finite R] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (P : CochainComplex
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} R))) ℤ) :
    (sfIntrinsicDerivedEquivalence X R).functor.map
        ((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).leftDerivedFunctorCounit.app
          ((HomotopyCategory.quotient _ _).obj P)) ≫
      (sfIntrinsicModuleEquivalence X R).functor.mapDerivedCategoryFactors.hom.app
        (((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).mapHomologicalComplex
          (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((mapHomologicalComplexCompIso (finiteScalarOrdinaryPullbackComparison R p)
          (.up ℤ)).inv.app P) =
    (finiteScalarPullbackComparison R p).inv.app (DerivedCategory.Q.obj P) ≫
      (proEtaleConstantRingDerivedPullback R p).map
        ((sfIntrinsicModuleEquivalence Y R).functor.mapDerivedCategoryFactors.hom.app P) ≫
      (proEtaleRingDerivedPullbackFactors p (proEtaleConstantRing Y R)
        (proEtaleConstantRing X R) (proEtaleConstantRingComparison p R)).hom.app
          (((sfIntrinsicModuleEquivalence Y R).functor.mapHomologicalComplex (.up ℤ)).obj P) := by
  rw [← exact_factors_eq_counit_local
    (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p) P]
  simpa only [Functor.map_comp, Category.assoc] using
    finiteScalarPullback_representative_factors_factorized R p P

theorem finiteScalarPullback_representative_factors
    (R : Type u) [CommRing R] [Finite R] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (P : CochainComplex
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} R))) ℤ) :
    (sfIntrinsicDerivedEquivalence X R).functor.map
        ((finiteScalarFixedPullbackFactors R p).hom.app P) ≫
      (sfIntrinsicModuleEquivalence X R).functor.mapDerivedCategoryFactors.hom.app
        (((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).mapHomologicalComplex
          (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((finiteScalarComplexPullbackComparison R p).inv.app P) =
    (finiteScalarPullbackComparison R p).inv.app (DerivedCategory.Q.obj P) ≫
      (proEtaleConstantRingDerivedPullback R p).map
        ((sfIntrinsicModuleEquivalence Y R).functor.mapDerivedCategoryFactors.hom.app P) ≫
      (proEtaleRingDerivedPullbackFactors p (proEtaleConstantRing Y R)
        (proEtaleConstantRing X R) (proEtaleConstantRingComparison p R)).hom.app
          (((sfIntrinsicModuleEquivalence Y R).functor.mapHomologicalComplex (.up ℤ)).obj P)
    := by
  rw [fixedFactors_eq_counit_local R p P]
  simp only [finiteScalarComplexPullbackComparison]
  dsimp only [finiteScalarPullbackComparison]
  exact finiteScalarPullback_representative_factors_core R p P

end WeilConjectures
