/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorComplex
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorPullbackDescentData

/-! # The ordinary scalar inverse-image comparison

Source: Stacks Tags 00YV and 07A6.
(blueprint: def-sf-finite-scalar-ordinary-pullback-comparison).
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

/-- The two constant-coefficient direct images are the same functor.
Source: the adjunction defining the coefficient structure map, Stacks Tag 00YV.
(blueprint: def-sf-finite-scalar-ordinary-pullback-comparison). -/
theorem finiteScalarConstantPushforward_eq
    (R : Type u) [CommRing R] {X Y : Scheme.{u}} (p : X ⟶ Y) :
    proEtaleConstantRingPushforward R p = proEtaleConstantModuleDirectImage p R := by
  have hρ : proEtaleRingDirectImageMap p (proEtaleConstantRing Y R)
      (proEtaleConstantRing X R) (proEtaleConstantRingComparison p R) =
      proEtaleCoefficientDirectImageMap p R := by
    change (proEtaleSheafAdjunction p CommRingCat.{u + 1}).homEquiv _ _
      (proEtaleCoefficientInverseImageMap p R) = _
    exact ((proEtaleSheafAdjunction p CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _
  unfold proEtaleConstantRingPushforward proEtaleRingModuleDirectImage
    proEtaleConstantModuleDirectImage
  rw [hρ]

/-- The inverse mate of the section-normalized ordinary direct-image comparison.
Its definition fixes the comparison before passing to complexes or derived categories.
Source: Stacks Tags 00YV and 07A6, uniqueness of adjoints.
(blueprint: def-sf-finite-scalar-ordinary-pullback-comparison). -/
@[irreducible] def finiteScalarOrdinaryPullbackComparison
    (R : Type u) [CommRing R] [Finite R] {X Y : Scheme.{u}} (p : X ⟶ Y) :
    (sfIntrinsicModuleEquivalence Y R).functor ⋙
        proEtaleRingModulePullback p (proEtaleConstantRing Y R)
          (proEtaleConstantRing X R) (proEtaleConstantRingComparison p R) ≅
      ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p ⋙
        (sfIntrinsicModuleEquivalence X R).functor := by
  let a := ProEtale.upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1} R)) p
  let b := proEtaleRingModuleAdjunction p
    (proEtaleConstantRing Y R) (proEtaleConstantRing X R)
    (proEtaleConstantRingComparison p R)
  let r := (sfIntrinsicDirectImageComparison p R).symm ≪≫
    isoWhiskerLeft (sfIntrinsicModuleEquivalence X R).functor
      (eqToIso (finiteScalarConstantPushforward_eq R p)).symm
  let α := ((mateEquiv a b).symm
    (TwoSquare.mk _ (sfIntrinsicModuleEquivalence X R).functor
      (sfIntrinsicModuleEquivalence Y R).functor _ r.hom))
  have : IsIso α := isIso_inverseMate_of_equivalences a b r
  exact asIso α

/-- The same comparison degree by degree, retaining the actual chain-map components.
Source: Stacks Tag 07A6, termwise application of the ordinary comparison.
(blueprint: def-sf-finite-scalar-ordinary-pullback-comparison). -/
@[irreducible] def finiteScalarComplexPullbackComparison
    (R : Type u) [CommRing R] [Finite R] {X Y : Scheme.{u}} (p : X ⟶ Y) :
    (sfIntrinsicModuleEquivalence Y R).functor.mapHomologicalComplex (.up ℤ) ⋙
        (proEtaleRingModulePullback p (proEtaleConstantRing Y R)
          (proEtaleConstantRing X R) (proEtaleConstantRingComparison p R)).mapHomologicalComplex
            (.up ℤ) ≅
      (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).mapHomologicalComplex
          (.up ℤ) ⋙
        (sfIntrinsicModuleEquivalence X R).functor.mapHomologicalComplex (.up ℤ) :=
  Functor.mapHomologicalComplexCompIso (finiteScalarOrdinaryPullbackComparison R p) (.up ℤ)

/-- The intrinsic complex tensor comparison, with its natural-transformation type fixed.
The existing descent-data theorem specifies every component and thus determines this map.
Source: Stacks Tag 07A4, signed-total pullback comparison.
(blueprint: def-sf-finite-scalar-ordinary-pullback-comparison). -/
@[irreducible] def finiteScalarIntrinsicComplexTensorPullback
    (R : Type u) [CommRing R] {X Y : Scheme.{u}} (p : X ⟶ Y) :
    uncurry.obj ((proEtaleOrdinaryTensor Y (proEtaleConstantRing Y R)).map₂HomologicalComplex
        (.up ℤ) (.up ℤ) (.up ℤ)) ⋙
      (proEtaleRingModulePullback p (proEtaleConstantRing Y R) (proEtaleConstantRing X R)
        (proEtaleConstantRingComparison p R)).mapHomologicalComplex (.up ℤ) ⟶
    ((proEtaleRingModulePullback p (proEtaleConstantRing Y R) (proEtaleConstantRing X R)
        (proEtaleConstantRingComparison p R)).mapHomologicalComplex (.up ℤ)).prod
      ((proEtaleRingModulePullback p (proEtaleConstantRing Y R) (proEtaleConstantRing X R)
        (proEtaleConstantRingComparison p R)).mapHomologicalComplex (.up ℤ)) ⋙
      uncurry.obj ((proEtaleOrdinaryTensor X (proEtaleConstantRing X R)).map₂HomologicalComplex
        (.up ℤ) (.up ℤ) (.up ℤ)) :=
  (Classical.choose (proEtaleTensorPullbackDescentData p (proEtaleConstantRing Y R)
    (proEtaleConstantRing X R) (proEtaleConstantRingComparison p R)).2.2).inv

/-- The wrapper retains precisely the prescribed inverse signed-total comparison.
Source: Stacks Tag 07A4, the component specification of the descent-data theorem.
(blueprint: def-sf-finite-scalar-ordinary-pullback-comparison). -/
theorem finiteScalarIntrinsicComplexTensorPullback_app
    (R : Type u) [CommRing R] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (P Q : CochainComplex (proEtaleRingModules Y (proEtaleConstantRing Y R)) ℤ) :
    (finiteScalarIntrinsicComplexTensorPullback R p).app (P, Q) =
      (proEtaleTensorPullbackTotalIso p (proEtaleConstantRing Y R) (proEtaleConstantRing X R)
        (proEtaleConstantRingComparison p R) P Q).inv := by
  unfold finiteScalarIntrinsicComplexTensorPullback
  exact Classical.choose_spec (proEtaleTensorPullbackDescentData p (proEtaleConstantRing Y R)
    (proEtaleConstantRing X R) (proEtaleConstantRingComparison p R)).2.2 P Q

end WeilConjectures
