/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingCompactSupportProjectionMap
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
public import WeilConjectures.CategoryTheory.InverseMateEquivalence

/-! # Constant-scalar tensor and inverse-image comparison

Source: Stacks Project, Tags 07A4 and 07A6.
(blueprint: def-sf-finite-scalar-pullback-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Functor

namespace WeilConjectures

/-- Inverse image comparison determined by the normalized direct-image comparison.
Source: Stacks Tag 07A6 and uniqueness of adjoints
(blueprint: def-sf-finite-scalar-pullback-comparison). -/
def finiteScalarPullbackComparison (R : Type u) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} (p : X ⟶ Y) :
    (sfIntrinsicDerivedEquivalence Y R).functor ⋙
        proEtaleConstantRingDerivedPullback R p ≅
      (ProEtale.upperStar
        (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).leftDerivedFunctor ⋙
        (sfIntrinsicDerivedEquivalence X R).functor := by
  let a := ProEtale.derivedUpperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1} R)) p
  let b := proEtaleRingDerivedAdjunction p
    (proEtaleConstantRing Y R) (proEtaleConstantRing X R)
    (proEtaleConstantRingComparison p R)
  have hρ : proEtaleRingDirectImageMap p (proEtaleConstantRing Y R)
      (proEtaleConstantRing X R) (proEtaleConstantRingComparison p R) =
      proEtaleCoefficientDirectImageMap p R := by
    change (proEtaleSheafAdjunction p CommRingCat.{u + 1}).homEquiv _ _
      (proEtaleCoefficientInverseImageMap p R) = _
    exact ((proEtaleSheafAdjunction p CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _
  have hg : proEtaleConstantRingPushforward R p =
      proEtaleConstantModuleDirectImage p R := by
    unfold proEtaleConstantRingPushforward proEtaleRingModuleDirectImage
      proEtaleConstantModuleDirectImage
    rw [hρ]
  let r := (sfIntrinsicDerivedDirectImageComparison p R).symm ≪≫
    isoWhiskerLeft (sfIntrinsicDerivedEquivalence X R).functor
      (Functor.rightDerivedFunctorNatIso (eqToIso hg)).symm
  let α := ((mateEquiv a b).symm
    (TwoSquare.mk _ (sfIntrinsicDerivedEquivalence X R).functor
      (sfIntrinsicDerivedEquivalence Y R).functor _ r.hom))
  have : IsIso α := isIso_inverseMate_of_equivalences a b r
  exact asIso α

/-- The intrinsic tensor-pullback map in curried bifunctor notation.
Source: Stacks Tag 07A4
(blueprint: def-sf-finite-scalar-pullback-comparison). -/
def finiteScalarCurriedTensorPullback (R : Type u) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (aX : ProEtaleTensorModel X (proEtaleConstantRing X R))
    (aY : ProEtaleTensorModel Y (proEtaleConstantRing Y R)) :
    (postcompose₂.obj (proEtaleConstantRingDerivedPullback R p)).obj
        (curry.obj aY.tensor) ⟶
      (((whiskeringLeft₂ _).obj (proEtaleConstantRingDerivedPullback R p)).obj
        (proEtaleConstantRingDerivedPullback R p)).obj (curry.obj aX.tensor) :=
  curry.map (proEtaleCanonicalTensorComparison p
    (proEtaleConstantRing Y R) (proEtaleConstantRing X R)
    (proEtaleConstantRingComparison p R) aY aX).hom ≫
      (curryObjProdComp (proEtaleConstantRingDerivedPullback R p)
        (proEtaleConstantRingDerivedPullback R p) aX.tensor).hom

end WeilConjectures
