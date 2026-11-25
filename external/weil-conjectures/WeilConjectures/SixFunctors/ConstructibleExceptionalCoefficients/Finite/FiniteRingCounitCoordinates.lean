/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Finite.FiniteRingFixedCoordinates
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Finite.FiniteRingPullCoordinates

import all WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicConjugateComparisonTransport
import all WeilConjectures.SixFunctors.IntegralSystemRealization.Finite.IntegralFinitePullbackNormalization
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import all WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Finite.FiniteCoordinateCalculus

/-! # Proved finite coefficient coordinate calculus -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe w
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients

open CategoryTheory.Limits
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  sfIntrinsicModuleEquivalence
attribute [local implicit_reducible] Equivalence.mapDerivedCategory
  sfIntrinsicDerivedEquivalence PurCompactSupport.finite
  sfIntrinsicPullback sfIntrinsicTransport sfIntrinsicExtensionByZero
set_option backward.defeqAttrib.useBackward true

/-- Finite realization identifies the derived proper counit in the fixed coordinates.
Source: Stacks 03D6 and 0D6D, compactification-coherence proof, first two paragraphs
(blueprint: lem-sf-finite-ring-counit-coordinates).

Proof: derive the ordinary finite left-adjoint uniqueness isomorphism using derivedUniq.
Apply its counit identity to the inverse derived realization comparison.
derived_realization_mate and mateEquiv_counit give the realization counit identity.
Finally derived_square_left_comp identifies the composite of the two exact pullback
squares with finiteDerivedPullCoordinates. The argument applies to every map and
unbounded derived object, including zero objects and empty schemes. -/
theorem finite_direct_counit_coordinates
    (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ)
    {X Y : Scheme.{w}} (g : X ⟶ Y)
    (N : DerivedCategory (Sheaf (ProEt.topology X)
      (ModuleCat.{w + 1} (ULift.{w + 1} (Padic.coefficientExtensionRing l E (n + 1)))))) :
    let A := Padic.coefficientExtensionRing l E (n + 1)
    let B := ModuleCat.{w + 1} (ULift.{w + 1} A)
    let R := PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)
    let EX := sfIntrinsicDerivedEquivalence X A
    (PurCompactSupport.pull R g).map ((finiteFixedPushIso l E n g).inv.app N) ≫
        (proEtaleRingDerivedAdjunction g (R.ring Y) (R.ring X) (R.pull g)).counit.app
          (EX.functor.obj N) =
      (finiteDerivedPullCoordinates l E n g).hom.app
          ((ProEtale.lowerStar B g).rightDerivedFunctor.obj N) ≫
        EX.functor.map ((ProEtale.upperStarLowerStarAdjunction B g
          ).mapDerivedCategoryRightDerivedAdjunction.counit.app N) := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.le_add_left 1 n)
  let := sfIntrinsicModuleEquivalence_functor_additive A X
  let := sfIntrinsicModuleEquivalence_functor_additive A Y
  let B := ModuleCat.{w + 1} (ULift.{w + 1} A)
  let R := PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)
  let EX := sfIntrinsicModuleEquivalence X A
  let EY := sfIntrinsicModuleEquivalence Y A
  let L := ProEtale.upperStar B g
  let adj := ProEtale.upperStarLowerStarAdjunction B g
  let ar := proEtaleRingModuleAdjunction g (R.ring Y) (R.ring X) (R.pull g)
  let ai := sfIntrinsicConstantModuleAdjunction g A
  let : (proEtaleConstantModuleDirectImage g A).Additive :=
    (proEtaleConstantModuleDirectImage_additive_leftExact g A).1
  let := sfIntrinsicPullback_additive A g
  let := sfIntrinsicPullback_preservesFiniteLimits A g
  let := sfIntrinsicPullback_preservesFiniteColimits A g
  let p := Functor.rightDerivedFunctorNatIso
    (eqToIso (PurCompactSupport.finiteDirectImage_eq l E n g))
  let q := Functor.mapDerivedCategoryNatIso (PurCompactSupport.finitePullbackIso l E n g)
  let w := EY.funInvIdAssoc (L ⋙ EX.functor)
  let v := Functor.mapDerivedCategorySquareIso w
  let s := sfIntrinsicDerivedDirectImageComparison g A
  have hq := uniq_counit ar.mapDerivedCategoryRightDerivedAdjunction
    ai.mapDerivedCategoryRightDerivedAdjunction p (EX.functor.mapDerivedCategory.obj N)
    (s.inv.app N)
  rw [derivedUniq ar ai (eqToIso (PurCompactSupport.finiteDirectImage_eq l E n g))] at hq
  have hi := mateEquiv_counit adj.mapDerivedCategoryRightDerivedAdjunction
    ai.mapDerivedCategoryRightDerivedAdjunction
    (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso w.symm).inv) N
  have hm := derived_realization_mate A g
  change _ = s.inv at hm
  rw [hm] at hi
  have hw : (Functor.mapDerivedCategorySquareIso w.symm).inv = v.hom :=
    (congrArg Iso.inv
      (Iso.ext (Functor.square_symm_hom w) :
        Functor.mapDerivedCategorySquareIso w.symm =
          (Functor.mapDerivedCategorySquareIso w).symm))
  rw [hw] at hi
  have ho := congr_app (derived_square_left_comp EY.functor L EX.functor
    (PurCompactSupport.finitePullbackIso l E n g) w)
    ((ProEtale.lowerStar B g).rightDerivedFunctor.obj N)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at ho
  change (PurCompactSupport.pull R g).map (s.inv.app N ≫ p.inv.app _) ≫ _ = _
  change q.hom.app _ ≫ _ = _ at hq
  dsimp only [Functor.comp_obj, TwoSquare.mk] at hi hq
  have hh := congrArg
    (fun t ↦ q.hom.app (EY.functor.mapDerivedCategory.obj
      ((ProEtale.lowerStar B g).rightDerivedFunctor.obj N)) ≫ t) hi
  have ht := hq.symm.trans hh
  dsimp only [v, q] at ht
  erw [← Category.assoc, ← ho] at ht
  exact ht

end WeilConjectures.ConstructibleExceptionalCoefficients
