/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Finite.FiniteRingPullCompositor

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

/-- The ordinary finite inverse-image comparison in fixed-scalar realization coordinates.
Source: Stacks 03D6 (blueprint: lem-sf-finite-ring-ordinary-pull-coordinates).
It is finitePullbackIso followed by the realization equivalence cancellation. -/
def finitePullCoordinates
    (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ)
    {X Y : Scheme.{w}} (g : X ⟶ Y) :
    let A := Padic.coefficientExtensionRing l E (n + 1)
    let R := PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)
    (sfIntrinsicModuleEquivalence Y A).functor ⋙
        proEtaleRingModulePullback g (R.ring Y) (R.ring X) (R.pull g) ≅
      ProEtale.upperStar (ModuleCat.{w + 1} (ULift.{w + 1} A)) g ⋙
        (sfIntrinsicModuleEquivalence X A).functor :=
  let A := Padic.coefficientExtensionRing l E (n + 1)
  Functor.isoWhiskerLeft (sfIntrinsicModuleEquivalence Y A).functor
      (PurCompactSupport.finitePullbackIso l E n g) ≪≫
    (sfIntrinsicModuleEquivalence Y A).funInvIdAssoc
      (ProEtale.upperStar (ModuleCat.{w + 1} (ULift.{w + 1} A)) g ⋙
        (sfIntrinsicModuleEquivalence X A).functor)

attribute [local irreducible] finiteOrdinaryPullComp

/-- Ordinary finite realization coordinates commute with pullback composition.
Source: Stacks 03D6 and 03DI (blueprint: lem-sf-finite-ring-ordinary-pull-coordinates).
Proof: apply the realization coordinate composition identity to the ordinary
finitePullbackIso compositor equality. Its proof inverts the realization unit
composition square and uses naturality of the middle pull comparison. All
coordinates are the explicit presentation isomorphism followed by equivalence
cancellation, so this also treats identity maps and empty schemes. -/
theorem finite_pull_coordinate_comp_ordinary
    (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ)
    {X Y Z : Scheme.{w}} (h : X ⟶ Y) (k : Y ⟶ Z)
    (hc : (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull (h ≫ k) =
      proEtaleRingCompositeCoefficients h k
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring Z)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring Y)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring X)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull k)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull h))
    (M : Sheaf (ProEt.topology Z)
      (ModuleCat.{w + 1} (ULift.{w + 1} (Padic.coefficientExtensionRing l E (n + 1))))) :
    let A := Padic.coefficientExtensionRing l E (n + 1)
    let B := ModuleCat.{w + 1} (ULift.{w + 1} A)
    let R := PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)
    (finitePullCoordinates l E n (h ≫ k)).hom.app M ≫
        (sfIntrinsicModuleEquivalence X A).functor.map ((ProEtale.upperStarComp B h k).hom.app M) =
      (finiteOrdinaryPullComp l E n h k hc).hom.app
          ((sfIntrinsicModuleEquivalence Z A).functor.obj M) ≫
        (proEtaleRingModulePullback h (R.ring Y) (R.ring X) (R.pull h)).map
          ((finitePullCoordinates l E n k).hom.app M) ≫
        (finitePullCoordinates l E n h).hom.app ((ProEtale.upperStar B k).obj M) := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.le_add_left 1 n)
  let B := ModuleCat.{w + 1} (ULift.{w + 1} A)
  let R := PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)
  let EX := sfIntrinsicModuleEquivalence X A
  let EY := sfIntrinsicModuleEquivalence Y A
  let EZ := sfIntrinsicModuleEquivalence Z A
  let Lh := ProEtale.upperStar B h
  let Lk := ProEtale.upperStar B k
  let Lc := ProEtale.upperStar B (h ≫ k)
  have hq := finite_pull_comp_ordinary l E n h k hc
  dsimp only [sfIntrinsicPullbackComp, sfIntrinsicTransportIso, sfIntrinsicTransportComp]
    at hq
  exact realization_coordinate_comp EZ EY EX Lk Lh Lc
    (proEtaleRingModulePullback k (R.ring Z) (R.ring Y) (R.pull k))
    (proEtaleRingModulePullback h (R.ring Y) (R.ring X) (R.pull h))
    (proEtaleRingModulePullback (h ≫ k) (R.ring Z) (R.ring X) (R.pull (h ≫ k)))
    (PurCompactSupport.finitePullbackIso l E n k)
    (PurCompactSupport.finitePullbackIso l E n h)
    (PurCompactSupport.finitePullbackIso l E n (h ≫ k))
    (ProEtale.upperStarComp B h k) (finiteOrdinaryPullComp l E n h k hc)
    hq M

end WeilConjectures.ConstructibleExceptionalCoefficients
