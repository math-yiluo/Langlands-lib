/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Finite.FiniteRingFixedCoordinates

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

/-- The ordinary finite open-extension coordinates preserve the specified unit.
Source: compactification-coherence proof, first paragraph; Stacks 03DI
(blueprint: lem-sf-finite-ring-ordinary-open-unit-coordinates).
Proof: finiteOpenIso is the left-adjoint uniqueness comparison for the finite
open adjunction transported by finitePullbackIso. Apply the general
open_unit_coordinates identity to the two realization equivalences and the
specified fixed and ring open adjunctions. The realization comparison is exactly
fixedOpenModel. The calculation uses only unit naturality and the equivalence
triangle identities, and also applies to identity and empty opens. -/
theorem finite_open_unit_ordinary
    (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ)
    {X Y : Scheme.{w}} (j : X ⟶ Y) [IsOpenImmersion j]
    (K : Sheaf (ProEt.topology X)
      (ModuleCat.{w + 1} (ULift.{w + 1} (Padic.coefficientExtensionRing l E (n + 1))))) :
    let A := Padic.coefficientExtensionRing l E (n + 1)
    let R := PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)
    let EX := sfIntrinsicModuleEquivalence X A
    let EY := sfIntrinsicModuleEquivalence Y A
    let J := AlgebraicGeometry.ProEtale.openImmersionLowerShriek
      (ModuleCat.{w + 1} (ULift.{w + 1} A)) j
    let U := AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{w + 1} (ULift.{w + 1} A)) j
    let o := Functor.isoWhiskerLeft EX.functor (PurCompactSupport.finiteOpenIso l E n j) ≪≫
      FrobeniusExchange.fixedOpenModel A j
    let v := Functor.isoWhiskerLeft EY.functor (PurCompactSupport.finitePullbackIso l E n j) ≪≫
      EY.funInvIdAssoc (U ⋙ EX.functor)
    (PurCompactSupport.openAdjunction R j).unit.app (EX.functor.obj K) ≫
      (proEtaleRingModulePullback j (R.ring Y) (R.ring X) (R.pull j)).map (o.hom.app K) =
      EX.functor.map
        ((AlgebraicGeometry.ProEtale.openImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{w + 1} (ULift.{w + 1} A)) j).unit.app K) ≫ v.inv.app (J.obj K) := by
  dsimp only [PurCompactSupport.finiteOpenIso, FrobeniusExchange.fixedOpenModel]
  exact open_unit_coordinates
    (sfIntrinsicModuleEquivalence X (Padic.coefficientExtensionRing l E (n + 1)))
    (sfIntrinsicModuleEquivalence Y (Padic.coefficientExtensionRing l E (n + 1)))
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{w + 1} (ULift.{w + 1} (Padic.coefficientExtensionRing l E (n + 1)))) j)
    (PurCompactSupport.openAdjunction
      (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)) j)
    (PurCompactSupport.finitePullbackIso l E n j) K

end WeilConjectures.ConstructibleExceptionalCoefficients
