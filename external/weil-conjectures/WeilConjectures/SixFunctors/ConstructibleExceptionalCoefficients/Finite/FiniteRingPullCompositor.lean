/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Finite.FiniteRingFixedCoordinates

import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Finite.FiniteRingOrdinaryPushCoordinates
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

/-- The ordinary pull compositor determined by the unique normalized direct-image compositor.
Source: Stacks 03D6 (blueprint: lem-sf-finite-ring-pull-compositor).
The adjunction conjugation equivalence determines it uniquely. -/
def finiteOrdinaryPullComp
    (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ)
    {X Y Z : Scheme.{w}} (h : X ⟶ Y) (k : Y ⟶ Z)
    (hc : (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull (h ≫ k) =
      proEtaleRingCompositeCoefficients h k
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring Z)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring Y)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring X)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull k)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull h)) :
    let R := PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)
    proEtaleRingModulePullback (h ≫ k) (R.ring Z) (R.ring X) (R.pull (h ≫ k)) ≅
      proEtaleRingModulePullback k (R.ring Z) (R.ring Y) (R.pull k) ⋙
        proEtaleRingModulePullback h (R.ring Y) (R.ring X) (R.pull h) :=
  let R := PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)
  (conjugateIsoEquiv
    ((proEtaleRingModuleAdjunction k (R.ring Z) (R.ring Y) (R.pull k)).comp
      (proEtaleRingModuleAdjunction h (R.ring Y) (R.ring X) (R.pull h)))
    (proEtaleRingModuleAdjunction (h ≫ k) (R.ring Z) (R.ring X) (R.pull (h ≫ k)))).symm
      (PurCompactSupport.modulePushComposition_existsUnique R h k hc).exists.choose

attribute [local irreducible] finiteOrdinaryPullComp

/-- The finite pullback presentation preserves the ordinary pull compositor.
Source: Stacks 03D6 (blueprint: lem-sf-finite-ring-pull-compositor).
Proof: apply the generic uniqueness compositor transport identity to the three
finiteDirectImage_eq equalities. Substitute finiteOrdinaryPushComposition and
unfold the named inverse conjugate. This identifies the specified left-adjoint
uniqueness comparison with the composite of the two factor comparisons. -/
theorem finite_pull_comp_ordinary
    (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ)
    {X Y Z : Scheme.{w}} (h : X ⟶ Y) (k : Y ⟶ Z)
    (hc : (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull (h ≫ k) =
      proEtaleRingCompositeCoefficients h k
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring Z)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring Y)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring X)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull k)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull h)) :
    let A := Padic.coefficientExtensionRing l E (n + 1)
    let R := PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)
    PurCompactSupport.finitePullbackIso l E n (h ≫ k) ≪≫ sfIntrinsicPullbackComp A h k =
      finiteOrdinaryPullComp l E n h k hc ≪≫
        Functor.isoWhiskerLeft
          (proEtaleRingModulePullback k (R.ring Z) (R.ring Y) (R.pull k))
          (PurCompactSupport.finitePullbackIso l E n h) ≪≫
        Functor.isoWhiskerRight (PurCompactSupport.finitePullbackIso l E n k)
          (sfIntrinsicPullback A h) := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let R := PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)
  let ag := proEtaleRingModuleAdjunction k (R.ring Z) (R.ring Y) (R.pull k)
  let af := proEtaleRingModuleAdjunction h (R.ring Y) (R.ring X) (R.pull h)
  let ac := proEtaleRingModuleAdjunction (h ≫ k) (R.ring Z) (R.ring X) (R.pull (h ≫ k))
  have ht := uniq_compositor_transport ag (sfIntrinsicConstantModuleAdjunction k A)
    af (sfIntrinsicConstantModuleAdjunction h A) ac
    (sfIntrinsicConstantModuleAdjunction (h ≫ k) A)
    (PurCompactSupport.finiteDirectImage_eq l E n k)
    (PurCompactSupport.finiteDirectImage_eq l E n h)
    (PurCompactSupport.finiteDirectImage_eq l E n (h ≫ k))
    (sfIntrinsicPullbackComp A h k)
  have hd := finiteOrdinaryPushComposition l E n h k hc
  change (PurCompactSupport.modulePushComposition_existsUnique R h k hc).exists.choose = _ at hd
  dsimp only [finiteTransportedOrdinaryCompositor, finiteScalarTransportCompositor,
    finiteIntrinsicOrdinaryCompositor] at hd
  erw [← hd] at ht
  unfold finiteOrdinaryPullComp
  exact ht

end WeilConjectures.ConstructibleExceptionalCoefficients
