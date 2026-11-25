/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Finite.FiniteRingOrdinaryPullCoordinates

import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition

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

attribute [local instance] sfIntrinsicModuleEquivalence_functor_additive

/-- The exact derived square of the ordinary finite inverse-image coordinates.
Source: Stacks 015F and 03D6 (blueprint: lem-sf-finite-ring-pull-coordinates). -/
def finiteDerivedPullCoordinates
    (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ)
    {X Y : Scheme.{w}} (g : X ⟶ Y) :
    let A := Padic.coefficientExtensionRing l E (n + 1)
    let R := PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)
    (sfIntrinsicDerivedEquivalence Y A).functor ⋙ PurCompactSupport.pull R g ≅
      (ProEtale.upperStar (ModuleCat.{w + 1} (ULift.{w + 1} A)) g).mapDerivedCategory ⋙
        (sfIntrinsicDerivedEquivalence X A).functor :=
  let A := Padic.coefficientExtensionRing l E (n + 1)
  letI : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.le_add_left 1 n)
  letI := sfIntrinsicModuleEquivalence_functor_additive A X
  letI := sfIntrinsicModuleEquivalence_functor_additive A Y
  Functor.mapDerivedCategorySquareIso (finitePullCoordinates l E n g)

private theorem finite_pull_coordinate_comp_derived
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
    (K : DerivedCategory (Sheaf (ProEt.topology Z)
      (ModuleCat.{w + 1} (ULift.{w + 1} (Padic.coefficientExtensionRing l E (n + 1)))))) :
    let A := Padic.coefficientExtensionRing l E (n + 1)
    let B := ModuleCat.{w + 1} (ULift.{w + 1} A)
    let R := PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)
    let cf := Functor.mapDerivedCategoryNatIso (ProEtale.upperStarComp B h k) ≪≫
      (Functor.mapDerivedCategoryCompIso (ProEtale.upperStar B k) (ProEtale.upperStar B h)).symm
    (finiteDerivedPullCoordinates l E n (h ≫ k)).hom.app K ≫
        (sfIntrinsicDerivedEquivalence X A).functor.map (cf.hom.app K) =
      (PurCompactSupport.geometricPullComposition R h k hc).hom.app
          ((sfIntrinsicDerivedEquivalence Z A).functor.obj K) ≫
        (PurCompactSupport.pull R h).map ((finiteDerivedPullCoordinates l E n k).hom.app K) ≫
        (finiteDerivedPullCoordinates l E n h).hom.app
          ((ProEtale.upperStar B k).mapDerivedCategory.obj K) := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.le_add_left 1 n)
  let := sfIntrinsicModuleEquivalence_functor_additive A X
  let := sfIntrinsicModuleEquivalence_functor_additive A Y
  let := sfIntrinsicModuleEquivalence_functor_additive A Z
  let B := ModuleCat.{w + 1} (ULift.{w + 1} A)
  let R := PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)
  exact Functor.exactSquare_comp_inverse
    (ProEtale.upperStar B k) (ProEtale.upperStar B h) (ProEtale.upperStar B (h ≫ k))
    (proEtaleRingModulePullback k (R.ring Z) (R.ring Y) (R.pull k))
    (proEtaleRingModulePullback h (R.ring Y) (R.ring X) (R.pull h))
    (proEtaleRingModulePullback (h ≫ k) (R.ring Z) (R.ring X) (R.pull (h ≫ k)))
    (sfIntrinsicModuleEquivalence Z A).functor
    (sfIntrinsicModuleEquivalence Y A).functor
    (sfIntrinsicModuleEquivalence X A).functor
    (finitePullCoordinates l E n k) (finitePullCoordinates l E n h)
    (finitePullCoordinates l E n (h ≫ k)) (ProEtale.upperStarComp B h k)
    ((conjugateIsoEquiv
      ((proEtaleRingModuleAdjunction k (R.ring Z) (R.ring Y) (R.pull k)).comp
        (proEtaleRingModuleAdjunction h (R.ring Y) (R.ring X) (R.pull h)))
      (proEtaleRingModuleAdjunction (h ≫ k) (R.ring Z) (R.ring X)
        (R.pull (h ≫ k)))).symm
      (PurCompactSupport.modulePushComposition_existsUnique R h k hc).exists.choose)
    (finite_pull_coordinate_comp_ordinary l E n h k hc) K

/-- Finite inverse-image coordinates commute with the compositor of a triangle.
Source: compactification-coherence proof, first two paragraphs; Stacks 03D6 and 0D6D
(blueprint: lem-sf-finite-ring-pull-coordinates).

Proof: the ordinary finite direct-image compositor is the transported intrinsic
compositor by finiteOrdinaryPushComposition. Conjugate this equality by the
three adjunctions and apply uniqueness of left adjoints. Combine this with the
ordinary realization-equivalence composition square, using naturality of the
middle comparison. Apply exactSquare_comp_inverse to descend the resulting
ordinary square to every unbounded derived object. Finally eliminate the
triangle equality and simplify reflexive equality transports. The same equations
apply to identities, empty schemes and zero coefficient modules. -/
theorem finite_pull_triangle_coordinates
    (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ)
    {X Y Z : Scheme.{w}} (h : X ⟶ Y) (k : Y ⟶ Z) (j : X ⟶ Z)
    (w : h ≫ k = j)
    (hc : (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull (h ≫ k) =
      proEtaleRingCompositeCoefficients h k
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring Z)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring Y)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring X)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull k)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull h))
    (K : DerivedCategory (Sheaf (ProEt.topology Z)
      (ModuleCat.{w + 1} (ULift.{w + 1} (Padic.coefficientExtensionRing l E (n + 1)))))) :
    let A := Padic.coefficientExtensionRing l E (n + 1)
    let B := ModuleCat.{w + 1} (ULift.{w + 1} A)
    let R := PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)
    let cf := Functor.mapDerivedCategoryNatIso
      (eqToIso (congrArg (fun t ↦ ProEtale.upperStar B t) w.symm) ≪≫
        ProEtale.upperStarComp B h k) ≪≫
      (Functor.mapDerivedCategoryCompIso (ProEtale.upperStar B k) (ProEtale.upperStar B h)).symm
    (finiteDerivedPullCoordinates l E n j).hom.app K ≫
        (sfIntrinsicDerivedEquivalence X A).functor.map (cf.hom.app K) =
      (eqToIso (congrArg (fun t ↦ PurCompactSupport.pull R t) w.symm) ≪≫
        PurCompactSupport.geometricPullComposition R h k hc).hom.app
          ((sfIntrinsicDerivedEquivalence Z A).functor.obj K) ≫
        (PurCompactSupport.pull R h).map ((finiteDerivedPullCoordinates l E n k).hom.app K) ≫
        (finiteDerivedPullCoordinates l E n h).hom.app
          ((ProEtale.upperStar B k).mapDerivedCategory.obj K) := by
  subst j
  dsimp only
  simpa only [eqToIso_refl, Iso.refl_trans] using
    finite_pull_coordinate_comp_derived l E n h k hc K

end WeilConjectures.ConstructibleExceptionalCoefficients
