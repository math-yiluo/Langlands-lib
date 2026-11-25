/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Finite.FiniteRingFixedCoordinates
public import WeilConjectures.AlgebraicGeometry.ProEtale.Proper.ProEtaleProperOpenUnitNormalization
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Finite.FiniteRingPullCoordinates

import all WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Finite.FiniteCoordinateCalculus
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Finite.FiniteRingCounitCoordinates

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

attribute [local irreducible] ProEtale.upperStar ProEtale.upperStarComp
  PurCompactSupport.geometricPullComposition finiteDerivedPullCoordinates
  proEtaleRingModulePullback sfConstantCoefficientIso

/-- Finite realization preserves the restriction obtained from pull composition and counit.
Source: compactification-coherence proof, first two paragraphs; Stacks 03D6 and 0D6D
(blueprint: lem-sf-finite-ring-restriction-coordinates).

Proof: derivedUniq identifies the exact derived left-adjoint uniqueness comparison.
Its counit equation, composed with the realization mate counit equation from
derived_realization_mate, gives finite_direct_counit_coordinates. Use the triangle
composition square finite_pull_triangle_coordinates for the open triangle of r.
Expand the ring restriction, move the inverse direct-image comparison through the
triangle compositor by naturality, and cancel the first pull comparison. Apply
the direct counit square and then naturality of the first pull comparison with
respect to the fixed counit. Substitute the triangle square and expand
properOpenRestriction. The resulting composite is exactly the claimed equation;
no properness or etale-origin condition is needed for this restriction calculation.
The final naturality calculation is the generic restriction_coefficient_mate
identity, specialized to the counit square and the triangle square just proved. -/
theorem finite_restriction_coordinates
    (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ)
    {X Y : Scheme.{w}} {f : X ⟶ Y} {c d : Compactification f}
    (r : c.Refinement d)
    (hi : (PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull (c.i ≫ r.hom) =
      proEtaleRingCompositeCoefficients c.i r.hom
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring d.Z)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring c.Z)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).ring X)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull r.hom)
        ((PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)).pull c.i))
    (N : DerivedCategory (Sheaf (ProEt.topology c.Z)
      (ModuleCat.{w + 1} (ULift.{w + 1} (Padic.coefficientExtensionRing l E (n + 1)))))) :
    let A := Padic.coefficientExtensionRing l E (n + 1)
    let B := ModuleCat.{w + 1} (ULift.{w + 1} A)
    let R := PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)
    let ρ : PurCompactSupport.push R r.hom ⋙ PurCompactSupport.pull R d.i ⟶
        PurCompactSupport.pull R c.i :=
      Functor.whiskerLeft (PurCompactSupport.push R r.hom)
          (PurCompactSupport.refinementPull R r hi).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (proEtaleRingDerivedAdjunction r.hom
          (R.ring d.Z) (R.ring c.Z) (R.pull r.hom)).counit (PurCompactSupport.pull R c.i)
    (PurCompactSupport.pull R d.i).map ((finiteFixedPushIso l E n r.hom).inv.app N) ≫
        ρ.app ((sfIntrinsicDerivedEquivalence c.Z A).functor.obj N) =
      (finiteDerivedPullCoordinates l E n d.i).hom.app
          ((ProEtale.lowerStar B r.hom).rightDerivedFunctor.obj N) ≫
        (sfIntrinsicDerivedEquivalence X A).functor.map
          ((ProEtale.properOpenRestriction (ULift.{w + 1} A)
            r.hom c.i d.i r.i_hom).app N) ≫
        (finiteDerivedPullCoordinates l E n c.i).inv.app N := by
  revert hi N
  rcases c with ⟨Zc, gc, ic, hc, hpc, hoc⟩
  rcases d with ⟨Zd, gd, jd, hd, hpd, hod⟩
  rcases r with ⟨v, hv, hvg⟩
  change Zc ⟶ Zd at v
  change ic ≫ v = jd at hv
  change v ≫ gd = gc at hvg
  subst jd
  intro hi N
  let c : Compactification f := ⟨Zc, gc, ic, hc, hpc, hoc⟩
  let d : Compactification f := ⟨Zd, gd, ic ≫ v, hd, hpd, hod⟩
  let r : c.Refinement d := ⟨v, rfl, hvg⟩
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let B := ModuleCat.{w + 1} (ULift.{w + 1} A)
  let R := PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)
  let EX := (sfIntrinsicDerivedEquivalence X A).functor
  let EC := (sfIntrinsicDerivedEquivalence c.Z A).functor
  let Rf := (ProEtale.lowerStar B r.hom).rightDerivedFunctor
  let L₁ := (ProEtale.upperStar B c.i).mapDerivedCategory
  let L₂ := (ProEtale.upperStar B d.i).mapDerivedCategory
  let Li := (ProEtale.upperStar B r.hom).mapDerivedCategory
  let P₁ := PurCompactSupport.pull R c.i
  let P₂ := PurCompactSupport.pull R d.i
  let Pi := PurCompactSupport.pull R r.hom
  let kf : L₂ ≅ Li ⋙ L₁ := Functor.mapDerivedCategoryNatIso
      (eqToIso (congrArg (fun t ↦ ProEtale.upperStar B t) r.i_hom.symm) ≪≫
        ProEtale.upperStarComp B c.i r.hom) ≪≫
    (Functor.mapDerivedCategoryCompIso (ProEtale.upperStar B r.hom)
      (ProEtale.upperStar B c.i)).symm
  let ED := (sfIntrinsicDerivedEquivalence d.Z A).functor
  let af : Li ⊣ Rf := (ProEtale.upperStarLowerStarAdjunction B r.hom
    ).mapDerivedCategoryRightDerivedAdjunction
  let ar : Pi ⊣ PurCompactSupport.push R r.hom := proEtaleRingDerivedAdjunction r.hom
    (R.ring d.Z) (R.ring c.Z) (R.pull r.hom)
  dsimp only
  rw [ProEtale.properOpenRestriction.eq_def]
  refine restriction_coordinate_square
    (FA := Li) (RA := Rf) (FB := Pi) (RB := PurCompactSupport.push R r.hom)
    af ar L₁ L₂ P₁ P₂ EX EC ED kf
    (PurCompactSupport.refinementPull R r hi)
    (finiteDerivedPullCoordinates l E n c.i) (finiteDerivedPullCoordinates l E n d.i)
    (finiteDerivedPullCoordinates l E n r.hom) (finiteFixedPushIso l E n r.hom).inv
    (fun T ↦ finite_direct_counit_coordinates (X := c.Z) (Y := d.Z) l E n r.hom T) (fun T ↦ ?_) N
  rw [PurCompactSupport.refinementPull.eq_def R r hi]
  exact (finite_pull_triangle_coordinates (X := X) (Y := c.Z) (Z := d.Z)
    l E n c.i r.hom d.i r.i_hom hi T).symm

end WeilConjectures.ConstructibleExceptionalCoefficients
