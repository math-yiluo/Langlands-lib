/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Finite.FiniteRingFixedCoordinates
public import WeilConjectures.AlgebraicGeometry.ProEtale.Proper.ProEtaleProperOpenUnitNormalization
public import WeilConjectures.SixFunctors.PurCompactSupport.RingOpenMapOpenUnit
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful

import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Finite.FiniteRingOpenUnitCoordinates
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Finite.FiniteRingRestrictionCoordinates
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Finite.FiniteCoordinateCalculus

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

/-- Finite coefficient realization conjugates the endomorphism obtained by taking
an arbitrary open-adjunction transpose and restricting the proper image.
There is no proper/open comparison or etale-origin witness in this assertion.
Source: compactification-coherence proof, first two paragraphs; Stacks 00YV,
03DI, 03D6, 0D6D (blueprint: lem-sf-finite-ring-open-restriction-coordinates).

Proof: before deriving, finiteDirectImage_eq identifies the two direct images
with the same constant-section scalar map. The left-adjoint uniqueness comparison
finitePullbackIso therefore preserves its unit and counit. By its definition,
finiteOpenIso is the left-adjoint uniqueness comparison for the resulting open
adjunction, so it preserves the open unit. The fixed realization comparisons
cancel the realization unit in inverse image and extension by zero; their direct
image comparison is its counit-normalized mate. These equations descend to the
derived categories by the exact localization and right-derived factorization
identities. The section-normalized ordinary direct-image compositor is the
conjugate of geometricPullComposition. Consequently the restriction square is
the pasting of the pullback composition square and the proper counit square.
Apply the open unit square, naturality to the arbitrary arrow m, the restriction
square, and then the inverse open unit square. All inner coordinate isomorphisms
cancel, leaving conjugation by a. This uses no invertibility of m and no
properness of r. Identity maps, empty opens, and zero coefficients use precisely
the same unit/counit and inverse-pair identities. -/
theorem finiteOpenRestriction_endomorphism_coordinates
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
    (K : DerivedCategory (Sheaf (ProEt.topology X)
      (ModuleCat.{w + 1} (ULift.{w + 1} (Padic.coefficientExtensionRing l E (n + 1))))))
    (M : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (n + 1)))
    (a : M ≅ (sfIntrinsicDerivedEquivalence X
      (Padic.coefficientExtensionRing l E (n + 1))).functor.obj K)
    (m : (AlgebraicGeometry.ProEtale.openImmersionLowerShriek
        (ModuleCat.{w + 1} (ULift.{w + 1} (Padic.coefficientExtensionRing l E (n + 1))))
        d.i).mapDerivedCategory.obj K ⟶
      (AlgebraicGeometry.ProEtale.lowerStar
        (ModuleCat.{w + 1} (ULift.{w + 1} (Padic.coefficientExtensionRing l E (n + 1))))
        r.hom).rightDerivedFunctor.obj
        ((AlgebraicGeometry.ProEtale.openImmersionLowerShriek
          (ModuleCat.{w + 1} (ULift.{w + 1} (Padic.coefficientExtensionRing l E (n + 1))))
          c.i).mapDerivedCategory.obj K)) :
    let A := Padic.coefficientExtensionRing l E (n + 1)
    let B := ModuleCat.{w + 1} (ULift.{w + 1} A)
    let R := PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)
    let J₁ := (PurCompactSupport.openExtension R c.i).mapDerivedCategory
    let J₂ := (PurCompactSupport.openExtension R d.i).mapDerivedCategory
    let o₁ := J₁.mapIso a ≪≫ (finiteFixedOpenIso l E n c.i).app K
    let o₂ := J₂.mapIso a ≪≫ (finiteFixedOpenIso l E n d.i).app K
    let m' := o₂.hom ≫ (sfIntrinsicDerivedEquivalence d.Z A).functor.map m ≫
      (finiteFixedPushIso l E n r.hom).inv.app
        ((AlgebraicGeometry.ProEtale.openImmersionLowerShriek B c.i).mapDerivedCategory.obj K) ≫
      (PurCompactSupport.push R r.hom).map o₁.inv
    letI : IsIso (PurCompactSupport.openDerivedAdjunction R c.i).unit :=
      PurCompactSupport.openDerivedAdjunction_unit_isIso R c.i
    letI : IsIso (AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction
      B c.i).unit := Adjunction.isIso_mapDerivedCategoryAdjunction_unit
      (AlgebraicGeometry.ProEtale.openImmersionLowerShriekUpperStarAdjunction B c.i)
    ((PurCompactSupport.openDerivedAdjunction R d.i).homEquiv _ _ m' ≫
      PurCompactSupport.refinementRestriction R r hi M) ≫
        (asIso (PurCompactSupport.openDerivedAdjunction R c.i).unit).inv.app M =
      a.hom ≫ (sfIntrinsicDerivedEquivalence X A).functor.map
        (((AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction
            B d.i).homEquiv _ _ m ≫
          (AlgebraicGeometry.ProEtale.properOpenRestriction (ULift.{w + 1} A)
            r.hom c.i d.i r.i_hom).app
            ((AlgebraicGeometry.ProEtale.openImmersionLowerShriek B c.i
              ).mapDerivedCategory.obj K)) ≫
          (asIso (AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction
            B c.i).unit).inv.app K) ≫ a.inv := by
  revert hi K M a m
  rcases c with ⟨Zc, gc, ic, hc, hpc, hoc⟩
  rcases d with ⟨Zd, gd, jd, hd, hpd, hod⟩
  rcases r with ⟨v, hv, hvg⟩
  change Zc ⟶ Zd at v
  change ic ≫ v = jd at hv
  change v ≫ gd = gc at hvg
  subst jd
  intro hi K M a m
  let c : Compactification f := ⟨Zc, gc, ic, hc, hpc, hoc⟩
  let d : Compactification f := ⟨Zd, gd, ic ≫ v, hd, hpd, hod⟩
  let r : c.Refinement d := ⟨v, rfl, hvg⟩
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let B := ModuleCat.{w + 1} (ULift.{w + 1} A)
  let R := PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)
  let EX := (sfIntrinsicDerivedEquivalence X A).functor
  let EC := (sfIntrinsicDerivedEquivalence c.Z A).functor
  let ED := (sfIntrinsicDerivedEquivalence d.Z A).functor
  let J₁ := (PurCompactSupport.openExtension R c.i).mapDerivedCategory
  let J₂ := (PurCompactSupport.openExtension R d.i).mapDerivedCategory
  let P₁ := PurCompactSupport.pull R c.i
  let P₂ := PurCompactSupport.pull R d.i
  let Q := PurCompactSupport.push R r.hom
  let F₁ := (ProEtale.openImmersionLowerShriek B c.i).mapDerivedCategory
  let F₂ := (ProEtale.openImmersionLowerShriek B d.i).mapDerivedCategory
  let U₁ := (ProEtale.upperStar B c.i).mapDerivedCategory
  let U₂ := (ProEtale.upperStar B d.i).mapDerivedCategory
  let P := (ProEtale.lowerStar B r.hom).rightDerivedFunctor
  let ar₁ := PurCompactSupport.openDerivedAdjunction R c.i
  let ar₂ := PurCompactSupport.openDerivedAdjunction R d.i
  let af₁ := ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction B c.i
  let af₂ := ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction B d.i
  let : IsIso ar₁.unit := PurCompactSupport.openDerivedAdjunction_unit_isIso R c.i
  let : IsIso af₁.unit := Adjunction.isIso_mapDerivedCategoryAdjunction_unit
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction B c.i)
  let o₁ := J₁.mapIso a ≪≫ (finiteFixedOpenIso l E n c.i).app K
  let o₂ := J₂.mapIso a ≪≫ (finiteFixedOpenIso l E n d.i).app K
  let ρ : Q ⋙ P₂ ⟶ P₁ :=
    Functor.whiskerLeft Q (PurCompactSupport.refinementPull R r hi).hom ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (proEtaleRingDerivedAdjunction r.hom
        (R.ring d.Z) (R.ring c.Z) (R.pull r.hom)).counit P₁
  have h₁ : ar₁.unit.app M ≫ P₁.map o₁.hom =
      a.hom ≫ EX.map (af₁.unit.app K) ≫
        (finiteDerivedPullCoordinates l E n c.i).inv.app (F₁.obj K) := by
    change ar₁.unit.app M ≫ P₁.map
      (J₁.map a.hom ≫ (finiteFixedOpenIso l E n c.i).hom.app K) = _
    rw [P₁.map_comp, ← Category.assoc]
    have hn := ar₁.unit.naturality a.hom
    dsimp only [Functor.id_map, Functor.comp_map] at hn
    rw [← hn, Category.assoc, finite_open_unit_derived l E n c.i K]
  have h₂ : ar₂.unit.app M ≫ P₂.map o₂.hom =
      a.hom ≫ EX.map (af₂.unit.app K) ≫
        (finiteDerivedPullCoordinates l E n d.i).inv.app (F₂.obj K) := by
    change ar₂.unit.app M ≫ P₂.map
      (J₂.map a.hom ≫ (finiteFixedOpenIso l E n d.i).hom.app K) = _
    rw [P₂.map_comp, ← Category.assoc]
    have hn := ar₂.unit.naturality a.hom
    dsimp only [Functor.id_map, Functor.comp_map] at hn
    rw [← hn, Category.assoc, finite_open_unit_derived l E n d.i K]
  have ht := restriction_endomorphism_coordinates EX EC ED U₁ U₂ P P₁ P₂ Q
    (finiteFixedPushIso l E n r.hom)
    (finiteDerivedPullCoordinates l E n c.i) (finiteDerivedPullCoordinates l E n d.i)
    (ProEtale.properOpenRestriction (ULift.{w + 1} A) r.hom c.i d.i r.i_hom) ρ a
    ((asIso af₁.unit).app K) (af₂.unit.app K)
    ((asIso ar₁.unit).app M) (ar₂.unit.app M) o₁ o₂ h₁ h₂
    (finite_restriction_coordinates l E n r hi (F₁.obj K)) m
  simpa only [Adjunction.homEquiv_unit, Category.assoc, ρ,
    Iso.app_inv, Iso.app_hom, Functor.id_obj, Functor.comp_obj,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    PurCompactSupport.refinementRestriction] using ht

end WeilConjectures.ConstructibleExceptionalCoefficients
