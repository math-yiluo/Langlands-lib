/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Finite.FiniteRingOrdinaryOpenUnitCoordinates
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.Finite.FiniteRingPullCoordinates

import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.Normalization.ExactClopenNormalization
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

private theorem fixed_open_exact_adjunction
    (A : Type w) [CommRing A] {X Y : Scheme.{w}} (j : X ⟶ Y) [IsOpenImmersion j] :
    ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{w + 1} (ULift.{w + 1} A)) j =
      exactLocalizationDerivedAdjunction
        (ProEtale.openImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{w + 1} (ULift.{w + 1} A)) j) := by
  let a := ProEtale.openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{w + 1} (ULift.{w + 1} A)) j
  let L := ProEtale.openImmersionLowerShriek
    (ModuleCat.{w + 1} (ULift.{w + 1} A)) j
  have he : a.mapDerivedCategoryRightDerivedAdjunction =
      a.derivedAdjunction.ofNatIsoLeft L.leftDerivedFunctorIsoMapDerivedCategory := by
    refine (a.mapHomotopyCategory (.up ℤ)).derived_eq_ofNatIsoLeft
      (HomotopyCategory.quasiIso _ (.up ℤ))
      (HomotopyCategory.quasiIso _ (.up ℤ)) _ _ _
      L.leftDerivedFunctorIsoMapDerivedCategory.symm ?_
    ext H
    simp only [Iso.symm_hom, NatTrans.comp_app, Functor.whiskerLeft_app]
    rw [← L.leftDerivedFunctorIsoMapDerivedCategory_hom_fac]
    rw [NatTrans.comp_app, Functor.whiskerLeft_app, Iso.inv_hom_id_app_assoc]
  rw [← AlgebraicGeometry.ProEtale.SemilinearProperOpen.Normalization.exact_adjunction_eq a,
    he]
  rfl

/-- The finite open-extension comparison preserves the specified derived open unit.
Source: compactification-coherence proof, first paragraph; Stacks 03DI and 015F
(blueprint: lem-sf-finite-ring-open-unit-coordinates).

Proof: finiteOpenIso is the left-adjoint uniqueness comparison for the ring open
adjunction transported by finitePullbackIso. The ordinary open_unit_coordinates
identity therefore gives its unit square in realization coordinates. Compare
the specified derived open adjunction with exactLocalizationDerivedAdjunction
using the left-derived factorization and exact_adjunction_eq. Localize the
ordinary unit square via exact_unit_square. The derived comparison of a composite
is derived_square_left_comp, which identifies the open comparison with
finiteFixedOpenIso. The inverse pull square is inverse finiteDerivedPullCoordinates.
Substitution yields the stated unit equation, including the identity and empty open. -/
theorem finite_open_unit_derived
    (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ)
    {X Y : Scheme.{w}} (j : X ⟶ Y) [IsOpenImmersion j]
    (K : DerivedCategory (Sheaf (ProEt.topology X)
      (ModuleCat.{w + 1} (ULift.{w + 1} (Padic.coefficientExtensionRing l E (n + 1)))))) :
    let A := Padic.coefficientExtensionRing l E (n + 1)
    let R := PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)
    let EX := sfIntrinsicDerivedEquivalence X A
    let J := ProEtale.openImmersionLowerShriek (ModuleCat.{w + 1} (ULift.{w + 1} A)) j
    (PurCompactSupport.openDerivedAdjunction R j).unit.app (EX.functor.obj K) ≫
        (PurCompactSupport.pull R j).map ((finiteFixedOpenIso l E n j).hom.app K) =
      EX.functor.map ((ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{w + 1} (ULift.{w + 1} A)) j).unit.app K) ≫
        (finiteDerivedPullCoordinates l E n j).inv.app (J.mapDerivedCategory.obj K) := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let R := PurCompactSupport.finite l E (n + 1) (Nat.succ_pos n)
  let : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.le_add_left 1 n)
  let := sfIntrinsicModuleEquivalence_functor_additive A X
  let := sfIntrinsicModuleEquivalence_functor_additive A Y
  let EX := sfIntrinsicModuleEquivalence X A
  let J := ProEtale.openImmersionLowerShriek (ModuleCat.{w + 1} (ULift.{w + 1} A)) j
  let z := PurCompactSupport.finiteOpenIso l E n j
  let o := Functor.isoWhiskerLeft EX.functor z ≪≫ FrobeniusExchange.fixedOpenModel A j
  have ht := exact_unit_square
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{w + 1} (ULift.{w + 1} A)) j)
    (PurCompactSupport.openAdjunction R j) (finitePullCoordinates l E n j).symm o
    (finite_open_unit_ordinary l E n j) K
  rw [← fixed_open_exact_adjunction A j] at ht
  have ho := derived_square_left_comp EX.functor J
    (sfIntrinsicModuleEquivalence Y A).functor z (FrobeniusExchange.fixedOpenModel A j)
  have hs : (Functor.mapDerivedCategorySquareIso
      (finitePullCoordinates l E n j).symm).hom =
      (finiteDerivedPullCoordinates l E n j).inv := by
    simp only [finiteDerivedPullCoordinates, Functor.mapDerivedCategorySquareIso,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      Functor.mapDerivedCategoryNatIso_symm, Category.assoc]
  rw [hs, show (Functor.mapDerivedCategorySquareIso o).hom =
      (finiteFixedOpenIso l E n j).hom by exact ho] at ht
  exact ht

end WeilConjectures.ConstructibleExceptionalCoefficients
