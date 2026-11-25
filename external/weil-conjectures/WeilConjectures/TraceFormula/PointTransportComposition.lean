/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ZetaWeil.FrobeniusPointTransport
public import WeilConjectures.ProperBaseChange.IntegralFinitePullbackComposition

/-!
# Composition of finite-level point transports

Source: Deligne, Weil II (1.1.7), printed pp. 150--151; the finite-level refinement
of the proof of blueprint lemma-scheme-frobenius-geometric-frobenius--3; Stacks
Tags 03CE, 06UM, 015F and 0D6D (blueprint: lem-trf-point-transport-composition).

The helpers spell out the recipe in the statement for each power of the fixed
geometric Frobenius. The positive coefficient exponent is indexed by n + 1.
The composition comparison is expressed in the recorded intrinsic finite-module
presentation, with its ordinary comparison and exact localization comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
/-- The unit-normalized identification of the intrinsic finite pullback with the
recorded tensor pullback. Both factors are the existing adjunction comparisons;
no isomorphism is chosen here.
Source: Stacks 03D3 and 0D6D; the recorded finite composition interface
(blueprint: lem-trf-point-transport-composition). -/
def pointPowerPullbackModel (n : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    finiteDerivedPullback l E n f ≅
      proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1)) f :=
  letI : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  Functor.mapDerivedCategoryNatIso
    ((inverseImageFiniteIntrinsicPullbackComparison f
      (Padic.coefficientExtensionRing l E (n + 1))).symm ≪≫
        integralFinitePullbackModel l E f n)

end WeilConjectures
