/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurStrictScalar.StrictScalarFiniteEvaluationTransport

/-! # Finite proper and open comparisons used by native support evaluation

Source: Stacks 03DI, 0D6E and 0E8I.
(blueprint: def-pur-native-geometric-finite-evaluation-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Native proper evaluation, expressed in the finite coefficient model.
Source: Stacks 0D6E (blueprint: def-pur-native-geometric-finite-evaluation-data). -/
def nativeFiniteProper {X Y : Scheme.{u}} (g : X ⟶ Y) (n : ℕ) :
    ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) g ⋙
      coefficientSequenceDerivedEvaluation.{u, u} l E Y n ≅
    coefficientSequenceDerivedEvaluation.{u, u} l E X n ⋙
      proEtaleRingDerivedDirectImage g
        ((PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)).ring Y)
        ((PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)).ring X)
        ((PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)).pull g) :=
  haveI := proEtaleConstantModuleDirectImage_additive g
    (Padic.coefficientExtensionRing l E (n + 1))
  ProEtale.VaryingRing.evalP (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) g n ≪≫
    Functor.isoWhiskerLeft _ (Functor.rightDerivedFunctorNatIso
      (compactSupportDirectModel g (Padic.coefficientExtensionRing l E (n + 1)))) ≪≫
    Functor.isoWhiskerLeft _ (Functor.rightDerivedFunctorNatIso
      (eqToIso (PurCompactSupport.finiteDirectImage_eq l E n g))).symm

/-- Native open evaluation, expressed in the finite coefficient model.
Source: Stacks 03DI (blueprint: def-pur-native-geometric-finite-evaluation-data). -/
def nativeFiniteOpen {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (n : ℕ) :
    ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) j ⋙
      coefficientSequenceDerivedEvaluation.{u, u} l E Y n ≅
    coefficientSequenceDerivedEvaluation.{u, u} l E X n ⋙
      (PurCompactSupport.openExtension
        (PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)) j).mapDerivedCategory :=
  haveI := sfIntrinsicExtensionByZero_additive j
    (Padic.coefficientExtensionRing l E (n + 1))
  haveI := (sfIntrinsicExtensionByZero_exact j
    (Padic.coefficientExtensionRing l E (n + 1))).2.1
  haveI := (sfIntrinsicExtensionByZero_exact j
    (Padic.coefficientExtensionRing l E (n + 1))).2.2
  ProEtale.VaryingRing.evalJ (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) j n ≪≫
    Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryNatIso
      (compactSupportOpenModel j (Padic.coefficientExtensionRing l E (n + 1)))) ≪≫
    Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryNatIso
      (PurCompactSupport.finiteOpenIso l E n j)).symm

/-- Positive restriction through proper image, with the fixed quotient identification.
Source: Stacks 0D6E (blueprint: def-pur-native-geometric-finite-evaluation-data). -/
def finiteProperRestriction {X Y : Scheme.{u}} (g : X ⟶ Y) (n : ℕ) :
    positiveRestriction l E X (n + 1) (Nat.le_add_left 1 n) ⋙
      proEtaleRingDerivedDirectImage g
        ((constants l E).ring Y) ((constants l E).ring X) ((constants l E).pull g) ≅
    proEtaleRingDerivedDirectImage g
        ((PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)).ring Y)
        ((PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)).ring X)
        ((PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)).pull g) ⋙
      positiveRestriction l E Y (n + 1) (Nat.le_add_left 1 n) :=
  let a := constantFiniteChange l E (n + 1) (Nat.le_add_left 1 n)
  let C := constants l E
  let B := PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)
  Functor.isoWhiskerRight
      (positiveRestrictionIdentification l E X (n + 1) (Nat.le_add_left 1 n))
      (proEtaleRingDerivedDirectImage g (C.ring Y) (C.ring X) (C.pull g)) ≪≫
    (proEtaleRingRestrictionDerivedDirectImage g
      (C.ring Y) (B.ring Y) (C.ring X) (B.ring X)
      (a.map Y) (a.map X) (C.pull g) (B.pull g) (a.square g)).symm ≪≫
    Functor.isoWhiskerLeft
      (proEtaleRingDerivedDirectImage g (B.ring Y) (B.ring X) (B.pull g))
      (positiveRestrictionIdentification l E Y (n + 1) (Nat.le_add_left 1 n)).symm

/-- Positive restriction through open extension, with the fixed quotient identification.
Source: Stacks 0E8I (blueprint: def-pur-native-geometric-finite-evaluation-data). -/
def finiteOpenRestriction {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (n : ℕ) :
    positiveRestriction l E X (n + 1) (Nat.le_add_left 1 n) ⋙
      (PurCompactSupport.openExtension (constants l E) j).mapDerivedCategory ≅
    (PurCompactSupport.openExtension
        (PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)) j).mapDerivedCategory ⋙
      positiveRestriction l E Y (n + 1) (Nat.le_add_left 1 n) :=
  let a := constantFiniteChange l E (n + 1) (Nat.le_add_left 1 n)
  let C := constants l E
  let B := PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)
  Functor.isoWhiskerRight
      (positiveRestrictionIdentification l E X (n + 1) (Nat.le_add_left 1 n))
      (PurCompactSupport.openExtension C j).mapDerivedCategory ≪≫
    PurCompactSupport.openRestriction a j ≪≫
    Functor.isoWhiskerLeft (PurCompactSupport.openExtension B j).mapDerivedCategory
      (positiveRestrictionIdentification l E Y (n + 1) (Nat.le_add_left 1 n)).symm

end WeilConjectures.PurStrictScalar
