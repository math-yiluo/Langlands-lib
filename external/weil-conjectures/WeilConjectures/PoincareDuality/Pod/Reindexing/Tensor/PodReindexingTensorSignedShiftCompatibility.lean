/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.PodCompletionReindexShifts
import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingLimitSignedShift
import WeilConjectures.PoincareDuality.Pod.PodLimitSignedShiftNormalization
import WeilConjectures.CategoryTheory.Adjunction.PoincareDuality.ReductionShiftFromLimitMate

/-! # Compatibility of signed tensor shifts with reindexing

This module records the fixed-model compatibility calculation separately from
the construction of the signed tensor shift models.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local instance 10000] WeilConjectures.podLimitCommShift
  WeilConjectures.podOrdinaryCommShift WeilConjectures.podSystemCommShift
  WeilConjectures.podReductionCommShift
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.podReindexCalculus

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

-- Keep the coefficient universe explicit during sheafification synthesis.
private instance (priority := 20000) fixedAbSheafify (Z : Scheme.{u}) :
    HasSheafify (ProEt.topology Z) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} Z

private instance (priority := 20000) fixedAbBijective (Z : Scheme.{u}) :
    (ProEt.topology Z).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} Z

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

-- The shorter proof retains every hypothesis of the assigned statement.
set_option linter.unusedVariables false in
/-- Compatibility of fixed signed tensor shifts with a normalized reindexing.

Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 07A4, 0941
(blueprint: lem-pod-reindexing-tensor-signed-shifts-core-compatibility-r3).

Proof: the coordinate laws identify each prescribed signed Roos shift with
its native comparison. K-injective normalization of the limit-to-Roos map
then gives both fixed limit shift equations. The restricted generator formula,
Roos naturality and the Roos shift law give the strict reindexing square;
localization and LimitModel identify it with the shift square for D.limit.
Finally, the Unit law identifies the inverse reduction comparison with the
adjunction mate of D.limit. The shift-mate identity gives reduction compatibility.
No boundedness or extra coefficient hypothesis is used.
-/
theorem podReindexingTensorSignedShiftCompatibility
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (hT : PodCompletedTensorReindex.Laws l E g D T)
    (SY : PodTensorSignedShift l E Y) (SX : PodTensorSignedShift l E X)
    (hSYg : SY.Generators l E) (hSXg : SX.Generators l E)
    (hSYm : SY.Model l E D.shiftSource) (hSXm : SX.Model l E D.shiftTarget) :
    NatTrans.CommShift D.reduction.hom ℤ ∧
      NatTrans.CommShift D.limit.hom ℤ ∧
      PodLimitSignedShift l E Y D.sourceRoos D.shiftSource ∧
      PodLimitSignedShift l E X D.targetRoos D.shiftTarget := by
  obtain ⟨hunits, heval, hproj, hunit, hcounit, hcomplete, hquot, htrans, hfinite,
    hboundary, hfst, hsnd, hnat, hSY, hSX, hshift, hgen, hmodel, hpull⟩ := hD
  have hlim := podReindexingLimitSignedShift l E g D hnat hshift hgen hmodel hSY hSX
  let adjY := (podReindexCalculus l E Y).adjunction
  let adjX := (podReindexCalculus l E X).adjunction
  let G := podOrdinaryReindex l E g
  let P := integralComparisonDerivedSequencePullback l E g
  have hred := Adjunction.iso_commShift_of_unit_square adjY adjX G P
    (fun n ↦ Adjunction.LeftAdjointCommShift.compatibilityUnit_iso adjY n)
    (fun n ↦ Adjunction.LeftAdjointCommShift.compatibilityUnit_iso adjX n)
    D.reduction D.limit.hom hunit
  exact ⟨hred, hlim, podLimitSignedShiftNormalization l E Y D.sourceRoos D.shiftSource hSY,
    podLimitSignedShiftNormalization l E X D.targetRoos D.shiftTarget hSX⟩

end WeilConjectures
