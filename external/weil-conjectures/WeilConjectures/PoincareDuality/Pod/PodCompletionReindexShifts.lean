/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodCompletedTensorReindex.PodCompletionTensorNormalization
public import Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-! # Signed shifts of normalized reindexing

Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 011G, 07A4, 0941 (blueprint: def-pod-completion-reindex-shifts).
The finite tensor generator formulas and both signed Roos coordinates determine
all shift maps before localization. Their representative squares fix the derived maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.integralCompletedTensor WeilConjectures.sfIntegralConstructible
  WeilConjectures.podReindexCalculus
universe t u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The canonical right-derived limit shift, after exact scalar restriction.
Source: Stacks 0941 (blueprint: def-pod-completion-reindex-shifts). -/
instance podLimitCommShift (W : Scheme.{t}) : (coefficientSequenceLimit l E W).CommShift ℤ :=
  by
    dsimp only [coefficientSequenceLimit, coefficientConstantTowerLimit]
    infer_instance

/-- Exact ordinary relabelling has its localization shift.
Source: Stacks 015F (blueprint: def-pod-completion-reindex-shifts). -/
instance podOrdinaryCommShift {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g] :
    (podOrdinaryReindex l E g).CommShift ℤ :=
  by
    dsimp only [podOrdinaryReindex]
    infer_instance

/-- Whole-system relabelling has the same localization shift.
Source: Stacks 015F (blueprint: def-pod-completion-reindex-shifts). -/
instance podSystemCommShift {X Y : Scheme.{t}} (g : X ⟶ Y) :
    (integralComparisonDerivedSequencePullback l E g).CommShift ℤ :=
  by
    dsimp only [integralComparisonDerivedSequencePullback]
    infer_instance

/-- The reduction shift is the mate of that same limit shift under the actual adjunction.
Source: Stacks 011G, 0941 (blueprint: def-pod-completion-reindex-shifts). -/
instance podReductionCommShift (W : Scheme.{t}) :
    (podReindexCalculus l E W).reduction.CommShift ℤ :=
  (podReindexCalculus l E W).adjunction.leftAdjointCommShift ℤ

/-- Exact restriction commutes with cochain shift before conversion to a tower.
Source: Stacks 011G, 0941 (blueprint: def-pod-completion-reindex-shifts). -/
def podRestrictionShift (W : Scheme.{t})
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ) (r : ℤ) :
    podRestrictedTower l E (C⟦r⟧) ≅ podShiftTower (podRestrictedTower l E C) r :=
  HomologicalComplex.complexOfFunctorsToFunctorToComplex.mapIso
    ((((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).commShiftIso r).app C)

/-- The canonical limit shift is represented by the specified signed Roos shift.
Source: Stacks 011G, 0941 (blueprint: def-pod-completion-reindex-shifts). -/
def PodLimitSignedShift (W : Scheme.{t}) (ρ : IntegralComparisonRoosModel l E W)
    (S : PodSignedRoosShift (scalarReductionSource l E W)) : Prop :=
  ∀ (C : CochainComplex (coefficientSequenceModules l E W) ℤ) (r : ℤ),
    HEq ((coefficientSequenceLimit l E W).map ((DerivedCategory.Q.commShiftIso r).inv.app C) ≫
        (podLimitRoos l E ρ (C⟦r⟧)).hom ≫
        DerivedCategory.Q.map
          (integralOperationsRoosFunctor.map (podRestrictionShift l E W C r).hom) ≫
        DerivedCategory.Q.map (S.comparison (podRestrictedTower l E C) r).hom ≫
        ((DerivedCategory.Q (C := scalarReductionSource l E W)).commShiftIso r).hom.app
          (integralOperationsRoos (podRestrictedTower l E C)))
      (((coefficientSequenceLimit l E W).commShiftIso r).hom.app (DerivedCategory.Q.obj C) ≫
        (podLimitRoos l E ρ C).hom⟦r⟧')

/-- Shift a good complex; preservation is part of the model data, not a hypothesis.
The tensor shifts are retained both on entire strict towers and on derived objects.
Source: Stacks 07A4, 011G, 0941 (blueprint: def-pod-completion-reindex-shifts). -/
structure PodTensorSignedShift (W : Scheme.{u}) where
  /-- Flat terms and K-flatness are stable under every integer shift. -/
  good : ∀ P : (integralOperationsGoodComplex l E W).FullSubcategory,
    ∀ r : ℤ, integralOperationsGoodComplex l E W (P.obj⟦r⟧)
  /-- Shift the first tensor factor on the actual strict quotient tower. -/
  leftTower : ∀ (P Q : (integralOperationsGoodComplex l E W).FullSubcategory) (r : ℤ),
    (integralOperationsTensorTowerFunctor l E W).obj (P.obj⟦r⟧,Q.obj) ≅
      podShiftTower ((integralOperationsTensorTowerFunctor l E W).obj (P.obj,Q.obj)) r
  /-- Shift the second factor, retaining the Koszul sign. -/
  rightTower : ∀ (P Q : (integralOperationsGoodComplex l E W).FullSubcategory) (r : ℤ),
    (integralOperationsTensorTowerFunctor l E W).obj (P.obj,Q.obj⟦r⟧) ≅
      podShiftTower ((integralOperationsTensorTowerFunctor l E W).obj (P.obj,Q.obj)) r
  /-- Derived first-factor shift, for every identification of a shifted input. -/
  left : ∀ (M N M' : sfIntegralConstructibleCategory l E W) (r : ℤ)
    (_e : M'.obj ≅ M.obj⟦r⟧),
    (integralCompletedTensor l E W).obj (M'.obj,N.obj) ≅
      ((integralCompletedTensor l E W).obj (M.obj,N.obj))⟦r⟧
  /-- Derived second-factor shift, with the same arbitrary identification convention. -/
  right : ∀ (M N N' : sfIntegralConstructibleCategory l E W) (r : ℤ)
    (_e : N'.obj ≅ N.obj⟦r⟧),
    (integralCompletedTensor l E W).obj (M.obj,N'.obj) ≅
      ((integralCompletedTensor l E W).obj (M.obj,N.obj))⟦r⟧

namespace PodTensorSignedShift
variable {W : Scheme.{u}} (S : PodTensorSignedShift l E W)
  (ρ : PodSignedRoosShift (scalarReductionSource l E W))

/-- Both homogeneous generator rules, including the sign when the second factor shifts.
`HEq` only handles the equal integer indices (p+r)+q=(p+q)+r; no map is forgotten.
Source: Stacks 011G, 07A4 (blueprint: def-pod-completion-reindex-shifts). -/
def Generators : Prop :=
  (∀ (P Q : (integralOperationsGoodComplex l E W).FullSubcategory)
    (n : ℕ) (p q r : ℤ) (U : W.ProEtᵒᵖ)
    (x : (((unrestrictedIntegralFiniteComplex l E W n).obj P.obj).X (p+r)).val.obj U)
    (y : (((unrestrictedIntegralFiniteComplex l E W n).obj Q.obj).X q).val.obj U),
    HEq ((((S.leftTower P Q r).hom.app (op n)).f (p+q)).val.app U
      (integralOperationsTotalTensorSection l E W n (P.obj⟦r⟧) Q.obj p q U x y))
      (integralOperationsTotalTensorSection l E W n P.obj Q.obj (p+r) q U x y)) ∧
  (∀ (P Q : (integralOperationsGoodComplex l E W).FullSubcategory)
    (n : ℕ) (p q r : ℤ) (U : W.ProEtᵒᵖ)
    (x : (((unrestrictedIntegralFiniteComplex l E W n).obj P.obj).X p).val.obj U)
    (y : (((unrestrictedIntegralFiniteComplex l E W n).obj Q.obj).X (q+r)).val.obj U),
    HEq ((((S.rightTower P Q r).hom.app (op n)).f (p+q)).val.app U
      (integralOperationsTotalTensorSection l E W n P.obj (Q.obj⟦r⟧) p q U x y))
      ((p*r).negOnePow •
        integralOperationsTotalTensorSection l E W n P.obj Q.obj p (q+r) U x y))

/-- Both derived shift maps are the localizations of those tower maps followed by the
same signed Roos shift. Every good representative and every derived presentation is tested.
Source: Stacks 07A4, 0941 (blueprint: def-pod-completion-reindex-shifts). -/
def Model : Prop :=
  ∀ (P Q : (integralOperationsGoodComplex l E W).FullSubcategory) (r : ℤ)
    (M N M' N' : sfIntegralConstructibleCategory l E W)
    (eP : DerivedCategory.Q.obj P.obj ≅ M.obj)
    (eQ : DerivedCategory.Q.obj Q.obj ≅ N.obj)
    (eP' : DerivedCategory.Q.obj (P.obj⟦r⟧) ≅ M'.obj)
    (eQ' : DerivedCategory.Q.obj (Q.obj⟦r⟧) ≅ N'.obj)
    (a : M'.obj ≅ M.obj⟦r⟧) (b : N'.obj ≅ N.obj⟦r⟧),
    eP'.hom ≫ a.hom = (DerivedCategory.Q.commShiftIso r).hom.app P.obj ≫ eP.hom⟦r⟧' →
    eQ'.hom ≫ b.hom = (DerivedCategory.Q.commShiftIso r).hom.app Q.obj ≫ eQ.hom⟦r⟧' →
    ((integralCompletedTensor l E W).map (Prod.mkHom eP'.hom eQ.hom) ≫
      (S.left M N M' r a).hom =
      (integralCompletedTensorComparison l E W).hom.app (⟨P.obj⟦r⟧,S.good P r⟩,Q) ≫
      DerivedCategory.Q.map (integralOperationsRoosFunctor.map (S.leftTower P Q r).hom) ≫
      DerivedCategory.Q.map
        (ρ.comparison ((integralOperationsTensorTowerFunctor l E W).obj (P.obj,Q.obj)) r).hom ≫
      (DerivedCategory.Q.commShiftIso r).hom.app _ ≫
      (integralCompletedTensorComparison l E W).inv.app (P,Q)⟦r⟧' ≫
      ((integralCompletedTensor l E W).map (Prod.mkHom eP.hom eQ.hom))⟦r⟧') ∧
    ((integralCompletedTensor l E W).map (Prod.mkHom eP.hom eQ'.hom) ≫
      (S.right M N N' r b).hom =
      (integralCompletedTensorComparison l E W).hom.app (P,⟨Q.obj⟦r⟧,S.good Q r⟩) ≫
      DerivedCategory.Q.map (integralOperationsRoosFunctor.map (S.rightTower P Q r).hom) ≫
      DerivedCategory.Q.map
        (ρ.comparison ((integralOperationsTensorTowerFunctor l E W).obj (P.obj,Q.obj)) r).hom ≫
      (DerivedCategory.Q.commShiftIso r).hom.app _ ≫
      (integralCompletedTensorComparison l E W).inv.app (P,Q)⟦r⟧' ≫
      ((integralCompletedTensor l E W).map (Prod.mkHom eP.hom eQ.hom))⟦r⟧')

end PodTensorSignedShift

/-- The actual reduction and limit maps commute with the canonical shifts; both tensor
factor equations use the same signed representative-normalized shift maps.
Source: blueprint Steps 1 and 5; Stacks 011G, 07A4, 0941
(blueprint: def-pod-completion-reindex-shifts). -/
def PodReindexSignedShifts {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (T : PodCompletedTensorReindex l E g D)
    (SY : PodTensorSignedShift l E Y) (SX : PodTensorSignedShift l E X) : Prop :=
  NatTrans.CommShift D.reduction.hom ℤ ∧ NatTrans.CommShift D.limit.hom ℤ ∧
  PodLimitSignedShift l E Y D.sourceRoos D.shiftSource ∧
  PodLimitSignedShift l E X D.targetRoos D.shiftTarget ∧
  SY.Generators l E ∧ SX.Generators l E ∧
  SY.Model l E D.shiftSource ∧ SX.Model l E D.shiftTarget ∧
  ∀ (M N M' N' : sfIntegralConstructibleCategory l E Y) (r : ℤ)
    (a : M'.obj ≅ M.obj⟦r⟧) (b : N'.obj ≅ N.obj⟦r⟧),
  ((podOrdinaryReindex l E g).map (SY.left M N M' r a).hom ≫
      ((podOrdinaryReindex l E g).commShiftIso r).hom.app _ ≫ (T.tensor M N).hom⟦r⟧' =
    (T.tensor M' N).hom ≫
      (SX.left ⟨_,T.constructible M⟩ ⟨_,T.constructible N⟩ ⟨_,T.constructible M'⟩ r
        ((podOrdinaryReindex l E g).mapIso a ≪≫
          ((podOrdinaryReindex l E g).commShiftIso r).app M.obj)).hom) ∧
  ((podOrdinaryReindex l E g).map (SY.right M N N' r b).hom ≫
      ((podOrdinaryReindex l E g).commShiftIso r).hom.app _ ≫ (T.tensor M N).hom⟦r⟧' =
    (T.tensor M N').hom ≫
      (SX.right ⟨_,T.constructible M⟩ ⟨_,T.constructible N⟩ ⟨_,T.constructible N'⟩ r
        ((podOrdinaryReindex l E g).mapIso b ≪≫
          ((podOrdinaryReindex l E g).commShiftIso r).app N.obj)).hom)

end WeilConjectures
