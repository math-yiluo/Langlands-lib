/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FrobeniusExchange.SystemOperationExchangeRealization
public import WeilConjectures.SmoothPurity.FrobeniusExchange.SystemScalarFiniteEvaluation
import WeilConjectures.SmoothPurity.FrobeniusExchange.SystemOpenScalarEvaluationCore

/-! # Evaluation of the open scalar mate

Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 03DI and 07A6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FrobeniusExchange
open AlgebraicGeometry.Scheme.FiniteCompactScalar

/-- The finite scalar transpose of the specified open restriction comparison.
Source: Stacks 03DI and 07A6 (blueprint: lem-sf-system-open-scalar-evaluation). -/
def finiteOpenScalar
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    (sfIntrinsicExtensionByZero j A).mapDerivedCategory ⋙
        pbcDerivedExtend (scalarRingMap φ Z) ⟶
      pbcDerivedExtend (scalarRingMap φ X) ⋙ (sfIntrinsicExtensionByZero j B).mapDerivedCategory :=
  ((mateEquiv (pbcDerivedScalarAdjunction (scalarRingMap φ X))
    (pbcDerivedScalarAdjunction (scalarRingMap φ Z))).symm
    (TwoSquare.mk _ _ _ _
      (Functor.mapDerivedCategorySquareIso (sfOpenRestriction j φ)).hom))

/-- Evaluation of open extension, inverse to the specified open-adjunction mate.
Source: Zheng 4.10 (blueprint: lem-sf-system-open-scalar-evaluation). -/
def systemOpenFiniteEvaluation
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] (n : ℕ) :
    systemDerivedOpen l E j ⋙ coefficientSequenceDerivedEvaluation l E Z n ≅
      coefficientSequenceDerivedEvaluation l E X n ⋙
        (sfIntrinsicExtensionByZero j
          (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory :=
  letI := systemOpenEvaluationInv_isIso l E j n
  (asIso (systemOpenEvaluationInv l E j n)).symm

/-- Evaluation takes the forward open system scalar map to the finite scalar transpose.

Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 03DI, 06YY and 07A6;
step 3, open factor, of lem-sf-compact-scalar-evaluation-square.
(blueprint: lem-sf-system-open-scalar-evaluation).

Proof: first compute the inverse mate defining systemOpenScalarInv. The exact ordinary
open adjunction evaluates with its original units and counits. Its scalar/pullback
comparison is the balanced tensor map on the open, and both extensions vanish off it.
Thus evaluation of the inverse mate is the inverse finite open scalar comparison,
through the scalar evaluation maps normalized by restriction transposition. Universal
cochain counits identify the generic scalar models with the fixed ones, and their
adjoint-uniqueness maps preserve this equation. Invert the two specified open evaluation
mates and the system open scalar mate. The inverse-pair identities and functoriality
of evaluation give the forward equation. Finally transpose under the finite scalar
adjunction: the finite open restriction map is the unique ordinary open comparison
normalized by its unit; the sectionwise tensor formula and triangle identity identify
its scalar transpose with the forward open scalar comparison. This is finiteOpenScalar.
Localization of the actual exact open functors retains these unit equations on all
unbounded complexes. Naturality moves the scalar evaluation maps to the displayed
ends. The calculation includes the empty open, identity open, zero complex and n=0;
no constructibility, boundedness, quotient-flatness or evaluation-faithfulness is used. -/
theorem systemOpenScalar_finiteEvaluation
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] (n : ℕ) (N : coefficientSequenceDerived l E X) :
    letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
    letI := Padic.finite_coefficientExtensionRing l L (n + 1) (Nat.succ_pos n)
    (coefficientSequenceDerivedEvaluation l L Z n).map
          ((systemOpenScalar l E L ι j).hom.app N) ≫
        (systemOpenFiniteEvaluation l L j n).hom.app
          ((integralComparisonDerivedSequenceScalar l E L ι X).obj N) ≫
        (sfIntrinsicExtensionByZero j
          (Padic.coefficientExtensionRing l L (n + 1))).mapDerivedCategory.map
            ((systemScalarFiniteEvaluation l E L ι X n).hom.app N) =
      (systemScalarFiniteEvaluation l E L ι Z n).hom.app ((systemDerivedOpen l E j).obj N) ≫
        (pbcDerivedExtend (scalarRingMap (integralScalarQuotientMap l E L ι n) Z)).map
          ((systemOpenFiniteEvaluation l E j n).hom.app N) ≫
        (finiteOpenScalar (integralScalarQuotientMap l E L ι n) j).app
          ((coefficientSequenceDerivedEvaluation l E X n).obj N) := by
  let _ := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  let _ := Padic.finite_coefficientExtensionRing l L (n + 1) (Nat.succ_pos n)
  haveI : IsIso (systemOpenScalarInv l E L ι j) :=
    systemOpenScalarInv_isIso l E L ι j
  have h := systemOpenScalarInv_finiteEvaluation_core l E L ι j n N
  dsimp only [systemOpenFiniteEvaluation, finiteOpenScalar] at h ⊢
  rw [h]
  rw [show (systemOpenScalar l E L ι j).hom.app N =
      (asIso (systemOpenScalarInv l E L ι j)).inv.app N by rfl]
  rw [show (systemOpenScalarInv l E L ι j).app N =
      (asIso (systemOpenScalarInv l E L ι j)).hom.app N by rfl]
  rw [← Category.assoc]
  rw [← (coefficientSequenceDerivedEvaluation l L Z n).map_comp]
  rw [Iso.inv_hom_id_app]
  rw [(coefficientSequenceDerivedEvaluation l L Z n).map_id, Category.id_comp]

end WeilConjectures.FrobeniusExchange
