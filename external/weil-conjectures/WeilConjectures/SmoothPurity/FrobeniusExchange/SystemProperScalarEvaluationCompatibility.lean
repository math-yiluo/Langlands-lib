/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FrobeniusExchange.SystemOperationExchangeRealization
public import WeilConjectures.SmoothPurity.FrobeniusExchange.SystemScalarFiniteEvaluation

/-! # The scalar/pullback compatibility square used by proper evaluation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FrobeniusExchange
open AlgebraicGeometry.Scheme.FiniteCompactScalar
open WeilConjectures.SemilinearSections

/-- The evaluated scalar/pullback cube required by the mate-pasting proof.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 06YY, 07A6 and 0941.
(blueprint: lem-sf-system-proper-scalar-evaluation-compatibility).

This is the square compatibility clause in the proof of the proper scalar
evaluation formula.  It is stated separately so that the mate calculation in
`systemDirectScalar_finiteEvaluation` is a formal consequence of
`SemilinearSections.evaluation_mate`.

Proof plan: take the scalar transpose of the ordinary scalar/pullback comparison.
Its tensor-unit normalization identifies it with the identity-on-sections
restriction/direct-image square. On complexes, the universal scalar counits
identify this transpose with the specified derived scalar adjunction. Localize
using one flat-term K-flat resolution; pullback and finite evaluation preserve
these representatives. The scalar evaluation comparisons preserve transposes
because both adjoint-uniqueness maps do. At finite coefficients, transpose the
normalized direct-image restriction comparison first under scalar adjunctions
and then under geometric adjunctions; the ordinary units and counits and the
K-injective normalization of sfDerivedImageRestriction identify this double
mate with the finite tensor/pullback square. Naturality transports the ordinary
commuting tensor/evaluation square through the cochain counits and the exact
localization factors. Cancel these isomorphisms on the common K-flat model,
then use naturality along the resolution to obtain the displayed equation on
all derived systems. This uses neither quotient flatness nor faithfulness of
evaluation, and includes n = 0, identity embeddings and empty schemes.
-/
-- STATEMENT-DISPUTED: the former statement allowed an arbitrary `a`, although its
-- left side is fixed. The repaired statement specifies the double mate used by its caller.
theorem systemProperScalarEvaluation_compatibility
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
    letI := Padic.finite_coefficientExtensionRing l L (n + 1) (Nat.succ_pos n)
    let levelE := (sfIntrinsicConstantModuleAdjunction f
      (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategoryRightDerivedAdjunction
    let levelL := (sfIntrinsicConstantModuleAdjunction f
      (Padic.coefficientExtensionRing l L (n + 1))).mapDerivedCategoryRightDerivedAdjunction
    let φ := integralScalarQuotientMap l E L ι n
    let scalarMate := ((mateEquiv
      (pbcDerivedScalarAdjunction (scalarRingMap φ X))
      (pbcDerivedScalarAdjunction (scalarRingMap φ Y))).symm
      (TwoSquare.mk _ _ _ _ (sfDerivedImageRestriction f φ).hom))
    let a := (mateEquiv levelE levelL).symm scalarMate
    ∀ A : coefficientSequenceDerived l E Y,
      (coefficientSequenceDerivedEvaluation l L X n).map
          ((integralComparisonSystemScalarPullback l E L ι f).inv.app A) ≫
        (systemScalarFiniteEvaluation l E L ι X n).hom.app
          ((integralComparisonDerivedSequencePullback l E f).obj A) ≫
        (pbcDerivedExtend
            (scalarRingMap (integralScalarQuotientMap l E L ι n) X)).map
          ((systemPullEvaluation l E f n).inv.app A) =
      (systemPullEvaluation l L f n).inv.app
          ((integralComparisonDerivedSequenceScalar l E L ι Y).obj A) ≫
        (sfIntrinsicDerivedPullback (Padic.coefficientExtensionRing l L (n + 1)) f).map
          ((systemScalarFiniteEvaluation l E L ι Y n).hom.app A) ≫
        a.app ((coefficientSequenceDerivedEvaluation l E Y n).obj A) := by sorry

end WeilConjectures.FrobeniusExchange
