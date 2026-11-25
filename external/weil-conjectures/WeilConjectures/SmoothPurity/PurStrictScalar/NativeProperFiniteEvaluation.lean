/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurStrictScalar.NativeGeometricFiniteEvaluationData

/-! # Proper finite evaluation of native systems

Source: Stacks 03DI, 0D6E and 0E8I.
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

/-- Proper evaluation commutes with restriction from the native system to constants.
Source: Stacks 0D6E, 07A6, 0940; the proper square in the proof of
lem-pur-native-support-finite-evaluation.
(blueprint: lem-pur-native-proper-finite-evaluation).
Proof: form the square of the native sequence-site direct image, constant tower
restriction, level evaluation and finite scalar restriction. The ordinary square
is identity on sections: pushforward and scalar restriction retain the same
sections and the structural ring square identifies their actions. The normalized
right-derived squares commute by uniqueness with respect to the resolution units.
For varying-ring evaluation, use its definition as the right mate of evalG.
The derived-mate factorization theorem gives its resolution-unit equation. The
ordinary mate is the section-normalized moduleEvalP, because moduleEvalG was
constructed as its inverse mate and the mate equivalence cancels that pair.
The section-normalized finite direct-image model
comparison preserves that normalization. Apply the commuting cube theorem and
transport by positiveRestrictionIdentification. The two finite model comparisons
cancel, giving the displayed equality on every derived system, without assuming
that varying-ring evaluation preserves K-injectives. -/
theorem nativeProper_finiteEvaluation
    {X Y : Scheme.{u}} (g : X ⟶ Y) (n : ℕ)
    (N : coefficientSequenceDerived.{u, u} l E X) :
    (ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) Y n).map
        ((systemProper l E g).hom.app N) ≫
      (evalR (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g n).app
        ((systemU l E X).obj N) ≫
      (moduleDirectImage (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))
        g).rightDerivedFunctor.map ((evaluationRestriction l E X n).hom.app N) ≫
      (finiteProperRestriction l E g n).hom.app
        ((coefficientSequenceDerivedEvaluation.{u, u} l E X n).obj N) =
    (evaluationRestriction l E Y n).hom.app
        ((ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) g).obj N) ≫
      (finiteRestriction l E Y n).map ((nativeFiniteProper l E g n).hom.app N) := by
  sorry

end WeilConjectures.PurStrictScalar
