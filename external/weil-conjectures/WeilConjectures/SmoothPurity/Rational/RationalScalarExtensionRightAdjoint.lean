/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.SmoothPurity.Rational.RationalScalarAmbientTrace
import WeilConjectures.SmoothPurity.Rational.RationalScalarRestrictionConstructible

/-! # The left adjoint to finite rational scalar extension

Source: Bhatt--Scholze, Lemma 6.7.2, Proposition 6.8.14(2), Remark 6.8.15;
the trace-dual-basis step of the finite coefficient argument.
(blueprint: lem-sf-rational-scalar-extension-right-adjoint).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

/-- Finite rational scalar extension is also a right adjoint.

Source: Bhatt--Scholze, Lemma 6.7.2, Proposition 6.8.14(2), Remark 6.8.15;
the trace argument in step 1 of lem-sf-rational-pullback-scalar-right-mate.
(blueprint: lem-sf-rational-scalar-extension-right-adjoint).

Proof: restrict a complex over the completed F coefficient sheaf along the
completed coefficient inclusion. This is exact. Since O_F is finite free over
O_E, restriction preserves finite generation and constructibility. The two
uniformizer filtrations are cofinal, so it preserves derived completeness too.
It therefore restricts to the integral constructible categories. Extend its
map on integral Hom groups to rational Hom groups by restricting the F-linear
maps to E-linear maps and inverting the uniformizer. Balancing is respected
because the two coefficient inclusions agree on O_E.

The extension F/E is finite separable, since both fields have characteristic
zero. Choose an E-basis b_i and its trace-dual basis c_i. The nondegenerate
trace pairing identifies Hom_E(F,E) with F. On complexes the unit of restriction
left adjoint to extension is m ↦ sum_i b_i tensor c_i m, and the counit is
z tensor m ↦ Tr_{F/E}(z)m. Choose a common nonzero denominator for the finitely
many coefficients in these formulas. The resulting integral morphisms give
well-defined rational morphisms, independent of denominator, and the two
dual-basis identities give both triangles. Finite free tensor agrees with the
recorded completed scalar construction on complete complexes by
finiteFreeCompletedScalarComparison; conjugate this adjunction by that
comparison and then by the normalized rational scalar comparison. This gives
a left adjoint to exactly the recorded scalar functor. The assertion is only
adjoint existence, not a choice of an arbitrary object from an existence
proof. Identity extensions, zero complexes and empty schemes obey the same
unit and counit formulas. -/
theorem rationalScalarExtension_isRightAdjoint
    (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F) (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] :
    (sfRationalScalarExtension l E W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι).IsRightAdjoint := by
  classical
  let T := sfRationalScalarExtension l E W 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι
  let IE := rationalScalarAmbientInclusion l E W
  let IF := rationalScalarAmbientInclusion l F W
  let fE := ScalarLocalization.fullyFaithfulFullSubcategoryInclusion
    (Padic.coefficientExtensionIntegers l E)
    (DerivedCategory (scalarReductionSource l E W)) (sfIntegralConstructible l E W)
    (Padic.coefficientExtensionUniformizer l E)
  let fF := ScalarLocalization.fullyFaithfulFullSubcategoryInclusion
    (Padic.coefficientExtensionIntegers l F)
    (DerivedCategory (scalarReductionSource l F W)) (sfIntegralConstructible l F W)
    (Padic.coefficientExtensionUniformizer l F)
  let Uobj (K : sfRationalConstructibleCategory l F W) :
      sfRationalConstructibleCategory l E W :=
    ⟨⟨(rationalScalarDerivedRestriction l E F ι W).obj K.obj.obj,
      rationalScalarDerivedRestriction_constructible l E F ι W K.obj⟩⟩
  have traceData := fun K : sfRationalConstructibleCategory l F W ↦
    rationalScalarAmbientTrace l E W F ι K.obj.obj
  let e (K : sfRationalConstructibleCategory l F W)
      (M : sfRationalConstructibleCategory l E W) :
      (Uobj K ⟶ M) ≃ (K ⟶ T.obj M) :=
    (fE.homEquiv).trans
      (((traceData K).choose M).trans fF.homEquiv.symm)
  have he (K : sfRationalConstructibleCategory l F W)
      (M N : sfRationalConstructibleCategory l E W) (g : M ⟶ N) (h : Uobj K ⟶ M) :
      e K N (h ≫ g) = e K M h ≫ T.map g := by
    apply fF.map_injective
    change IF.map (fF.preimage ((traceData K).choose N (IE.map (h ≫ g)))) =
      IF.map (fF.preimage ((traceData K).choose M (IE.map h)) ≫ T.map g)
    rw [fF.map_preimage, IF.map_comp, fF.map_preimage, IE.map_comp]
    exact (traceData K).choose_spec M N g (IE.map h)
  exact (Adjunction.adjunctionOfEquivLeft e he).isRightAdjoint

end WeilConjectures
