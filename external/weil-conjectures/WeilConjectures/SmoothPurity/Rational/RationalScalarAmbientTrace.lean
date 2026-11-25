/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.SmoothPurity.Rational.RationalScalarDerivedRestriction
public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalizationFullSubcategory
import WeilConjectures.SmoothPurity.Rational.RationalScalarAmbientIntegralTrace
import WeilConjectures.SmoothPurity.Rational.RationalScalarAmbientLocalizationTransport

/-!
# The ambient rational trace Hom equivalence

Source: Bhatt--Scholze, Proposition 6.8.14(2), Remark 6.8.15; the trace step of the
finite coefficient argument (blueprint: lem-sf-rational-scalar-ambient-trace).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (W : AlgebraicGeometry.Scheme.{u})

/-- Inclusion of rational constructible objects into the ambient scalar localization.
Source: the raw rationalization Hom formula
(blueprint: lem-sf-rational-scalar-ambient-trace). -/
abbrev rationalScalarAmbientInclusion :=
  ScalarLocalization.fullSubcategoryInclusion (Padic.coefficientExtensionIntegers l E)
    (DerivedCategory (scalarReductionSource l E W)) (sfIntegralConstructible l E W)
    (Padic.coefficientExtensionUniformizer l E)

/-- The ambient trace equivalence, natural in the complete constructible argument.
The other argument is an arbitrary ambient F-complex, with no constructibility
or completeness hypothesis. Its representing E-object is the actual derived
restriction, fixed before this assertion.

Source: Bhatt--Scholze, Proposition 6.8.14(2), Remark 6.8.15; steps 2--3 of
`lem-sf-rational-scalar-extension-right-adjoint` (agent elaboration).
(blueprint: lem-sf-rational-scalar-ambient-trace).

Proof: regard F as a finite separable E-algebra using the specified inclusion.
The nondegenerate trace pairing identifies the E-dual of F with F. Choose a
basis b_i and trace-dual basis c_i. Restriction is left adjoint to ordinary
extension: the counit is z tensor m mapping to Tr(z)m and the unit is m mapping
to sum_i b_i tensor c_i m. Their E-linearity, F-linearity and the two triangles
follow from the trace-dual identities; the formulas commute with sheaf restriction,
differentials and chain maps. Choose one common integral denominator for all
basis, dual basis and trace coefficients. The finite formulas then give morphisms
in the scalar-localized integral derived categories. Multiplying denominators
changes no localized morphism, by tensor balancing; the triangles descend for the
same reason. Exact restriction and finite free extension preserve quasi-isomorphisms,
so the equivalences descend from complexes to arbitrary derived morphisms, including
roofs. For a complete E-input, the canonical finite-free completed-scalar comparison
is invertible. Compose with this comparison and its normalized rationalization to
obtain the displayed target, precisely the specified rational scalar extension.
The trace equivalences are natural in the E-input, first on integral chain maps,
then on roofs, and finally on rational morphisms by the same coefficient balancing.
The ambient F-input need not be complete for this argument: only the comparison
on the E-input uses completeness. -/
theorem rationalScalarAmbientTrace
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F)
    (K : DerivedCategory (scalarReductionSource l F W)) :
    ∃ e : ∀ M : sfRationalConstructibleCategory l E W,
      (ScalarLocalization.mk ((rationalScalarDerivedRestriction l E F ι W).obj K) ⟶
        (rationalScalarAmbientInclusion l E W).obj M) ≃
      (ScalarLocalization.mk K ⟶
        (rationalScalarAmbientInclusion l F W).obj
          ((sfRationalScalarExtension l E W 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι).obj M)),
      ∀ (M N : sfRationalConstructibleCategory l E W) (f : M ⟶ N) (h),
        e N (h ≫ (rationalScalarAmbientInclusion l E W).map f) =
          e M h ≫ (rationalScalarAmbientInclusion l F W).map
            ((sfRationalScalarExtension l E W 0
              (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι).map f) := by
  obtain ⟨e₀, he₀⟩ := rationalScalarAmbientIntegralTrace l E W F ι K
  exact rationalScalarAmbientLocalizationTransport l E W F ι K e₀ he₀

end WeilConjectures
