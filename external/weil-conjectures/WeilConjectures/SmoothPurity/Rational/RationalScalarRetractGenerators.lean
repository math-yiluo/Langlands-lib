/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import Mathlib.CategoryTheory.Retract

import WeilConjectures.SmoothPurity.Rational.RationalScalarIntegralDenominatorSplit
import WeilConjectures.SmoothPurity.Rational.RationalScalarRestrictionConstructible
import WeilConjectures.SmoothPurity.Rational.RationalScalarLocalizationRetract

/-! # Scalar-extended retract generators of the raw rational category

Source: Bhatt--Scholze, Proposition 6.8.14(2), Remark 6.8.15;
finite separability applied to the coefficient-restriction construction;
Stacks Project Tags 090W and 02FL (the separability diagonal).
(blueprint: lem-sf-rational-scalar-retract-generators).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Every raw rational F-object is a retract of an object extended from E.

Source: Bhatt--Scholze, Proposition 6.8.14(2), Remark 6.8.15;
the coefficient-restriction construction in step 1 of
lem-sf-rational-restriction-pullback-unit, followed by the separability projector
of Stacks Project Tags 090W and 02FL.
(blueprint: lem-sf-rational-scalar-retract-generators).

Proof: represent K by its integral complete constructible F-complex and restrict
its completed coefficient action from O_F to O_E. Restriction is exact and
commutes with products. The equality iota(varpi_E) = u varpi_F^e identifies the
O_E reductions with a cofinal subsequence of the O_F reductions, so the
restricted complex is derived complete. At finite levels the coefficient
restriction of each constructible sheaf is constructible: a finite O_F-module
is finite over O_E. Exactness preserves the same bounded cohomological interval.
This supplies an object M of the raw rational E-category; no splitting of an
idempotent in that category is used.

The finite extension F/E is separable in characteristic zero. Choose its
separability element sum_i a_i tensor b_i, with product sum_i a_i b_i = 1
and (z tensor 1)e = (1 tensor z)e for every z in F. Under the finite-free
ordinary/completed scalar comparison, multiplication gives T(M) to K and
x maps to sum_i a_i tensor b_i x gives K to T(M). The centralizing identity
makes the section F-linear, and multiplication after the section is identity.
Clear one common O_E denominator in this finite sum to obtain actual morphisms
in the raw localized Hom groups. The tensor identities therefore hold there,
not just after an unrelated realization. These maps give the asserted retract.
Zero objects, empty schemes, and identity field maps use the same construction. -/
theorem rationalScalar_retract_generators
    (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F) (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (K : sfRationalConstructibleCategory l F W) :
    ∃ M : sfRationalConstructibleCategory l E W,
      Nonempty (Retract K ((sfRationalScalarExtension l E W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι).obj M)) := by
  let M : sfRationalConstructibleCategory l E W :=
    ⟨(rationalScalarDerivedRestriction l E F ι W).obj K.obj.obj,
      rationalScalarDerivedRestriction_constructible l E F ι W K.obj⟩
  refine ⟨M, ?_⟩
  apply rationalScalar_constructible_trace_retract l E F ι W K
  exact rationalScalar_ambient_trace_retract l E F ι W K

end WeilConjectures
