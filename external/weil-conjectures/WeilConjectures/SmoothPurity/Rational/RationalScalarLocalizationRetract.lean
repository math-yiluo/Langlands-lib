/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Rational.RationalScalarRestrictionConstructible
public import Mathlib.CategoryTheory.Retract
import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalizationFullSubcategory

/-! # Descent of the ambient trace retract to the constructible subcategory

This module records the full-subcategory descent needed after the ambient trace
calculation.  (blueprint: lem-sf-rational-scalar-localization-retract).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- An ambient trace retract whose two objects are constructible lifts to the
raw rational constructible category.  The full-subcategory inclusion preserves
its section and retraction maps literally.

Source: the full-subcategory localization construction in the definition of raw
rationalization; Stacks Project Tags 090W and 02FL.
(blueprint: lem-sf-rational-scalar-localization-retract).

Proof: the inclusion of the scalar-localized constructible full subcategory into the
ambient scalar localization is fully faithful
(`ScalarLocalization.fullyFaithfulFullSubcategoryInclusion`) and sends an object to
the ambient object with the same underlying complex.  Take the preimages of the two
ambient maps.  The inclusion maps their composite to the ambient composite, which is
the identity; faithfulness gives the retract equation. -/
theorem rationalScalar_constructible_trace_retract
    (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F) (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (K : sfRationalConstructibleCategory l F W)
    (h : Nonempty (Retract
      (ScalarLocalization.mk (R := Padic.coefficientExtensionIntegers l F)
        (C := DerivedCategory (scalarReductionSource l F W))
        (p := Padic.coefficientExtensionUniformizer l F) K.obj.obj)
      (ScalarLocalization.mk (R := Padic.coefficientExtensionIntegers l F)
        (C := DerivedCategory (scalarReductionSource l F W))
        (p := Padic.coefficientExtensionUniformizer l F)
        ((sfRationalScalarExtension l E W 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι).obj
          ⟨(rationalScalarDerivedRestriction l E F ι W).obj K.obj.obj,
            rationalScalarDerivedRestriction_constructible l E F ι W K.obj⟩).obj.obj))) :
    Nonempty (Retract K ((sfRationalScalarExtension l E W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι).obj
      ⟨(rationalScalarDerivedRestriction l E F ι W).obj K.obj.obj,
        rationalScalarDerivedRestriction_constructible l E F ι W K.obj⟩)) := by
  obtain ⟨h⟩ := h
  let G := ScalarLocalization.fullyFaithfulFullSubcategoryInclusion
    (Padic.coefficientExtensionIntegers l F) (DerivedCategory (scalarReductionSource l F W))
    (sfIntegralConstructible l F W) (Padic.coefficientExtensionUniformizer l F)
  refine ⟨{ i := G.preimage h.i, r := G.preimage h.r, retract := ?_ }⟩
  apply G.map_injective
  rw [CategoryTheory.Functor.map_comp, G.map_preimage, G.map_preimage,
    CategoryTheory.Functor.map_id]
  exact h.retract

end WeilConjectures
