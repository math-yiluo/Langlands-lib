/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FiniteCoefficientPoint

/-! # The rational Hom calculation for integral point sections

Source: Stacks, More on Algebra, Tag 0A6A; step 9 of the point-fibre proof.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TensorProduct
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The scalar extension of the integral Hom map is an additive isomorphism, with
its prescribed pure-tensor formula.
Source: Stacks, More on Algebra, Tag 0A6A, equation-base-change-RHom;
the point-fibre argument, step 9.
(blueprint: lem-weil-point-rational-sections-hom).

Proof: the integral equivalence identifies the integral Hom modules linearly, by
pointIntegralFibre_linear. Over the coefficient DVR, bounded finite cohomology
complexes are perfect: finite modules have finite free resolutions of length one,
and the perfect-cohomology assembly theorem applies. Apply perfect RHom base
change to O_E → E and these perfect section complexes. The field E is localization
at the uniformizer and is flat. Thus H^0 commutes with this tensor product; H^0 of
RHom is the derived Hom group by the K-injective Hom-complex theorem. The normalized
base-change map sends f tensor a to a times the extended map f. Insert the canonical
localization-field equivalence, commute the tensor factors, and transport along the
specified size-descent counit. All these maps are additive isomorphisms and their
pure-tensor formulas give exactly the equality below, including zero and torsion
Hom modules. No essential-surjectivity assertion is used or proved here. -/
theorem pointRationalSectionsHom
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (hi : (pointIntegralFibre D l hl E).IsEquivalence)
    (K M : sfIntegralConstructibleCategory l E (Spec (.of D.k))) :
    ∃ e : (Localization.Away (Padic.coefficientExtensionUniformizer l E) ⊗[
          Padic.coefficientExtensionIntegers l E] (K ⟶ M)) ≃+
        ((pointIntegralRationalFibre D l hl E).obj K ⟶
          (pointIntegralRationalFibre D l hl E).obj M),
      ∀ (a : Localization.Away (Padic.coefficientExtensionUniformizer l E)) (f : K ⟶ M),
        (e (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f)).hom =
          (sfRationalCoefficientEquiv l E a) •
            ((pointIntegralRationalFibre D l hl E).map f).hom := by
  sorry

end WeilConjectures
