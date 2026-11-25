/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated

/-! # Finite reductions detect integral constructible isomorphisms

Source: Bhatt--Scholze, Definition 3.5.2 and Sections 6.5--6.7; the adic
projection proof, conservativity step (blueprint: lem-sf-intrinsic-reduction-conservative).
-/

@[expose] public section
set_option autoImplicit false
attribute [local instance] WeilConjectures.scalarReductionRestrictionLimits
  WeilConjectures.scalarReductionRestrictionColimits
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace WeilConjectures

/-- Finite reductions detect isomorphisms on the actual integral constructible domain.
Source: Bhatt--Scholze, Definition 3.5.2; blueprint adic projection proof, Step 3
(blueprint: lem-sf-intrinsic-reduction-conservative).

Proof: take a distinguished cone. Integral constructibles are triangulated, so its
cone is complete. Exact reduction sends its triangle to a triangle whose first map
is invertible; every reduced cone is therefore zero. Restriction of scalars preserves
zero objects. In the canonical augmented Roos triangle for the cone, both products
are now zero, by product extensionality. The cone is zero, and its original map is
invertible. This includes zero objects, empty schemes, torsion and arbitrary intervals. -/
theorem sfIntegralReduction_conservative
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (Y : AlgebraicGeometry.Scheme.{u})
    {M N : DerivedCategory (scalarReductionSource l E Y)} (f : M ⟶ N)
    (hM : sfIntegralConstructible l E Y M) (hN : sfIntegralConstructible l E Y N)
    (hf : ∀ n : ℕ, IsIso ((scalarReductionDerivedExtension l E Y n).map f)) :
    IsIso f := by
  obtain ⟨C, g, d, hT⟩ := distinguished_cocone_triangle f
  have hC : sfIntegralConstructible l E Y C :=
    ObjectProperty.ext_of_isTriangulatedClosed₃ _ (Triangle.mk f g d) hT hM hN
  have hz (n : ℕ) : IsZero ((sfDerivedReductionRestricted l E Y n).obj C) := by
    let F := scalarReductionDerivedExtension l E Y n
    obtain ⟨hshift, htri⟩ :=
      (scalarReductionDerivedExistence l E Y n).choose_spec.choose_spec.2.1
    let : F.CommShift ℤ := hshift
    have : F.IsTriangulated := htri
    have hFC : IsZero (F.obj C) :=
      Triangle.isZero₃_of_isIso₁ _ (F.map_distinguished _ hT) (hf n)
    let : (scalarReductionDerivedRestriction l E Y n).Additive :=
      inferInstanceAs (scalarReductionRestriction l E Y n).mapDerivedCategory.Additive
    exact (scalarReductionDerivedRestriction l E Y n).map_isZero hFC
  obtain ⟨hprod, dC, hTC⟩ := hC.1
  let := hprod
  have hp : IsZero (∏ᶜ fun n : ℕ ↦ (sfDerivedReductionRestricted l E Y n).obj C) := by
    rw [IsZero.iff_id_eq_zero]
    apply Pi.hom_ext
    intro n
    exact (hz n).eq_of_tgt _ _
  have hzero : IsZero C := Triangle.isZero₁_of_isZero₂₃ _ hTC hp hp
  exact (Triangle.isZero₃_iff_isIso₁ _ hT).mp hzero

end WeilConjectures
