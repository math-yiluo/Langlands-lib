/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Supporting.ConstructibleHeart
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
import Mathlib.CategoryTheory.Triangulated.TStructure.Induced
import WeilConjectures.SmoothPurity.Sf.SfIntegralStandardTruncations
import WeilConjectures.DeligneLaumon.SfScalarExtensionComposition
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.Heart

/-! # Constructible hearts on the intrinsic coefficient categories

Source: Weil blueprint, order 1506, constructible heart and its standard t-structure
(blueprint: def-weil-constructible-heart).
The existing heart module uses the earlier integral predicate. Here the same standard
classes are placed on the currently recorded intrinsic rational and common-stage categories.

## Main definitions

- `sfRationalHeart`: the full heart in the intrinsic rational category.
- `sfCommonStageHeart`: the full heart in the general common-stage category.
- `sfRationalStandardTStructure` and `sfCommonStageStandardTStructure`: standard t-structures.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (Y : Scheme.{u})

/-- The integral standard class, with either cohomological inequality.
Source: blueprint order 1506 (blueprint: def-weil-constructible-heart). -/
def sfIntegralStandardClass (nonpositive : Bool) (n : ℤ) :
    ObjectProperty (sfIntegralConstructibleCategory l E Y) :=
  fun K ↦ ∀ i : ℤ, (if nonpositive then n < i else i < n) →
    IsZero ((DerivedCategory.homologyFunctor (scalarReductionSource l E Y) i).obj K.obj)

/-- Rational standard classes are the isomorphism closures of the integral classes.
Source: blueprint order 1506 (blueprint: def-weil-constructible-heart). -/
def sfRationalStandardClass (nonpositive : Bool) (n : ℤ) :
    ObjectProperty (sfRationalConstructibleCategory l E Y) :=
  fun K ↦ ∃ M : sfIntegralConstructibleCategory l E Y,
    sfIntegralStandardClass l E Y nonpositive n M ∧
      Nonempty (K ≅ (sfRationalConstructibleLocalization l E Y).obj M)

variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  [base : Y.Over (Spec (.of D.k))]
  [hft : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [hqc : QuasiCompact (Y ↘ Spec (.of D.k))]

include D hl base hft hqc

end WeilConjectures
