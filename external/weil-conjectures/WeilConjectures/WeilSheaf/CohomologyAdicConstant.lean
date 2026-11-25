/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.Constant
import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantCohomologicalDimension
import WeilConjectures.WeilSheaf.CohomologyNonneg
import WeilConjectures.WeilSheaf.CohomologyProEtale

/-!
# The cohomological range of the constant Weil sheaf

Let `Y` be a quasi-compact quasi-separated `k₀`-scheme of finite type whose geometric fiber
`Ȳ = Y ⊗ k̄` has dimension at most `e`. Then the cohomology `Hʳ(Y ⊗ k̄, ℚ̄_ℓ)` of the constant
Weil sheaf vanishes for `r ∉ [0, 2e]`: it is the pro-étale cohomology `Hʳ(Ȳ_proét, ℚ̄_ℓ)`
(`AlgebraicGeometry.WeilSheaf.cohomologyIsoRightDerivedGlobalSections`), which vanishes above
`2e` (`AlgebraicGeometry.ProEtale.isZero_rightDerived_Γ_adicConstantSheaf_of_two_mul_lt`).
For `Y` smooth of relative dimension `d`, the geometric fiber has dimension at most `d`.

## Main statements

- `AlgebraicGeometry.WeilSheaf.subsingleton_cohomology_adicConstant_of_two_mul_lt`
- `AlgebraicGeometry.topologicalKrullDim_geometricFiber_le_of_smoothOfRelativeDimension`
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The geometric fiber of a smooth scheme of relative dimension `d` over a field has dimension at
most `d`. -/
lemma topologicalKrullDim_geometricFiber_le_of_smoothOfRelativeDimension {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (d : ℕ) [SmoothOfRelativeDimension d f] :
    topologicalKrullDim f.geometricFiber ≤ (d : WithBot ℕ∞) := by
  have := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
  have : SmoothOfRelativeDimension d f.geometricFiberToAlgebraicClosure :=
    MorphismProperty.pullback_snd _ _ ‹SmoothOfRelativeDimension d f›
  exact_mod_cast topologicalKrullDim_le_of_smoothOfRelativeDimension
    f.geometricFiberToAlgebraicClosure d

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace WeilSheaf

variable (k₀ l) (Y : Scheme.{u}) [Y.Over (Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]

/-- **Cohomological range of the constant Weil sheaf.** If the geometric fiber `Y ⊗ k̄` has
dimension at most `e`, then `Hʳ(Y ⊗ k̄, ℚ̄_ℓ) = 0` for `r < 0` and for `r > 2e`. -/
theorem subsingleton_cohomology_adicConstant_of_two_mul_lt (e : ℕ)
    (he : topologicalKrullDim (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber ≤ (e : WithBot ℕ∞))
    {r : ℤ} (hr : r < 0 ∨ 2 * (e : ℤ) < r) :
    Subsingleton ((adicConstant k₀ l Y).cohomology r).carrier := by
  rcases hr with hr | hr
  · exact subsingleton_cohomology_of_neg _ hr
  · obtain ⟨r, rfl⟩ : ∃ n : ℕ, r = n := ⟨r.toNat, by lia⟩
    exact subsingleton_cohomology_of_isZero_rightDerived _ r
      (ProEtale.isZero_rightDerived_Γ_adicConstantSheaf_of_two_mul_lt
        (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure e he r
        (by exact_mod_cast hr))

/-- Blueprint `lemma-perfect-complexes-geometric-point` (constant-sheaf clause,
`theorem-trace-isomorphism-top-degree--8`): the cohomology `Hⁱ(X ⊗ k̄, ℚ̄_ℓ)` of a smooth
`k₀`-scheme of finite type and pure dimension `d` vanishes for `i ∉ [0, 2d]`: the fibrewise
cohomological dimension of `X ⊗ k̄` over the algebraically closed field `k̄` is `2d`. -/
theorem subsingleton_cohomology_adicConstant (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    (d : ℕ) [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))] {i : ℤ}
    (hi : i < 0 ∨ 2 * d < i) :
    Subsingleton ((adicConstant k₀ l X).cohomology i).carrier :=
  subsingleton_cohomology_adicConstant_of_two_mul_lt k₀ l X d
    (topologicalKrullDim_geometricFiber_le_of_smoothOfRelativeDimension _ d) hi

end WeilSheaf

end AlgebraicGeometry
