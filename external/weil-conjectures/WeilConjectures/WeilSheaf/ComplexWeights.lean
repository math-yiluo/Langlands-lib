/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.Reduction.Weights
public import WeilConjectures.WeilSheaf.HomologyShift

/-!
# Upper weight bounds of Weil complexes

The blueprint definition `definition-weights--6` has two halves. A Weil complex `K` on a
`k₀`-scheme `Y` has *weights at most* `w` if every cohomology sheaf `𝓗ʲK` is `ι`-mixed of
weights at most `w + j`; it has *weights at least* `w` if its Verdier dual `D_Y K` has weights
at most `-w`. The upper half is `AlgebraicGeometry.WeilComplex.IsMixedOfWeightsAtMost`
(`WeilConjectures.DeligneLaumon.Reduction.Weights`), with cohomological indexing so that the
bound in degree `j` is `w + j`; this file records that it is the upper half of the blueprint
definition and proves that shifting by `n` raises the bound by `n`.

The lower half is not formalised. It needs, at the level of Weil complexes, the dualizing Weil
complex `ω_Y` (the exceptional inverse image `Ra_Y^! ℚ̄_ℓ` with its canonical Weil structure)
and the derived internal hom `RHom(K, ω_Y)` with arbitrary, not necessarily lisse, first
argument. Neither exists for `AlgebraicGeometry.WeilComplex`: the exceptional inverse image and
the Verdier dual of `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Duality` live on
the derived category of pro-étale sheaves without Weil structure, and the only derived internal hom
of Weil complexes is `AlgebraicGeometry.WeilComplex.ihomLisse`, out of a lisse Weil sheaf.

## Main statements

- `AlgebraicGeometry.WeilComplex.isMixedOfWeightsAtMost_iff`: the upper half of
  `definition-weights--6`.
- `AlgebraicGeometry.WeilComplex.isMixedOfWeightsAtMost_shift_iff`: shifts.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  {ι : PadicAlgCl l →+* ℂ} {K : WeilComplex k₀ l X} {w w' : ℝ}

/-- *Weights at most `w` of a Weil complex.* A Weil complex `K` has weights at most `w` if and
only if for every `j ∈ ℤ` its cohomology sheaf `𝓗ʲK` is `ι`-mixed of weights at most `w + j`.
This is the upper half of the blueprint definition; its lower half, through the Verdier dual,
is not available for Weil complexes (see the module docstring).
(blueprint: `definition-weights--6`) -/
theorem isMixedOfWeightsAtMost_iff :
    K.IsMixedOfWeightsAtMost ι w ↔
      ∀ j : ℤ, ((homologySheaf j).obj K).IsMixedOfWeightsAtMost ι (w + j) :=
  Iff.rfl

/-- A zero Weil complex has weights at most `w`, for every `w`. -/
theorem isMixedOfWeightsAtMost_of_isZero (hK : IsZero K) (w : ℝ) :
    K.IsMixedOfWeightsAtMost ι w :=
  fun j ↦ WeilSheaf.isMixedOfWeightsAtMost_of_isZero ((homologySheaf j).map_isZero hK) _

/-- Shifting a Weil complex by `n` raises its upper weight bounds by `n`: `K[n]` has weights at
most `w + n` if and only if `K` has weights at most `w`, since `𝓗ʲ(K[n]) = 𝓗ʲ⁺ⁿK`. -/
theorem isMixedOfWeightsAtMost_shift_iff (n : ℤ) :
    (K⟦n⟧).IsMixedOfWeightsAtMost ι (w + n) ↔ K.IsMixedOfWeightsAtMost ι w := by
  refine ⟨fun h b ↦ ?_, fun h a ↦ ?_⟩
  · refine ((h (b - n)).of_iso (homologySheafShiftIso K n (b - n) b (by ring))).mono_weight
      (le_of_eq ?_)
    push_cast
    ring
  · refine ((h (n + a)).of_iso (homologySheafShiftIso K n a (n + a) rfl).symm).mono_weight
      (le_of_eq ?_)
    push_cast
    ring

end WeilComplex

end AlgebraicGeometry
