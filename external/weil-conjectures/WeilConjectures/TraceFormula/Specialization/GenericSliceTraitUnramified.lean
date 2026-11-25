/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.GenericSliceTrait
public import WeilConjectures.TraceFormula.Specialization.TraitChangeInvariance

/-!

# The change of trait of a generic slice trait is unramified

For a generic slice trait `D` of `𝔸¹_S`, `S = Spec k'⟦t⟧`
(`AlgebraicGeometry.GenericSliceTrait`), the composite `k'⟦t⟧ ⟶ R ⟶ K⟦t⟧` of the structure map
and of the change of trait is the coefficientwise map
(`AlgebraicGeometry.GenericSliceTrait.ι_comp_φ`), so `t` is a uniformizer of both `R` and `K⟦t⟧`
(`AlgebraicGeometry.GenericSliceTrait.maximalIdeal_eq_map_ι`): the change of trait
`Spec K⟦t⟧ ⟶ S'` is unramified, as needed by the invariance of nearby cycles under change of
trait (SGA 4½, [Th. finitude], 3.7).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.GenericSliceTrait

variable {k' : Type u} [Field k'] (D : GenericSliceTrait k')

/-- The composite `k'⟦t⟧ ⟶ R ⟶ K⟦t⟧` of the structure map and the change of trait of a generic
slice trait is the coefficientwise map. -/
lemma ι_comp_φ : D.ι.comp D.φ = PowerSeries.map (algebraMap k' (traitSliceField k')) := by
  have h : Spec.map (CommRingCat.ofHom (D.ι.comp D.φ)) = traitMap k' (traitSliceField k') := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, D.spec_φ, reassoc_of% D.spec_ι_comp,
      traitSlice_over]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)

/-- The change of trait `Spec K⟦t⟧ ⟶ S'` of a generic slice trait is unramified: `t` is a
uniformizer of both. -/
lemma maximalIdeal_eq_map_ι :
    IsLocalRing.maximalIdeal (PowerSeries (traitSliceField k')) =
      (IsLocalRing.maximalIdeal D.R).map D.ι := by
  rw [D.maximalIdeal_eq, Ideal.map_map, ι_comp_φ,
    maximalIdeal_powerSeries_eq_map k' (traitSliceField k')]

end AlgebraicGeometry.GenericSliceTrait
