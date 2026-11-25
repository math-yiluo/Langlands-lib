/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilObject.Sheaf.EndTensorUnit
public import WeilConjectures.WeilSheaf.GeometricFiberPullback
public import WeilConjectures.ZetaFunction.WeilObjectOfLisse
public import WeilConjectures.ZetaFunction.WeilObjectOfLisseSpecTrace

/-!
# The global traces of the Weil object of a lisse sheaf

For a lisse `ℓ`-adic sheaf `H` on `X₀`, the global traces of the Weil object `(H, 1)` of
`Dᵇc(X₀)⟦ℚ̲̄_ℓ⟧` (`AlgebraicGeometry.WeilComplex.weilObjectOfLisse`), the local traces of its
compactly supported cohomology `RΓ_c(X₀, H)` at the geometric point of `Spec k₀`, are, through
`End (𝟙_ Mod_{Spec k̄}) ≅ ℚ̄_ℓ`, the alternating sums of the traces of the powers of the
geometric Frobenius on the compactly supported cohomology `H_c^i(X₀ ⊗ k̄, p^* H)` of the pulled
back Weil sheaf
(`WeilComplex.endTensorUnitRingEquiv_weilCompactSupportCohomology_weilObjectOfLisse`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilComplex

open ProEtale ProEtale.CondensedRing

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

attribute [local instance] fact_ringChar_prime_of_finite

/-- **The global traces of the Weil object of a lisse sheaf**: the global trace in degree `n + 1`
of the Weil object `(H, 1)` is `∑ᵢ (-1)ⁱ Tr(F^{n+1} | H_c^i(X₀ ⊗ k̄, p^* H))`. -/
theorem endTensorUnitRingEquiv_weilCompactSupportCohomology_weilObjectOfLisse
    {H : AdicSheaf l X} (hH : IsAdicLisseSheaf H) (n : ℕ) :
    endTensorUnitRingEquiv l (AlgebraicClosure k₀)
        (weilStalkTraceAlternatingSum l (n + 1) (specAlgebraicClosure k₀)
          (specAlgebraicClosure_comp_pow (n + 1))
          ((weilCompactSupportCohomology l (Iso.refl _)).obj (weilObjectOfLisse (k₀ := k₀) hH 1))) =
      ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
        (((WeilSheaf.toComplex.obj (WeilSheaf.geometricFiberPullback (k₀ := k₀) hH)
          ).compactlySupportedCohomology i).frobeniusEnd ^ (n + 1)) := by
  have hfin := finite_support_weilSheafStalkTrace_homology l (n + 1) (specAlgebraicClosure k₀)
    (specAlgebraicClosure_comp_pow (n + 1))
    ((weilCompactSupportCohomology l (Iso.refl _)).obj (weilObjectOfLisse (k₀ := k₀) hH 1))
  rw [weilStalkTraceAlternatingSum, map_finsum _ (hfin.subset fun j hj h ↦ hj (by
    beta_reduce at h ⊢
    rw [h, smul_zero]))]
  refine finsum_congr fun i ↦ ?_
  rw [map_zsmul, weilSheafStalkTrace_congr l (n + 1) _ _
    (homologyWeilCompactSupportCohomologyWeilObjectOfLisseIso hH i),
    endTensorUnitRingEquiv_weilSheafStalkTrace_ofId_lowerShriekHomologyOfLisse hH n i]
  congr 1
  exact (WeilSheaf.globalSectionsEquivOfIso
    (homologySheafDerivedLowerShriekGeometricFiberPullbackIso hH i)).trace_frobeniusEnd_pow
      (n + 1)

end AlgebraicGeometry.WeilComplex
