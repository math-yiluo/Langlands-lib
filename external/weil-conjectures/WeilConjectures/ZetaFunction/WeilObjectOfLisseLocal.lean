/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilObject.Sheaf.EndTensorUnit
public import WeilConjectures.WeilSheaf.GeometricFiberPullback
public import WeilConjectures.ZetaFunction.WeilObjectOfLisse
public import WeilConjectures.ZetaFunction.WeilObjectOfLisseLocalGalois
public import WeilConjectures.WeilSheaf.TraceFunction
public import WeilConjectures.WeilSheaf.TraceFunctionCongr

/-!
# The local traces of the Weil object of a lisse sheaf

For a lisse `ℓ`-adic sheaf `H` on `X₀` and `b ∈ ℚ̄_ℓˣ`, the local traces of the Weil object
`(H, b)` of `Dᵇc(X₀)⟦ℚ̲̄_ℓ⟧` (`AlgebraicGeometry.WeilComplex.weilObjectOfLisse`) at the points
of `X₀` are, through `End (𝟙_ Mod_{Spec k̄}) ≅ ℚ̄_ℓ`, the values of the trace function of the
Weil sheaf `p^* H ⊗ 𝓑_b` on `X₀ ⊗ k̄`
(`WeilComplex.endTensorUnitRingEquiv_weilStalkTraceAlternatingSum_weilObjectOfLisse`).
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

/-- **The local traces of the Weil object of a lisse sheaf**: at an `𝔽_{q^{n+1}}`-rational point
`y` of `X₀`, the local trace of the Weil object `(H, b)` is the trace function of the Weil sheaf
`p^* H ⊗ 𝓑_b`, that is `b^{n+1} Tr(F_y^{n+1} | H_ȳ)`. -/
theorem endTensorUnitRingEquiv_weilStalkTraceAlternatingSum_weilObjectOfLisse
    {H : AdicSheaf l X} (hH : IsAdicLisseSheaf H) (b : (PadicAlgCl l)ˣ) (n : ℕ)
    (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ (n + 1))) :
    endTensorUnitRingEquiv l (AlgebraicClosure k₀)
        (weilStalkTraceAlternatingSum l (n + 1) _
          (frobeniusFixedPointsReflOfFieldPoint (X := overSpec X) n y).2.2
          (weilObjectOfLisse (k₀ := k₀) hH b)) =
      (WeilSheaf.toComplex.obj
        ((WeilSheaf.geometricFiberPullback (k₀ := k₀) hH).constantTwist b)).traceFunction
          (n + 1) y := by
  rw [traceFunction_toComplex, WeilSheaf.traceFunction_constantTwist,
    WeilSheaf.traceFunction_geometricFiberPullback_eq_trace,
    endTensorUnitRingEquiv_weilStalkTraceAlternatingSum_weilObjectOfLisse_eq]

end AlgebraicGeometry.WeilComplex
