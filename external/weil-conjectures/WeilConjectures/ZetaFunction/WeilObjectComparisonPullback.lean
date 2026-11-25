/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilObject.Sheaf.EndTensorUnit
public import WeilConjectures.WeilSheaf.GeometricFiberPullback
public import WeilConjectures.WeilSheaf.TraceFunction
public import WeilConjectures.WeilSheaf.TraceFunctionCongr
public import WeilConjectures.ZetaFunction.WeilObjectOfLisseGlobal
public import WeilConjectures.ZetaFunction.WeilObjectOfLisseLocal

/-!
# Weil sheaves pulled back from the model have the traces of Weil objects

Let `H` be a lisse `ℓ`-adic sheaf on a separated `k₀`-scheme `X₀` of finite type, and
`p^* H` its pullback to the geometric fibre `X̄` with the canonical Weil structure
(`AlgebraicGeometry.WeilSheaf.geometricFiberPullback`). Through the equivalence of `ℓ`-adic
sheaves with condensed `ℚ̲̄_ℓ`-modules (`AlgebraicGeometry.ProEtale.adicSheafEquivCondensedMod`),
`H` is an object of `Dᵇc(X₀)⟦ℚ̲̄_ℓ⟧`, a Weil object for the identity of `X₀` with the identity
Weil structure (`AlgebraicGeometry.WeilComplex.weilObjectOfLisse`), and `p^* H` has its
traces: its stalks are the stalks of `H` with their Galois
action, and its compactly supported cohomology is the stalk at `Spec k̄` of `Rf_! H`.

## Main results

- `AlgebraicGeometry.WeilSheaf.hasWeilObjectComparison_toComplex_geometricFiberPullback`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

open ProEtale ProEtale.CondensedRing in
/-- **Weil sheaves pulled back from the model have the traces of Weil objects**: for a lisse
`ℓ`-adic sheaf `H` on `X₀`, the Weil sheaf `p^* H` with its canonical Weil structure has, through
the canonical identification `End (𝟙_ Mod_{Spec k̄}) ≅ ℚ̄_ℓ`, the traces of the Weil object `H`
of `Dᵇc(X₀)⟦ℚ̲̄_ℓ⟧` with the identity Weil structure. -/
theorem hasWeilObjectComparison_toComplex_geometricFiberPullback {H : AdicSheaf l X}
    (hH : IsAdicLisseSheaf H) :
    WeilComplex.HasWeilObjectComparison
      (endTensorUnitRingEquiv l (AlgebraicClosure k₀)).toAddMonoidHom
      (toComplex.obj (geometricFiberPullback (k₀ := k₀) hH)) :=
  ⟨WeilComplex.weilObjectOfLisse hH 1,
    WeilComplex.endTensorUnitRingEquiv_weilCompactSupportCohomology_weilObjectOfLisse hH,
    fun n y ↦ by
      have h := WeilComplex.endTensorUnitRingEquiv_weilStalkTraceAlternatingSum_weilObjectOfLisse
        (k₀ := k₀) hH 1 n y
      rw [WeilComplex.traceFunction_toComplex, traceFunction_constantTwist, Units.val_one,
        one_pow, one_mul, ← WeilComplex.traceFunction_toComplex] at h
      exact h⟩

end AlgebraicGeometry.WeilSheaf
