/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilObject.Sheaf.EndTensorUnit
public import WeilConjectures.WeilSheaf.GeometricFiberPullback
public import WeilConjectures.WeilSheaf.ConstantTwistCohomology
public import WeilConjectures.WeilSheaf.TraceFunctionCongr
public import WeilConjectures.WeilSheaf.WeilDescent
public import WeilConjectures.ZetaFunction.WeilObjectComparisonPullback
public import WeilConjectures.ZetaFunction.WeilSheafObjectComparisonInduction

/-!
# The comparison of lisse Weil sheaves with Weil objects

The Noetherian induction of
`WeilConjectures.ZetaFunction.WeilSheafObjectComparisonInduction` reduces the comparison of Weil
sheaves with Weil objects (`AlgebraicGeometry.WeilComplex.HasWeilObjectComparison`) to irreducible
lisse Weil sheaves on smooth irreducible affine `k₀`-schemes
(`AlgebraicGeometry.WeilSheaf.IrreducibleLisseComparisonHolds`). This file splits that case in
two:

* **Descent**
  (`WeilSheaf.IsIrreducibleLisse.exists_iso_constantTwist_geometricFiberPullback`):
  an irreducible lisse Weil sheaf `G` on a smooth irreducible `V₀` is a constant twist
  `p^* H ⊗ 𝓑_b` of the pullback of a lisse `ℓ`-adic sheaf `H` on `V₀` itself, along the
  projection `p : V₀ ⊗ k̄ ⟶ V₀` (Deligne, Weil II, 1.3.14, and the dictionary between lisse
  sheaves on `V₀` and continuous representations of `π₁(V₀)`).
* **Pulled-back sheaves**
  (`AlgebraicGeometry.WeilSheaf.hasWeilObjectComparison_constantTwist_geometricFiberPullback`):
  the Weil sheaf `p^* H ⊗ 𝓑_b` has the traces of the Weil object `(H, b)` of
  `Dᵇc(V₀)⟦ℚ̲̄_ℓ⟧` for the identity, `H` in degree `0` with the structure automorphism `b`:
  the stalks of `p^* H` are those of `H`, and its compactly supported cohomology is that of `H`,
  compatibly with the Frobenius.

## Main results

- `AlgebraicGeometry.WeilSheaf.irreducibleLisseComparisonHolds`: the generic case of the
  Noetherian induction.
- `AlgebraicGeometry.WeilSheaf.hasWeilObjectComparison_toComplex_of_irreducibleLisse`: every
  Weil sheaf has the traces of a Weil object, through the canonical identification
  `End (𝟙_ Mod_{Spec k̄}) ≅ ℚ̄_ℓ`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilSheaf

open ProEtale ProEtale.CondensedRing

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- **Constant twists and the Grothendieck–Lefschetz formula**: if a Weil sheaf `G` satisfies the
Grothendieck–Lefschetz formula, so does its constant twist `G ⊗ 𝓑_b`, both sides being
multiplied by `b^{n+1}` in degree `n + 1`
(`AlgebraicGeometry.WeilSheaf.nonempty_equiv_compactlySupportedCohomology_constantTwist`,
`AlgebraicGeometry.WeilSheaf.traceFunction_constantTwist`). -/
theorem _root_.AlgebraicGeometry.WeilComplex.SatisfiesLefschetz.constantTwist
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] {G : WeilSheaf k₀ l X}
    (hG : WeilComplex.SatisfiesLefschetz (toComplex.obj G)) (b : (PadicAlgCl l)ˣ) :
    WeilComplex.SatisfiesLefschetz (toComplex.obj (G.constantTwist b)) := fun n ↦ by
  have h₁ (i : ℤ) : LinearMap.trace (PadicAlgCl l) _
      (((toComplex.obj (G.constantTwist b)).compactlySupportedCohomology i).frobeniusEnd ^
        (n + 1)) =
        (b : PadicAlgCl l) ^ (n + 1) * LinearMap.trace (PadicAlgCl l) _
          (((toComplex.obj G).compactlySupportedCohomology i).frobeniusEnd ^ (n + 1)) := by
    obtain ⟨e⟩ := nonempty_equiv_compactlySupportedCohomology_constantTwist G b i
    rw [← FrobeniusModule.trace_frobeniusEnd_rescale_pow _ b.ne_zero]
    exact (e.trace_frobeniusEnd_pow (n + 1)).symm
  calc _ = ∑ᶠ i : ℤ, (b : PadicAlgCl l) ^ (n + 1) • ((i.negOnePow : ℤ) • LinearMap.trace
        (PadicAlgCl l) _ (((toComplex.obj G).compactlySupportedCohomology i).frobeniusEnd ^
          (n + 1))) :=
        finsum_congr fun i ↦ by rw [h₁, smul_eq_mul, mul_smul_comm]
    _ = _ := by
      rw [← smul_finsum, hG n, smul_finsum]
      refine finsum_congr fun y ↦ ?_
      rw [WeilComplex.traceFunction_toComplex, WeilComplex.traceFunction_toComplex,
        traceFunction_constantTwist, smul_eq_mul]

/-- **Pulled-back lisse sheaves have the traces of Weil objects**: for a lisse `ℓ`-adic sheaf
`H` on `X₀` and a unit `b ∈ ℚ̄_ℓ`, the constant twist `p^* H ⊗ 𝓑_b` of its pullback to
`X₀ ⊗ k̄` has, through the canonical identification `End (𝟙_ Mod_{Spec k̄}) ≅ ℚ̄_ℓ`, the traces
of the Weil object `(H, b)` of `Dᵇc(X₀)⟦ℚ̲̄_ℓ⟧` for the identity. -/
theorem hasWeilObjectComparison_constantTwist_geometricFiberPullback
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    {H : AdicSheaf l X} (hH : IsAdicLisseSheaf H) (b : (PadicAlgCl l)ˣ) :
    WeilComplex.HasWeilObjectComparison
      (endTensorUnitRingEquiv l (AlgebraicClosure k₀)).toAddMonoidHom
      (toComplex.obj ((WeilSheaf.geometricFiberPullback (k₀ := k₀) hH).constantTwist b)) :=
  by
  have h₁ := hasWeilObjectComparison_toComplex_geometricFiberPullback (k₀ := k₀) hH
  refine (WeilComplex.hasWeilObjectComparison_iff _).2
    ⟨⟨WeilComplex.weilObjectOfLisse hH b, fun n y ↦
      WeilComplex.endTensorUnitRingEquiv_weilStalkTraceAlternatingSum_weilObjectOfLisse hH b n y⟩,
      h₁.satisfiesLefschetz.constantTwist b⟩

/-- The generic case of the Noetherian induction: irreducible lisse Weil sheaves on smooth
irreducible affine `k₀`-schemes have the traces of Weil objects. -/
theorem irreducibleLisseComparisonHolds :
    IrreducibleLisseComparisonHolds (k₀ := k₀) (l := l)
      (endTensorUnitRingEquiv l (AlgebraicClosure k₀)).toAddMonoidHom := by
  intro V _ _ _ _ _ _ _ G hG
  obtain ⟨H, hH, b, ⟨e⟩⟩ := hG.exists_iso_constantTwist_geometricFiberPullback
  exact (hasWeilObjectComparison_constantTwist_geometricFiberPullback hH b).of_iso
    (toComplex.mapIso e.symm)

/-- **Weil sheaves have the traces of Weil objects**, through the canonical identification
`End (𝟙_ Mod_{Spec k̄}) ≅ ℚ̄_ℓ`, by Noetherian induction from
`AlgebraicGeometry.WeilSheaf.irreducibleLisseComparisonHolds`. -/
theorem hasWeilObjectComparison_toComplex_of_irreducibleLisse
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] (G : WeilSheaf k₀ l X) :
    WeilComplex.HasWeilObjectComparison
      (endTensorUnitRingEquiv l (AlgebraicClosure k₀)).toAddMonoidHom (toComplex.obj G) :=
  hasWeilObjectComparison_toComplex_of_lisseComparisonHolds
    (lisseComparisonHolds_of_irreducibleLisseComparisonHolds irreducibleLisseComparisonHolds) G

end AlgebraicGeometry.WeilSheaf
