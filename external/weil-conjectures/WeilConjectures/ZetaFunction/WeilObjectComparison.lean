/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.FrobeniusFixedPointsEquiv
public import WeilConjectures.TraceFormula.Statement
public import WeilConjectures.WeilSheaf.AlgClosedCoefficientCohomology
public import WeilConjectures.WeilSheaf.Stalk
public import WeilConjectures.ZetaFunction.WeilSheafObjectComparison

/-!
# Weil complexes as Weil objects of `Dᵇc(-)⟦ℚ̲̄_ℓ⟧`

The zeta-function chapter works with the Weil complexes `AlgebraicGeometry.WeilComplex` on a
scheme `X₀` over a finite field `k₀`, with their compactly supported cohomology modules and
trace functions. The trace formula of the project is stated in
`WeilConjectures.TraceFormula.Statement` for the Weil objects
`ProEtale.CondensedRing.WeilBoundedConstructible` of `Dᵇc(X₀)⟦ℚ̲̄_ℓ⟧` for the identity of `X₀`
(the Frobenius of `Spec k̄` twisted by `e = 𝟙`).

This file deduces the comparison between the two settings
(`AlgebraicGeometry.WeilComplex.exists_weilBoundedConstructible_comparison`) from its case of
Weil sheaves (see below) and deduces the trace formula for Weil
complexes from `ProEtale.CondensedRing.weilTraceFormula`
(`AlgebraicGeometry.WeilComplex.finsum_trace_compactlySupportedCohomology_eq_of_comparison` and
`AlgebraicGeometry.WeilComplex.sum_trace_compactlySupportedCohomology_eq_sum_traceFunction`).

The deduction transports the sum over the points of degree `n + 1` for `e = 𝟙` to the sum over
the `𝔽_{q^{n+1}}`-rational points along the bijection
`ProEtale.CondensedRing.fieldPointsEquivFrobeniusFixedPointsRefl`.

## The comparison

`AlgebraicGeometry.WeilComplex.exists_weilBoundedConstructible_comparison`: every Weil complex
`K` on `X₀` has the traces of a Weil object `K'` for `𝟙 X₀`. There is an additive map
`ι : End (𝟙 Mod_{Spec k̄}) ⟶ ℚ̄_ℓ` identifying
* the global trace of `K'` in degree `n + 1` with the alternating sum of the traces of `F^{n+1}`
  on the compactly supported cohomology of `K`, and
* the local trace of `K'` at the geometric point `Spec ι ≫ y` over an `𝔽_{q^{n+1}}`-rational
  point `y` with the trace function of `K` at `y`.

It is deduced by dévissage (`AlgebraicGeometry.WeilComplex.hasWeilObjectComparison_of_toComplex`)
from the case of Weil sheaves, `AlgebraicGeometry.WeilSheaf.exists_hasWeilObjectComparison`.
That case compares the Weil sheaves of the zeta-function chapter, which
live on the geometric fiber `X₀ ⊗ k̄`, with the bounded constructible Weil objects of the trace
formula chapter, which live on `X₀`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

attribute [local instance] fact_ringChar_prime_of_finite
    ProEtale.CondensedRing.fintypeFrobeniusFixedPoints

open ProEtale.CondensedRing in
/-- **Weil complexes have the traces of Weil objects of `Dᵇc(-)⟦ℚ̲̄_ℓ⟧`** (comparison of the
zeta-function chapter with the trace formula chapter): a Weil complex `K` on `X₀` has the
same traces as a Weil object `K'` for `𝟙 X₀`. There is an additive map
`ι : End (𝟙 Mod_{Spec k̄}) ⟶ ℚ̄_ℓ` such that, for every `n`,
* `ι` of the global trace of `K'` in degree `n + 1` is
  `∑ᵢ (-1)ⁱ Tr(F^{n+1} | H_c^i(X₀ ⊗ k̄, K))`, and
* for every `𝔽_{q^{n+1}}`-rational point `y` of `X₀`, `ι` of the local trace of `K'` at the
  geometric point `Spec ι ≫ y` (for the embedding `ι : 𝔽_{q^{n+1}} ↪ k̄` chosen by
  `IsAlgClosed.lift`) is the trace function `t_K(y)` of `K` in degree `n + 1`, which is the
  Frobenius trace on the stalks of `K` at the geometric point of `X₀ ⊗ k̄` over `Spec ι ≫ y`.

The Weil sheaves of the zeta-function chapter live on the geometric fiber `X₀ ⊗ k̄`, while the Weil
objects of the trace formula chapter live on `X₀` itself, with an extra automorphism. A Weil sheaf
need not descend to `X₀`, so `K'` is not a descent of `K`: by Deligne (Weil II, 1.3.14) every
irreducible Weil sheaf is the twist of an étale sheaf on `X₀` by a character of `W(k̄/k₀)`, which
becomes the automorphism of `K'`, and the traces only depend on the semisimplification.

It is deduced from the case of Weil sheaves, `WeilSheaf.exists_hasWeilObjectComparison`, by the
dévissage `WeilComplex.hasWeilObjectComparison_of_toComplex`. -/
theorem WeilComplex.exists_weilBoundedConstructible_comparison (K : WeilComplex k₀ l X) :
    ∃ (K' : WeilBoundedConstructible l (Iso.refl (WeilComplex.overSpec (k₀ := k₀) X)).hom)
      (ι : End (𝟙_ (GeometricPointMod l (AlgebraicClosure k₀))) →+ PadicAlgCl l),
      (∀ n : ℕ, ι (weilStalkTraceAlternatingSum l (n + 1) (specAlgebraicClosure k₀)
          (specAlgebraicClosure_comp_pow (n + 1))
          ((weilCompactSupportCohomology l (Iso.refl _)).obj K')) =
        ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
          ((K.compactlySupportedCohomology i).frobeniusEnd ^ (n + 1))) ∧
      ∀ (n : ℕ)
        (y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ (n + 1))),
        ι (weilStalkTraceAlternatingSum l (n + 1) _
          (frobeniusFixedPointsReflOfFieldPoint (X := WeilComplex.overSpec X) n y).2.2 K') =
          K.traceFunction (n + 1) y := by
  obtain ⟨ι, h⟩ := WeilSheaf.exists_hasWeilObjectComparison (k₀ := k₀) (l := l) (X := X)
  obtain ⟨K', hglob, hloc⟩ := WeilComplex.hasWeilObjectComparison_of_toComplex h K
  exact ⟨K', ι, hglob, hloc⟩

open ProEtale.CondensedRing in
/-- **The Grothendieck–Lefschetz trace formula for Weil complexes**, deduced from the trace formula
for Weil objects `ProEtale.CondensedRing.weilTraceFormula` (with `e = 𝟙`) through the comparison
`WeilComplex.exists_weilBoundedConstructible_comparison`. -/
theorem WeilComplex.finsum_trace_compactlySupportedCohomology_eq_of_comparison
    (K : WeilComplex k₀ l X) {m : ℕ} (hm : 1 ≤ m) :
    ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
        ((K.compactlySupportedCohomology i).frobeniusEnd ^ m) =
      ∑ᶠ y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ m),
        K.traceFunction m y := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨K', ι, hglob, hloc⟩ := K.exists_weilBoundedConstructible_comparison
  set eqv := (fieldPointsEquivFrobeniusFixedPointsRefl
    (X := WeilComplex.overSpec (k₀ := k₀) X) n).symm
  have heqv : ∀ x, ι (weilStalkTraceAlternatingSum l (n + 1) x.1 x.2.2 K') =
      K.traceFunction (n + 1) (eqv x) := by
    intro x
    obtain ⟨y, rfl⟩ := (fieldPointsEquivFrobeniusFixedPointsRefl n).surjective x
    exact (hloc n y).trans (congrArg (K.traceFunction (n + 1))
      ((fieldPointsEquivFrobeniusFixedPointsRefl n).symm_apply_apply y).symm)
  rw [← hglob n, weilTraceFormula l (Iso.refl (WeilComplex.overSpec (k₀ := k₀) X))
    ⟨1, Nat.one_pos, Iso.pow_refl 1⟩ K' (n + 1), map_sum, ← finsum_eq_sum_of_fintype]
  exact (finsum_congr heqv).trans (finsum_comp_equiv eqv)

/-- Blueprint `theorem-grothendieck-lefschetz-trace-formula--8`: the Grothendieck–Lefschetz formula
over `ℚ̄_ℓ`. For a separated `k₀`-scheme `X₀` of finite type, a Weil complex `K` on `X₀` and
`m ≥ 1`,

`∑ᵢ (-1)ⁱ Tr(Fᵐ | H_cⁱ(X, K)) = ∑_{y ∈ X₀(𝔽_{qᵐ})} t_K(y)`,

`F` being the geometric Frobenius on compactly supported cohomology
(`AlgebraicGeometry.WeilComplex.compactlySupportedCohomology`) and `t_K` the trace function
(`AlgebraicGeometry.WeilComplex.traceFunction`). Only finitely many terms are nonzero on
either side. It is
`AlgebraicGeometry.WeilComplex.finsum_trace_compactlySupportedCohomology_eq_of_comparison`. -/
theorem WeilComplex.sum_trace_compactlySupportedCohomology_eq_sum_traceFunction
    (K : WeilComplex k₀ l X) {m : ℕ} (hm : m ≠ 0) :
    ∑ᶠ i : ℤ, (i.negOnePow : ℤ) • LinearMap.trace (PadicAlgCl l) _
        ((K.compactlySupportedCohomology i).frobenius.toLinearMap ^ m) =
      ∑ᶠ y : (X ↘ Spec (CommRingCat.of k₀)).fieldPoints (FiniteField.galoisExtension k₀ m),
        K.traceFunction m y :=
  K.finsum_trace_compactlySupportedCohomology_eq_of_comparison (Nat.one_le_iff_ne_zero.2 hm)

end AlgebraicGeometry
