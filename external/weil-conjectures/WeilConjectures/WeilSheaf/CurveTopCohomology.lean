/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.CohomologyZero
public import WeilConjectures.WeilSheaf.Dual
public import WeilConjectures.WeilSheaf.GeometricCoinvariants
public import WeilConjectures.WeilSheaf.LissePoincarePairing

/-!
# Top compactly supported cohomology of a lisse Weil sheaf on an affine curve

On a smooth geometrically connected affine curve `U₀` over a finite field `k₀ = 𝔽_q`, the top
compactly supported cohomology `H_c²(U, F)` of a lisse Weil sheaf `F` is the geometric
coinvariants `V_{π₁(U)}` of its generic fibre `V`, Tate-twisted by `(-1)`: by global Verdier
duality on the smooth curve `U`, `H_c²(U, F)` is dual to `H⁰(U, F^∨(1))`, and the global sections
of the lisse sheaf `F^∨` are the invariants of `π₁(U)` on `V^∨`.

The geometric coinvariants are `AlgebraicGeometry.WeilSheaf.geometricCoinvariants`, the dual
`Γ(U, F^∨)^∨` of the global sections of the dual sheaf.

## Main statements

- `AlgebraicGeometry.WeilSheaf.nonempty_equiv_compactlySupportedCohomology_two`
  (`lemma-degree-zero-top-cohomology--2`), from the lisse Poincaré pairing
  `AlgebraicGeometry.WeilSheaf.exists_isPerfPair_compactlySupportedCohomology_dual_mul` (from the
  lisse case of `corollary-degreewise-duality-over-fields--1`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {U : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]

/-- Blueprint `lemma-degree-zero-top-cohomology--2`: Description of `H_c²` on an affine curve.

Let `U₀` be a smooth geometrically connected affine curve over `k₀ = 𝔽_q` and `F` a lisse Weil
sheaf on `U₀`, with local generic fibre `V`. There is a Frobenius-equivariant isomorphism
`H_c²(U, F) ≃ V_{π₁(U)}(-1)`, where the geometric coinvariants `V_{π₁(U)} = Γ(U, F^∨)^∨` carry the
Frobenius induced by the Weil structure and the Tate twist `(-1)` multiplies it by `q`. -/
theorem nonempty_equiv_compactlySupportedCohomology_two [IsAffine U]
    [SmoothOfRelativeDimension 1 (U ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (U ↘ Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l U)
    (hF : F.IsLisse) :
    Nonempty ((F.compactlySupportedCohomology 2).Equiv
      ((F.geometricCoinvariants hF).tateTwist (Nat.card k₀) (-1))) := by
  obtain ⟨P, hP, hPF⟩ :=
    exists_isPerfPair_compactlySupportedCohomology_dual_mul 1 F hF 2 0 (by norm_num)
  have hq : (Nat.card k₀ : PadicAlgCl l) ^ (-(-1 : ℤ)) ≠ 0 :=
    zpow_ne_zero _ (Nat.cast_ne_zero.2 Nat.card_pos.ne')
  exact ⟨(FrobeniusModule.Equiv.ofIsPerfPair P hq fun x y ↦ by
    rw [hPF, neg_neg, zpow_one, pow_one]).trans
      ((cohomologyZeroEquiv (F.dual hF)).dual.rescale _)⟩

/-- Blueprint `lemma-degree-zero-top-cohomology--7`: Purity of `H_c²` on an affine curve.

Let `U₀` be a smooth geometrically connected affine curve and `F` a lisse Weil sheaf on `U₀`,
punctually `ι`-pure of weight `w`. Then `H_c²(U, F)` is `ι`-pure of weight `w + 2` (possibly
zero): it is the Tate twist `(-1)` of the geometric coinvariants
(`AlgebraicGeometry.WeilSheaf.nonempty_equiv_compactlySupportedCohomology_two`), which are pure
of weight `w` (`AlgebraicGeometry.WeilSheaf.isPureOfWeightOver_geometricCoinvariants`), and the
twist `(-1)` raises weights by two. -/
theorem isPureOfWeightOver_compactlySupportedCohomology_two [IsAffine U]
    [SmoothOfRelativeDimension 1 (U ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (U ↘ Spec (CommRingCat.of k₀))] (ι : PadicAlgCl l →+* ℂ)
    (F : WeilSheaf k₀ l U) (hF : F.IsLisse) {w : ℝ} (hw : F.IsPunctuallyPureOfWeight ι w) :
    (F.compactlySupportedCohomology 2).IsPureOfWeightOver k₀ ι (w + 2) := by
  obtain ⟨e⟩ := nonempty_equiv_compactlySupportedCohomology_two F hF
  have h := (isPureOfWeightOver_geometricCoinvariants ι F hF hw).tateTwist Nat.card_pos (-1)
  have hw2 : w - 2 * ((-1 : ℤ) : ℝ) = w + 2 := by push_cast; ring
  rw [hw2] at h
  exact FrobeniusModule.IsPureOfWeight.of_equiv e h

end WeilSheaf

end AlgebraicGeometry
