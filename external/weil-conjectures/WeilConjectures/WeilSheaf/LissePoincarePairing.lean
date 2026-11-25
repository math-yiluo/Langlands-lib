/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.ConstantTwistCohomology
public import WeilConjectures.WeilSheaf.Dual
public import WeilConjectures.WeilSheaf.PoincareDualityLisse

/-!
# Poincaré duality for a lisse Weil sheaf

Let `k₀ = 𝔽_q` be a finite field, `ℓ ≠ p` a prime, `X₀` a smooth, separated `k₀`-scheme of finite
type and pure dimension `d`, and `F` a lisse Weil sheaf on `X₀` with dual `F^∨`. Poincaré
duality pairs `H_c^i(X₀ ⊗ k̄, F)` perfectly with `H^{2d-i}(X₀ ⊗ k̄, F^∨)`, with values in the line
`ℚ̄_ℓ(-d)` on which the geometric Frobenius acts by `q^d`. This is derived from
`AlgebraicGeometry.WeilSheaf.exists_isPerfPair_compactlySupportedCohomology_dual` (the twisted
form, pairing with `F^∨(d)`).

A perfect pairing `M × N ⟶ K` of Frobenius modules with `⟨F x, F y⟩ = c ⟨x, y⟩` identifies `M`
with the dual `N^∨` with Frobenius rescaled by `c`
(`FrobeniusModule.Equiv.ofIsPerfPair`); in particular, `H_c^i(F) ≅ H^{2d-i}(F^∨)^∨(-d)`.

## Main statements

- `AlgebraicGeometry.WeilSheaf.exists_isPerfPair_compactlySupportedCohomology_dual_mul`: the
  perfect pairings with `F^∨`, on which the Frobenius acts by `q^d`.
- `FrobeniusModule.Equiv.ofIsPerfPair`: a perfect pairing multiplying the Frobenius by `c`
  identifies `M` with `N^∨` rescaled by `c`.
-/

@[expose] public section

universe u v

namespace FrobeniusModule

variable {K : Type v} [Field K]

/-- A perfect pairing `P : M × N ⟶ K` of Frobenius modules with `P (F x) (F y) = c * P x y`,
`c ≠ 0`, identifies `M` with the dual `N^∨` with Frobenius rescaled by `c`: the value line is
`K` with Frobenius acting by `c`. -/
noncomputable def Equiv.ofIsPerfPair {M : FrobeniusModule.{max u v, v} K}
    {N : FrobeniusModule.{u, v} K} (P : M.carrier →ₗ[K] N.carrier →ₗ[K] K) [P.IsPerfPair]
    {c : K} (hc : c ≠ 0) (hP : ∀ x y, P (M.frobenius x) (N.frobenius y) = c * P x y) :
    M.Equiv (N.dual.rescale c) where
  toLinearEquiv := P.toPerfPair
  map_frobenius x := by
    refine (LinearMap.ext fun y ↦ ?_ : P.toPerfPair (M.frobenius x) =
      c • N.dual.frobenius (P.toPerfPair x)).trans (frobeniusEnd_rescale_apply hc _).symm
    rw [LinearMap.smul_apply, dual_frobenius_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.toPerfPair_apply, LinearMap.toPerfPair_apply, smul_eq_mul, ← hP,
      LinearEquiv.apply_symm_apply]

end FrobeniusModule

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- Degreewise Poincaré duality for a lisse Weil sheaf, untwisted form: for `X₀` smooth,
separated, of finite type and pure dimension `d` over `k₀` and `F` lisse, there are perfect
pairings `H_c^i(X₀ ⊗ k̄, F) × H^j(X₀ ⊗ k̄, F^∨) ⟶ ℚ̄_ℓ`, `i + j = 2d`, with
`⟨F x, F y⟩ = q^d ⟨x, y⟩` for the geometric Frobenius `F`: the value line is `ℚ̄_ℓ(-d)`.

This is `AlgebraicGeometry.WeilSheaf.exists_isPerfPair_compactlySupportedCohomology_dual`
(blueprint `corollary-degreewise-duality-over-fields--1`), which pairs with `F^∨(d)`, transported
along `H^j(F^∨(d)) ≅ H^j(F^∨)` with Frobenius rescaled by `χ_ℓ(σ)ᵈ = q^{-d}`
(`AlgebraicGeometry.WeilSheaf.nonempty_equiv_cohomology_constantTwist`). -/
theorem exists_isPerfPair_compactlySupportedCohomology_dual_mul (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l X)
    (hF : F.IsLisse) (i j : ℤ) (h : i + j = 2 * d) :
    ∃ P : (F.compactlySupportedCohomology i).carrier →ₗ[PadicAlgCl l]
        ((F.dual hF).cohomology j).carrier →ₗ[PadicAlgCl l] PadicAlgCl l,
      P.IsPerfPair ∧ ∀ x y, P ((F.compactlySupportedCohomology i).frobenius x)
        (((F.dual hF).cohomology j).frobenius y) = (Nat.card k₀ : PadicAlgCl l) ^ d * P x y := by
  obtain ⟨P, hP, hPF⟩ := exists_isPerfPair_compactlySupportedCohomology_dual d hF i j h
  obtain ⟨e⟩ := nonempty_equiv_cohomology_constantTwist (F.dual hF) (cyclotomicUnit k₀ l ^ d) j
  let eH : ((F.dual hF).cohomology j).carrier ≃ₗ[PadicAlgCl l]
      (((F.dual hF).constantTwist (cyclotomicUnit k₀ l ^ d)).cohomology j).carrier :=
    e.toLinearEquiv.symm
  have hb : ((cyclotomicUnit k₀ l ^ d : (PadicAlgCl l)ˣ) : PadicAlgCl l) ≠ 0 := Units.ne_zero _
  -- `eH` divides the Frobenius by `χ_ℓ(σ)ᵈ`
  have heH (y : ((F.dual hF).cohomology j).carrier) :
      eH (((F.dual hF).cohomology j).frobenius y) =
        ((cyclotomicUnit k₀ l ^ d : (PadicAlgCl l)ˣ) : PadicAlgCl l)⁻¹ •
          (((F.dual hF).constantTwist (cyclotomicUnit k₀ l ^ d)).cohomology j).frobenius
            (eH y) := by
    have h1 := e.map_frobenius (eH y)
    have h2 : e.toLinearEquiv (eH y) = y := e.toLinearEquiv.apply_symm_apply y
    rw [h2] at h1
    have h3 : (((F.dual hF).cohomology j).rescale
        ((cyclotomicUnit k₀ l ^ d : (PadicAlgCl l)ˣ) : PadicAlgCl l)).frobenius y =
        ((cyclotomicUnit k₀ l ^ d : (PadicAlgCl l)ˣ) : PadicAlgCl l) •
          ((F.dual hF).cohomology j).frobenius y := by
      simp [FrobeniusModule.rescale]
    rw [h3] at h1
    apply e.toLinearEquiv.injective
    rw [map_smul, h1, smul_smul, inv_mul_cancel₀ hb, one_smul]
    exact e.toLinearEquiv.apply_symm_apply _
  have hq : ((cyclotomicUnit k₀ l ^ d : (PadicAlgCl l)ˣ) : PadicAlgCl l)⁻¹ =
      (Nat.card k₀ : PadicAlgCl l) ^ d := by
    rw [Units.val_pow_eq_pow_val, cyclotomicUnit_eq, inv_pow, inv_inv]
  refine ⟨P.compl₁₂ (LinearEquiv.refl _ _).toLinearMap eH.toLinearMap,
    LinearMap.IsPerfPair.compl₁₂ (p := P) (LinearEquiv.refl _ _) eH, fun x y ↦ ?_⟩
  simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LinearEquiv.refl_apply]
  rw [heH, map_smul, hPF, smul_eq_mul, hq]

end AlgebraicGeometry.WeilSheaf
