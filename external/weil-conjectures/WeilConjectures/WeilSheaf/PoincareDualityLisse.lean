/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.Dual
public import WeilConjectures.WeilSheaf.PoincareDualityLisseEquiv
public import WeilConjectures.WeilSheaf.TateTwist

/-!
# Degreewise Poincaré duality for lisse Weil sheaves

Let `X₀` be a smooth separated `k₀`-scheme of finite type and pure dimension `d` and `F` a lisse
Weil sheaf on `X₀`, with coefficient dual `F^∨` and Tate twist `F^∨(d)`, the constant twist of
`F^∨` by `χ_ℓ(σ)ᵈ = q⁻ᵈ`. Poincaré duality with coefficients `F` says that the degreewise
pairings `H_c^i(X₀ ⊗ k̄, F) × H^j(X₀ ⊗ k̄, F^∨(d)) ⟶ ℚ̄_ℓ`, `i + j = 2d`, are perfect and
invariant under the geometric Frobenius.

## Main statements

- `AlgebraicGeometry.WeilSheaf.exists_isPerfPair_compactlySupportedCohomology_dual`
  (`corollary-degreewise-duality-over-fields--1`, with the Frobenius invariance of
  `theorem-poincare-duality-frobenius--3`).

## Implementation notes

The statement is existential, as for constant coefficients
(`AlgebraicGeometry.WeilSheaf.exists_isPerfPair_compactlySupportedCohomology_adicConstant`): Weil
complexes have no derived tensor product or orientation yet, so the derived Poincaré pairing of
`theorem-poincare-duality--6` cannot be written down. The pairing is instead the evaluation
pairing of the Frobenius-equivariant isomorphism `H^j(X₀ ⊗ k̄, F^∨(d)) ≅ H_c^i(X₀ ⊗ k̄, F)^∨`
(`AlgebraicGeometry.WeilSheaf.nonempty_equiv_cohomology_dual_compactlySupportedCohomology`),
read off from the Verdier duality of Weil complexes.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- **Degreewise Poincaré duality for a lisse Weil sheaf** (blueprint
`corollary-degreewise-duality-over-fields--1` for `K = F` perfect over `ℚ̄_ℓ,X`, with the Frobenius
invariance `theorem-poincare-duality-frobenius--3`): for `X₀` smooth, separated, of finite
type and pure dimension `d` over `k₀` and `F` a lisse Weil sheaf on `X₀`, the degreewise
Poincaré pairings `H_c^i(X₀ ⊗ k̄, F) × H^j(X₀ ⊗ k̄, F^∨(d)) ⟶ ℚ̄_ℓ`, `i + j = 2d`, are perfect and
invariant under the geometric Frobenius. Here `F^∨(d)` is the constant twist of the coefficient
dual `F^∨` by `χ_ℓ(σ)ᵈ`. Properness is not needed. -/
theorem exists_isPerfPair_compactlySupportedCohomology_dual (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))] {F : WeilSheaf k₀ l X}
    (hF : F.IsLisse) (i j : ℤ) (h : i + j = 2 * d) :
    ∃ P : (F.compactlySupportedCohomology i).carrier →ₗ[PadicAlgCl l]
        (((F.dual hF).constantTwist (cyclotomicUnit k₀ l ^ d)).cohomology j).carrier
          →ₗ[PadicAlgCl l] PadicAlgCl l,
      P.IsPerfPair ∧ ∀ x y, P ((F.compactlySupportedCohomology i).frobenius x)
        ((((F.dual hF).constantTwist (cyclotomicUnit k₀ l ^ d)).cohomology j).frobenius y) =
          P x y := by
  obtain ⟨e⟩ := nonempty_equiv_cohomology_dual_compactlySupportedCohomology d hF i j h
  let e' : _ ≃ₗ[PadicAlgCl l]
      Module.Dual (PadicAlgCl l) (F.compactlySupportedCohomology i).carrier :=
    e.toLinearEquiv
  refine ⟨(e' : _ →ₗ[PadicAlgCl l] _).flip, inferInstance, fun x y ↦ ?_⟩
  have he : e' ((((F.dual hF).constantTwist (cyclotomicUnit k₀ l ^ d)).cohomology j).frobenius y) =
      e' y ∘ₗ (F.compactlySupportedCohomology i).frobenius.symm.toLinearMap :=
    e.map_frobenius y
  change e' _ _ = e' y x
  rw [he, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

end AlgebraicGeometry.WeilSheaf
