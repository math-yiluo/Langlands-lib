/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.RingTheory.ReesAlgebra
public import Mathlib.Algebra.MvPolynomial.Expand

/-!
# The deformation to the normal cone for squaring on the line

The deformation computation of blueprint `example-contracting-squaring`. Let `X = 𝔸^σ` (the
blueprint case is `σ` a singleton, `X = 𝔸¹ = Spec k[x]`), `Z` the origin with ideal
`I = (x_i)`. The deformation to the normal cone of `Z` is `Spec` of the extended Rees algebra
`k[x][t, I t⁻¹]`, and `Ideal.mvPolynomialExtendedReesAlgebraEquiv` identifies it with the
polynomial ring `k[t][x'_i]` in the coordinates `x'_i = x_i t⁻¹`, so that `x_i = t x'_i`: the
constant family `𝔸^σ_T`. The first leg `c₁ = id` deforms to the identity
(`Ideal.extendedReesAlgebraMap_id`). The second leg `c₂(x) = x²` (the ring map
`MvPolynomial.expand 2`) deforms to `x' ↦ x² / t = t x'²`.

## Main results

- `Ideal.map_expand_two_mvPolynomialOrigin_le`: squaring pulls the origin back into itself.
- `Ideal.squaringDeformation`: the map `k[t][x'] ⟶ k[t][x']`, `x' ↦ t x'²`.
- `Ideal.extendedReesAlgebraMap_expand_two_comp_mvPolynomialExtendedReesAlgebraEquiv`: in the
  coordinates `x'`, the deformation of squaring is `x' ↦ t x'²`.
-/

@[expose] public section

open LaurentPolynomial

namespace Ideal

variable (C : Type*) [CommRing C] (σ : Type*)

/-- Squaring the coordinates, `x_i ↦ x_i²`, maps the ideal of the origin into itself. -/
lemma map_expand_two_mvPolynomialOrigin_le :
    (mvPolynomialOrigin C σ).map (MvPolynomial.expand 2 : MvPolynomial σ C →ₐ[C] _).toRingHom ≤
      mvPolynomialOrigin C σ := by
  rw [mvPolynomialOrigin, Ideal.map_span, Ideal.span_le]
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  change MvPolynomial.expand 2 (MvPolynomial.X i) ∈ _
  rw [MvPolynomial.expand_X]
  exact Ideal.pow_mem_of_mem _ (Ideal.subset_span (Set.mem_range_self i)) 2 two_pos

/-- (blueprint `example-contracting-squaring`) The deformation of squaring in the coordinates
`x'_i = x_i t⁻¹` of the deformation to the normal cone of the origin: the `k[t]`-algebra map
`k[t][x'_i] ⟶ k[t][x'_i]`, `x'_i ↦ t x'_i²`. -/
noncomputable def squaringDeformation :
    MvPolynomial σ (Polynomial C) →ₐ[Polynomial C] MvPolynomial σ (Polynomial C) :=
  MvPolynomial.aeval fun i ↦ MvPolynomial.C Polynomial.X * MvPolynomial.X i ^ 2

@[simp]
lemma squaringDeformation_X (i : σ) :
    squaringDeformation C σ (MvPolynomial.X i) =
      MvPolynomial.C Polynomial.X * MvPolynomial.X i ^ 2 := by
  simp [squaringDeformation]

@[simp]
lemma squaringDeformation_C (p : Polynomial C) :
    squaringDeformation C σ (MvPolynomial.C p) = MvPolynomial.C p := by
  simp [squaringDeformation]

/-- (blueprint `example-contracting-squaring`) **The deformation of squaring.** Identify the
deformation to the normal cone `k[x][t, I t⁻¹]` of the origin of `𝔸^σ` with the constant family
`k[t][x'_i]`, `x_i = t x'_i` (`Ideal.mvPolynomialExtendedReesAlgebraEquiv`). Then the map induced
by squaring `x_i ↦ x_i²` on the deformation is `x'_i ↦ x_i² / t = t x'_i²`, the identity on
`k[t]`. -/
theorem extendedReesAlgebraMap_expand_two_comp_mvPolynomialExtendedReesAlgebraEquiv :
    ((mvPolynomialOrigin C σ).extendedReesAlgebraMap
        (MvPolynomial.expand 2 : MvPolynomial σ C →ₐ[C] _).toRingHom (mvPolynomialOrigin C σ)
        (map_expand_two_mvPolynomialOrigin_le C σ)).comp
      (mvPolynomialExtendedReesAlgebraEquiv C σ).toRingHom =
    (mvPolynomialExtendedReesAlgebraEquiv C σ).toRingHom.comp
      (squaringDeformation C σ).toRingHom := by
  refine MvPolynomial.ringHom_ext (fun p ↦ ?_) fun i ↦ ?_
  · have h := congr($(extendedReesAlgebraMap_comp_toExtendedReesAlgebra
      (I := mvPolynomialOrigin C σ) _ _ (map_expand_two_mvPolynomialOrigin_le C σ))
        (Polynomial.mapRingHom MvPolynomial.C p))
    have hC := congr($(mvPolynomialExtendedReesAlgebraEquiv_comp_C C σ) p)
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, squaringDeformation_C] at h hC ⊢
    rw [hC, h, Polynomial.coe_mapRingHom, Polynomial.coe_mapRingHom, Polynomial.map_map]
    congr 2
    ext c : 1
    simp
  · apply Subtype.ext
    have h : (LaurentPolynomial.C (MvPolynomial.X i) * T (-1) : (MvPolynomial σ C)[T;T⁻¹]) ^ 2 *
        T 1 = LaurentPolynomial.C (MvPolynomial.X i ^ 2) * T (-1) := by
      rw [mul_pow, T_pow, mul_assoc, ← T_add, map_pow]
      norm_num
    simp [mvPolynomialToLaurent_C, mvPolynomialToLaurent_X, h]

end Ideal
