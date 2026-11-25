/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Algebra.Hom.Rat
public import WeilConjectures.ZetaLinearAlgebra.WeilFactorization

/-!
# Universal purity of an integral trace datum

Let `D` be a trace datum of length `2 * d` over an algebraically closed field `K` of
characteristic zero whose counting series has integer coefficients, and assume that for *every*
field embedding `ι : K → ℂ` the complexified reciprocal characteristic polynomial `ι (D.P i)` is
pure of weight `i`. Then `ι (D.P i)` is *universally* pure of weight `i`: every complex root `z`
is algebraic over `ℚ`, and every conjugate of `z` over `ℚ` has the same absolute value.

Algebraicity comes from the integral presentation `Z = A / B` of the counting series: the
weights separate the odd and even parity products of the `D.P i`, which are therefore the images
of `A` and `B` (`Polynomial.isAlgebraic_of_mem_roots_of_prod_mul_eq`). For the conjugates, a
root `z = ι β` with `β ∈ K` algebraic over `ℚ` and a conjugate `y` of `z` give a second
embedding `ι'` of `K` with `ι' β = y`, provided every embedding of `ℚ(β)` into `ℂ` extends to
`K`; purity for `ι'` bounds `y`. For `K = ℚ̄_ℓ` the extension property is the blueprint lemma
`lemma-reciprocal-roots-zeta--6`.

## Main statements

- `TraceDatum.isUniversallyPureOfWeight_map_P`: universal purity of an integral trace datum which
  is pure for every embedding.
-/

@[expose] public section

universe u v

namespace TraceDatum

variable {K : Type u} [Field K] [CharZero K] {q d : ℕ} (D : TraceDatum.{u, v} K (2 * d))

/-- **Universal purity of an integral trace datum** (the intrinsic-weight step of the blueprint
proof of `lemma-reciprocal-roots-zeta--7`): if every embedding of a number field `ℚ(β) ⊆ K`
into `ℂ` extends to `K`, the counting series of `D` has integer coefficients, and `ι (D.P i)` is
pure of weight `i` for every embedding `ι : K → ℂ`, then `ι (D.P i)` is universally pure of
weight `i`. -/
theorem isUniversallyPureOfWeight_map_P [IsAlgClosed K] (hq : 1 < q)
    (hext : ∀ (β : K) (z : ℂ), IsIntegral ℚ β →
      Polynomial.aeval z (minpoly ℚ β) = 0 → ∃ ι : K →+* ℂ, ι β = z)
    (hpure : ∀ (ι : K →+* ℂ) (i : Fin (2 * d + 1)), ((D.P i).map ι).IsPureOfWeight q i.1)
    {Z : PowerSeries ℚ} (hZ : PowerSeries.map (algebraMap ℚ K) Z = D.zeta)
    (hint : ∃ Z' : PowerSeries ℤ, PowerSeries.map (Int.castRingHom ℚ) Z' = Z)
    (ι : K →+* ℂ) (i : Fin (2 * d + 1)) :
    ((D.P i).map ι).IsUniversallyPureOfWeight q i.1 := by
  obtain ⟨A₀, B₀, hA, hB, hAB, hfrac⟩ := D.exists_reduced_int_normalized_fraction hZ hint
  have hA' : (A₀.map (Int.castRingHom ℚ)).coeff 0 = 1 := by
    rw [Polynomial.coeff_map, hA, map_one]
  have hB' : (B₀.map (Int.castRingHom ℚ)).coeff 0 = 1 := by
    rw [Polynomial.coeff_map, hB, map_one]
  have hroots : ∀ ι' : K →+* ℂ, ((D.P i).map ι').roots = (D.P i).roots.map ι' := fun ι' ↦
    (IsAlgClosed.splits (D.P i)).roots_map ι'
  refine ⟨(hpure ι i).1, fun z hz ↦ ?_⟩
  have hzalg : IsAlgebraic ℚ z :=
    Polynomial.isAlgebraic_of_mem_roots_of_prod_mul_eq (P := fun j ↦ (D.P j).map ι) hq
      (hpure ι) hAB hA' hB' (D.prod_odd_mul_eq_prod_even_mul ι hZ hfrac) hz
  refine ⟨hzalg, fun y hy ↦ ?_⟩
  rw [hroots] at hz
  obtain ⟨β, hβ, rfl⟩ := Multiset.mem_map.1 hz
  have hβint : IsIntegral ℚ β :=
    ((isAlgebraic_algHom_iff ι.toRatAlgHom ι.injective).1 hzalg).isIntegral
  have hmin : minpoly ℚ (ι β) = minpoly ℚ β := minpoly.algHom_eq ι.toRatAlgHom ι.injective β
  rw [hmin] at hy
  obtain ⟨ι', hι'⟩ := hext β y hβint (Polynomial.mem_aroots.1 hy).2
  have hy' : y ∈ ((D.P i).map ι').roots := by
    rw [hroots, ← hι']
    exact Multiset.mem_map_of_mem ι' hβ
  exact (hpure ι' i).2 y hy'

end TraceDatum
