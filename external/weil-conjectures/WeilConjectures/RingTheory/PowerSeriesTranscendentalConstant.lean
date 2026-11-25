/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Transcendental constants in power series rings

If `x ∈ K` is transcendental over a subfield `k`, then the constant power series `x ∈ K⟦t⟧` is
transcendental over `k⟦t⟧` (acting coefficientwise): comparing the coefficients of `t ^ n` in a
polynomial relation over `k⟦t⟧` gives polynomial relations over `k`.
-/

@[expose] public section

namespace PowerSeries

/-- If `x` is transcendental over `k`, the constant power series `x` is transcendental over
`k⟦t⟧`, acting on `K⟦t⟧` coefficientwise. -/
theorem transcendental_C_of_transcendental {k K : Type*} [Field k] [Field K] [Algebra k K]
    {x : K} (hx : Transcendental k x) :
    letI := (PowerSeries.map (algebraMap k K)).toAlgebra
    Transcendental (PowerSeries k) (PowerSeries.C x) := by
  let := (PowerSeries.map (algebraMap k K)).toAlgebra
  rintro ⟨p, hp, hpx⟩
  obtain ⟨i₀, hi₀⟩ : ∃ i, p.coeff i ≠ 0 := by
    by_contra! h
    exact hp (Polynomial.ext (by simpa using h))
  obtain ⟨n, hn⟩ : ∃ n, PowerSeries.coeff n (p.coeff i₀) ≠ 0 := by
    by_contra! h
    exact hi₀ (PowerSeries.ext (by simpa using h))
  let q : Polynomial k := ∑ i ∈ p.support, Polynomial.monomial i (PowerSeries.coeff n (p.coeff i))
  have hq : q ≠ 0 := by
    intro h
    apply hn
    have := congrArg (Polynomial.coeff · i₀) h
    simpa [q, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, hi₀] using this
  refine hx ⟨q, hq, ?_⟩
  have h1 := congrArg (PowerSeries.coeff n) hpx
  rw [map_sum]
  simp only [Polynomial.aeval_monomial]
  simpa [q, Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def, map_sum,
    ← map_pow, PowerSeries.coeff_mul_C, RingHom.algebraMap_toAlgebra] using h1

end PowerSeries
