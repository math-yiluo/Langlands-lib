/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Division

/-!
# The syzygies of two polynomial variables

Source: the Weil conjectures blueprint, `theorem-riemann-roch-coherent-serre-duality`, expanded
calculation of exactness at the middle term of the Koszul resolution on `x₀, x₁`
(blueprint: lem-sc-p1-linear-syzygy).
-/

@[expose] public section

universe u

namespace MvPolynomial

/-- Every relation between the two variables of `k[x₀, x₁]` is a multiple of `(x₁, -x₀)`.
Source: the Weil conjectures blueprint, `theorem-riemann-roch-coherent-serre-duality`, Koszul middle
exactness (blueprint: lem-sc-p1-linear-syzygy).

Proof: Regard the ring as `k[x₁][x₀]` and write `b = b₀ + x₀ b₁`, with `b₀` in `k[x₁]`
and `b₁` in the whole ring `k[x₁][x₀]`.
The constant coefficient in `x₀` of the relation is `b₀ x₁ = 0`. Since `k[x₁]` is a domain
and `x₁` is nonzero, `b₀ = 0`, so `b = x₀ b₁`. Substitution gives
`x₀ (a + b₁ x₁) = 0`. The two-variable polynomial ring is also a domain and `x₀` is nonzero,
so `a = -b₁ x₁`. Both domain assertions are supplied by
`lem-weil-pbc-polynomial-ring-domain`. Set `c = -b₁` to obtain the two required equalities. -/
theorem exists_eq_mul_X_and_eq_neg_mul_X {k : Type u} [Field k]
    (a b : MvPolynomial (Fin 2) k) (h : a * X 0 + b * X 1 = 0) :
    ∃ c : MvPolynomial (Fin 2) k, a = c * X 1 ∧ b = -c * X 0 := by
  have hb : X (0 : Fin 2) ∣ b * X 1 := by
    rw [eq_neg_of_add_eq_zero_right h]
    exact dvd_neg.mpr (dvd_mul_left (X 0) a)
  have hb' : X (0 : Fin 2) ∣ b := by
    rcases X_dvd_mul_iff.mp hb with hb' | hx
    · exact hb'
    · have : (0 : Fin 2) = 1 := X_dvd_X.mp hx
      exact False.elim ((by decide : (0 : Fin 2) ≠ 1) this)
  obtain ⟨d, hd⟩ := hb'
  refine ⟨-d, ?_, ?_⟩
  · have ha : (a + d * X 1) * X 0 = 0 := by
      calc
        (a + d * X 1) * X 0 = a * X 0 + b * X 1 := by
          rw [add_mul, hd]
          ac_rfl
        _ = 0 := h
    have ha' : a + d * X 1 = 0 :=
      (mul_eq_zero.mp ha).resolve_right (X_ne_zero 0)
    simpa using eq_neg_of_add_eq_zero_left ha'
  · simpa [neg_neg, mul_comm] using hd

end MvPolynomial
