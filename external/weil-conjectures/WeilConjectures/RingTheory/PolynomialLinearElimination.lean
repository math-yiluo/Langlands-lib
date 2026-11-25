/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.MvPolynomial.Eval

/-! # Eliminating linear polynomial variables

Source: Stacks Project, Tag 07CP, last line of the single-chart calculation modulo pi.
(blueprint: lem-weil-pbc-polynomial-linear-elimination).
-/

@[expose] public section

universe u v

namespace MvPolynomial

/-- A normalized system with unit leading coefficient leaves exactly the free variables.

Source: Stacks Project, Tag 07CP, last line of the single-chart calculation modulo pi.
(blueprint: lem-weil-pbc-polynomial-linear-elimination).

Proof: Map each free variable to its quotient class. In the reverse direction send
free variables to themselves and each other variable to a inverse times the sum
of its coefficients times the free variables. Normalization makes the free-variable
relations zero; substitution kills all the remaining relations. The quotient lift
therefore exists. The first composite fixes each free variable. For the other
composite the defining relation and invertibility of a show that each dependent
variable is fixed as well. Both composites fix coefficients, so polynomial and
quotient extensionality prove they are identities. This also works when E is empty,
when E contains all variables, and over the zero ring. -/
theorem linear_elimination (K : Type u) [CommRing K] (σ : Type v) [DecidableEq σ]
    (E : Finset σ) (a : Kˣ) (h : σ → σ → K)
    (hnorm : ∀ l : E, ∀ j : E, h l j = if l = j then (a : K) else 0) :
    Nonempty (MvPolynomial E K ≃ₐ[K]
      (MvPolynomial σ K ⧸ Ideal.span (Set.range (fun l : σ ↦
        C (a : K) * X l - ∑ j : E, C (h l j) * X (j : σ))))) := by
  classical
  let rel (l : σ) : MvPolynomial σ K :=
    C (a : K) * X l - ∑ j : E, C (h l j) * X (j : σ)
  let I := Ideal.span (Set.range rel)
  let q : MvPolynomial σ K →ₐ[K] MvPolynomial σ K ⧸ I := Ideal.Quotient.mkₐ K I
  let f : MvPolynomial E K →ₐ[K] MvPolynomial σ K ⧸ I :=
    aeval (fun j : E ↦ q (X (j : σ)))
  let val (l : σ) : MvPolynomial E K :=
    if hl : l ∈ E then X ⟨l, hl⟩ else
      C (↑(a⁻¹) : K) * ∑ j : E, C (h l j) * X j
  have val_free (j : E) : val (j : σ) = X j := by simp [val, j.property]
  let g₀ : MvPolynomial σ K →ₐ[K] MvPolynomial E K := aeval val
  have g₀_rel (l : σ) : g₀ (rel l) = 0 := by
    simp only [g₀, rel, map_sub, map_mul, map_sum, aeval_C, aeval_X]
    simp only [algebraMap_eq, val_free]
    by_cases hl : l ∈ E
    · have hs : (∑ j : E, C (h l j) * X j) = C (a : K) * X (⟨l, hl⟩ : E) := by
        simp_rw [hnorm ⟨l, hl⟩]
        simp only [apply_ite C, map_zero, ite_mul, zero_mul]
        exact Fintype.sum_ite_eq _ _
      rw [hs]
      simp only [val, dite_eq_left hl, sub_self]
    · simp [val, hl, ← mul_assoc, ← map_mul]
  have hI : ∀ p, p ∈ I → g₀ p = 0 := by
    have hi : I ≤ RingHom.ker g₀.toRingHom := by
      rw [Ideal.span_le]
      rintro p ⟨l, rfl⟩
      exact g₀_rel l
    exact fun p hp ↦ hi hp
  let g : (MvPolynomial σ K ⧸ I) →ₐ[K] MvPolynomial E K :=
    Ideal.Quotient.liftₐ I g₀ hI
  have gq (p : MvPolynomial σ K) : g (q p) = g₀ p := rfl
  have gf : g.comp f = AlgHom.id K _ := by
    ext j
    simp [f, gq, g₀, val_free]
  have fg : f.comp g = AlgHom.id K _ := by
    apply Ideal.Quotient.algHom_ext
    ext l
    change f (g (q (X l))) = q (X l)
    rw [gq]
    simp only [g₀, aeval_X]
    by_cases hl : l ∈ E
    · simp [val, hl, f]
    · have hr : q (rel l) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨l, rfl⟩)
      have hr' : q (C (a : K)) * q (X l) =
          ∑ j : E, q (C (h l j)) * q (X (j : σ)) := by
        simpa [rel, map_sub, map_mul, map_sum, sub_eq_zero] using hr
      simp only [val, dite_eq_right hl, map_mul, map_sum, f, aeval_C, aeval_X]
      have hc (x : K) : algebraMap K (MvPolynomial σ K ⧸ I) x = q (C x) := rfl
      simp only [hc]
      rw [← hr', ← mul_assoc, ← map_mul, ← C_mul]
      simp
  exact ⟨AlgEquiv.ofAlgHom f g fg gf⟩

end MvPolynomial
